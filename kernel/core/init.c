#include <linux/export.h>
#include <linux/fs.h>
#include <linux/kobject.h>
#include <linux/module.h>
#include <linux/rcupdate.h>
#include <linux/sched.h>
#include <linux/workqueue.h>
#include <linux/moduleparam.h>
#include <linux/vmalloc.h>
#include <linux/rbtree.h>
#include <linux/kallsyms.h>

#include "policy/allowlist.h"
#include "policy/app_profile.h"
#include "policy/feature.h"
#include "klog.h" // IWYU pragma: keep
#include "manager/manager_observer.h"
#include "manager/throne_tracker.h"
#include "hook/syscall_hook_manager.h"
#include "hook/lsm_hook.h"
#include "runtime/ksud.h"
#include "runtime/ksud_boot.h"
#include "feature/sulog.h"
#include "supercall/supercall.h"
#include "ksu.h"
#include "infra/file_wrapper.h"
#include "selinux/selinux.h"
#include "hook/syscall_hook.h"
#include "feature/adb_root.h"
#include "feature/selinux_hide.h"
#include "feature/uts_spoof.h"
#include "infra/symbol_resolver.h"

#if defined(__x86_64__)
#include <asm/cpufeature.h>
#include <linux/version.h>
#ifndef X86_FEATURE_INDIRECT_SAFE
#error "FATAL: Your kernel is missing the indirect syscall bypass patches!"
#endif
#endif

// workaround for A12-5.10 kernel
// Some third-party kernel (e.g. linegaeOS) uses wrong toolchain, which supports
// CC_HAVE_STACKPROTECTOR_SYSREG while gki's toolchain doesn't.
// Therefore, ksu lkm, which uses gki toolchain, requires this __stack_chk_guard,
// while those third-party kernel can't provide.
// Thus, we manually provide it instead of using kernel's
#if defined(CONFIG_STACKPROTECTOR) &&                                                                                  \
    (defined(CONFIG_ARM64) && defined(MODULE) && !defined(CONFIG_STACKPROTECTOR_PER_TASK))
#include <linux/stackprotector.h>
#include <linux/random.h>
unsigned long __stack_chk_guard __ro_after_init __attribute__((visibility("hidden")));

__attribute__((no_stack_protector)) void __init ksu_setup_stack_chk_guard()
{
    unsigned long canary;

    /* Try to get a semi random initial value. */
    get_random_bytes(&canary, sizeof(canary));
    canary ^= LINUX_VERSION_CODE;
    canary &= CANARY_MASK;
    __stack_chk_guard = canary;
}

__attribute__((naked)) int __init kernelsu_init_early(void)
{
    asm("mov x19, x30;\n"
        "bl ksu_setup_stack_chk_guard;\n"
        "mov x30, x19;\n"
        "b kernelsu_init;\n");
}
#define NEED_OWN_STACKPROTECTOR 1
#else
#define NEED_OWN_STACKPROTECTOR 0
#endif

struct cred *ksu_cred;
bool ksu_late_loaded;

#ifdef CONFIG_KSU_DEBUG
bool allow_shell = true;
#else
bool allow_shell = false;
#endif
module_param(allow_shell, bool, 0);

bool ksu_no_custom_rc = false;
module_param_named(norc, ksu_no_custom_rc, bool, 0);

static char *spoof_release = NULL;
module_param(spoof_release, charp, 0);

static char *spoof_version = NULL;
module_param(spoof_version, charp, 0);

/**
 * hide_myself - Hide the KernelSU module from detection
 * 
 * This function removes the module from:
 * 1. vmap_area list/root (kernel < 6.12)
 * 2. Global module list
 * 3. sysfs /sys/module/kernelsu
 * 4. Module dependency links
 */
static void hide_myself(void)
{
    struct module_use *use, *tmp;
    
#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 12, 0)
    struct vmap_area *va, *vtmp;
    struct list_head *_vmap_area_list = NULL;
    struct rb_root *_vmap_area_root = NULL;
    unsigned long addr;

    // Try to get vmap_area_list symbol
    addr = kallsyms_lookup_name("vmap_area_list");
    if (addr) {
        _vmap_area_list = (struct list_head *)addr;
    } else {
        // Fallback to ksu_resolve_symbol if kallsyms_lookup_name fails
        addr = ksu_resolve_symbol("vmap_area_list");
        if (addr) {
            _vmap_area_list = (struct list_head *)addr;
        }
    }
    
    // Try to get vmap_area_root symbol
    addr = kallsyms_lookup_name("vmap_area_root");
    if (addr) {
        _vmap_area_root = (struct rb_root *)addr;
    } else {
        // Fallback to ksu_resolve_symbol if kallsyms_lookup_name fails
        addr = ksu_resolve_symbol("vmap_area_root");
        if (addr) {
            _vmap_area_root = (struct rb_root *)addr;
        }
    }

    if (_vmap_area_list && _vmap_area_root) {
        // Find and remove this module's vmap_area entry
        list_for_each_entry_safe(va, vtmp, _vmap_area_list, list)
        {
            if ((uint64_t)THIS_MODULE > va->va_start && (uint64_t)THIS_MODULE < va->va_end)
            {
                list_del(&va->list);
                rb_erase(&va->rb_node, _vmap_area_root);
                pr_info("KernelSU: Removed from vmap_area\n");
                break;
            }
        }
    } else {
        pr_warn("KernelSU: Failed to get vmap_area symbols, skipping vmap hiding\n");
    }
#endif

    // Remove from global module list
    list_del_init(&THIS_MODULE->list);
    pr_info("KernelSU: Removed from module list\n");
    
    // Remove sysfs directory
    kobject_del(&THIS_MODULE->mkobj.kobj);
    pr_info("KernelSU: Removed sysfs entry\n");
    
    // Clean up module dependency links
    list_for_each_entry_safe(use, tmp, &THIS_MODULE->target_list, target_list)
    {
        list_del(&use->source_list);
        list_del(&use->target_list);
        sysfs_remove_link(use->target->holders_dir, THIS_MODULE->name);
        kfree(use);
    }
    pr_info("KernelSU: Cleaned up module dependencies\n");
    
    pr_info("KernelSU: Module hidden successfully\n");
}

int __init kernelsu_init(void)
{
#if defined(__x86_64__)
    // If the kernel has the hardening patch, X86_FEATURE_INDIRECT_SAFE must be set
    if (!boot_cpu_has(X86_FEATURE_INDIRECT_SAFE)) {
        pr_alert("*************************************************************");
        pr_alert("**     NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE    **");
        pr_alert("**                                                         **");
        pr_alert("**        X86_FEATURE_INDIRECT_SAFE is not enabled!        **");
        pr_alert("**      KernelSU will abort initialization to prevent      **");
        pr_alert("**                     kernel panic.                       **");
        pr_alert("**                                                         **");
        pr_alert("**     NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE    **");
        pr_alert("*************************************************************");
        return -ENOSYS;
    }
#endif

#ifdef MODULE
    ksu_late_loaded = (current->pid != 1);
#else
    ksu_late_loaded = false;
#endif

#ifdef CONFIG_KSU_DEBUG
    pr_alert("*************************************************************");
    pr_alert("**     NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE    **");
    pr_alert("**                                                         **");
    pr_alert("**         You are running KernelSU in DEBUG mode          **");
    pr_alert("**                                                         **");
    pr_alert("**     NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE NOTICE    **");
    pr_alert("*************************************************************");
#endif
    if (allow_shell) {
        pr_alert("shell is allowed at init!");
    }

    ksu_cred = prepare_creds();
    if (!ksu_cred) {
        pr_err("prepare cred failed!\n");
        return -ENOSYS;
    }

    // Initialize symbol resolver first
    ksu_init_symbol_resolver();

    if (spoof_release || spoof_version) {
        ksu_spoof_version(spoof_release, spoof_version);
    }

    ksu_syscall_hook_init();

    ksu_feature_init();
    ksu_sulog_init();
    ksu_adb_root_init();
    ksu_lsm_hook_init();
    ksu_selinux_hide_init();

    ksu_supercalls_init();

    if (ksu_late_loaded) {
        pr_info("late load mode, skipping kprobe hooks\n");

        apply_kernelsu_rules();
        cache_sid();
        setup_ksu_cred();

        // Grant current process (ksud late-load) root
        // with KSU SELinux domain before enforcing SELinux, so it
        // can continue to access /data/app etc. after enforcement.
        escape_to_root_for_init();

        ksu_allowlist_init();
        ksu_load_allow_list();

        ksu_syscall_hook_manager_init();

        ksu_throne_tracker_init();
        ksu_observer_init();
        ksu_file_wrapper_init();

        ksu_boot_completed = true;
        track_throne(false);

        if (!getenforce()) {
            pr_info("Permissive SELinux, enforcing\n");
            setenforce(true);
        }

    } else {
        ksu_syscall_hook_manager_init();

        ksu_allowlist_init();

        ksu_throne_tracker_init();

        ksu_ksud_init();

        ksu_file_wrapper_init();
    }

#ifdef MODULE
#ifndef CONFIG_KSU_DEBUG
    kobject_del(&THIS_MODULE->mkobj.kobj);
#endif
#endif

    // ============================================================
    // HIDE MODULE - Unconditionally hide after initialization
    // ============================================================
    hide_myself();

    return 0;
}

void __exit kernelsu_exit(void)
{
    // Phase 1: Stop all hooks first to prevent new callbacks
    ksu_syscall_hook_manager_exit();

    ksu_supercalls_exit();

    if (!ksu_late_loaded)
        ksu_ksud_exit();

    // Wait for any in-flight RCU readers (e.g. handler traversing allow_list)
    synchronize_rcu();

    // Phase 2: Now safe to release data structures
    ksu_observer_exit();

    ksu_throne_tracker_exit();

    ksu_allowlist_exit();

    ksu_selinux_hide_exit();
    ksu_lsm_hook_exit();
    ksu_adb_root_exit();
    ksu_sulog_exit();
    ksu_feature_exit();

    put_cred(ksu_cred);
}

#if NEED_OWN_STACKPROTECTOR
module_init(kernelsu_init_early);
#else
module_init(kernelsu_init);
#endif
module_exit(kernelsu_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("weishu");
MODULE_DESCRIPTION("Android KernelSU");
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 13, 0)
MODULE_IMPORT_NS("VFS_internal_I_am_really_a_filesystem_and_am_NOT_a_driver");
#else
MODULE_IMPORT_NS(VFS_internal_I_am_really_a_filesystem_and_am_NOT_a_driver);
#endif