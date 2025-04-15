^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Changelog for package agnocastlib
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

2.1.0 (2025-04-15)
------------------
* fix(agnocastlib): add O_EXCL for shm_open flag (`#595 <https://github.com/tier4/agnocast/issues/595>`_)
* refactor(kmod): reorder ioctl command (`#615 <https://github.com/tier4/agnocast/issues/615>`_)
* refactor(kmod): change command name to add_publisher/subscriber (`#614 <https://github.com/tier4/agnocast/issues/614>`_)
* refactor(kmod): change command name from new_shm to add_process (`#613 <https://github.com/tier4/agnocast/issues/613>`_)
* fix: do shm_unlink with daemon process for each ipc_ns (`#602 <https://github.com/tier4/agnocast/issues/602>`_)
* fix(agnocastlib): close agnocast fd when exit (`#610 <https://github.com/tier4/agnocast/issues/610>`_)
* fix(Publisher): workaround for only calling borrow_loaned_message() (`#605 <https://github.com/tier4/agnocast/issues/605>`_)
* feat(TakeSubscription): add take_data (`#598 <https://github.com/tier4/agnocast/issues/598>`_)

2.0.1 (2025-04-03)
------------------

2.0.0 (2025-04-02)
------------------
* refactor(test): not to use gmock-global (`#592 <https://github.com/tier4/agnocast/issues/592>`_)
* feat(kmod): allow local pid namespace (`#540 <https://github.com/tier4/agnocast/issues/540>`_)
* fix(agnocastlib): tidy up error messages (`#590 <https://github.com/tier4/agnocast/issues/590>`_)
* Revert "fix(agnocastlib): unify the target name with the project name… (`#587 <https://github.com/tier4/agnocast/issues/587>`_)
* fix(agnocastlib): unify the target name with the project name (`#585 <https://github.com/tier4/agnocast/issues/585>`_)
* feat: add agnocast_construct_executor tracepoints (`#586 <https://github.com/tier4/agnocast/issues/586>`_)
* fix(agnocastlib): fix validate_ld_preload (`#581 <https://github.com/tier4/agnocast/issues/581>`_)
* fix: use AGNOCAST prefix for MEMPOOL_SIZE (`#580 <https://github.com/tier4/agnocast/issues/580>`_)
* refactor(kmod): unified magic number for ioctl (`#569 <https://github.com/tier4/agnocast/issues/569>`_)
* fix(test): suppress warning for unused variable (`#571 <https://github.com/tier4/agnocast/issues/571>`_)
* feat: check version consistency (`#557 <https://github.com/tier4/agnocast/issues/557>`_)
* test: infrastructure for agnocast-heaphook tests (`#554 <https://github.com/tier4/agnocast/issues/554>`_)
* fix(agnocastlib): update the take function type to match the original (`#561 <https://github.com/tier4/agnocast/issues/561>`_)
* fix: do shm_unlink in kernel module (`#536 <https://github.com/tier4/agnocast/issues/536>`_)
* feat: handle transient local callbacks in executor (`#520 <https://github.com/tier4/agnocast/issues/520>`_)
* fix: pass string length along with its pointer (`#534 <https://github.com/tier4/agnocast/issues/534>`_)
* refactor: rename symbols related to integration tests (`#543 <https://github.com/tier4/agnocast/issues/543>`_)
* test: add callback group validation into integration test (`#542 <https://github.com/tier4/agnocast/issues/542>`_)
* fix(component container): enable parameter passing (`#538 <https://github.com/tier4/agnocast/issues/538>`_)
* test: fix error & fail workflow when git diff is failed (`#541 <https://github.com/tier4/agnocast/issues/541>`_)
* fix(agnocastlib): close mqs that are no longer needed (`#476 <https://github.com/tier4/agnocast/issues/476>`_)

1.0.2 (2025-03-14)
------------------
* improve(MultiThreadedAgnocastExecutor): remove unnecessary check (`#530 <https://github.com/tier4/agnocast/issues/530>`_)
* fix(MultiThreadedAgnocastExecutor): restore starvation tests (`#529 <https://github.com/tier4/agnocast/issues/529>`_)
* improve: remove old comment (`#527 <https://github.com/tier4/agnocast/issues/527>`_)
* feat: add validation if agnocast cb and ros2 cb belong to same MutuallyExclusive cbg in MultiThreadedAgnocastExecutor (`#515 <https://github.com/tier4/agnocast/issues/515>`_)
* fix(kmod): skip transient_local procedures on take subscriber addition (`#512 <https://github.com/tier4/agnocast/issues/512>`_)
* fix(MultiThreadedAgnocastExecutor): add ready_agnocast_executables & safey lock (`#505 <https://github.com/tier4/agnocast/issues/505>`_)

1.0.1 (2025-03-10)
------------------
* chore: comment out multi-threaded executor tests (`#472 <https://github.com/tier4/agnocast/issues/472>`_)
* test(MultiThreadedAgnocastExecutor): no starvation tests considering cbg (`#460 <https://github.com/tier4/agnocast/issues/460>`_)

1.0.0 (2024-03-03)
------------------
* First release.
