^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Changelog for package agnocastlib
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

2.1.2 (2025-08-18)
------------------
* fix: remove unnecessary TRACETOOLS_LTTNG_ENABLED (`#678 <https://github.com/tier4/agnocast/issues/678>`_)
* test(integration): Add integration test investigate malloc region differences after fork (`#675 <https://github.com/tier4/agnocast/issues/675>`_)
* feat(agnocastlib): template the callback type for greater flexibility (`#665 <https://github.com/tier4/agnocast/issues/665>`_)
* build: set C++ standard explicitly to support Clang builds (`#677 <https://github.com/tier4/agnocast/issues/677>`_)
* test(integration): Add integration test for malloc allocator switching based on publisher_num (`#661 <https://github.com/tier4/agnocast/issues/661>`_)
* feat(agnocastlib): impl get_all_callback_groups method in cie (`#674 <https://github.com/tier4/agnocast/issues/674>`_)
* feat(agnocastlib): cie spin (`#669 <https://github.com/tier4/agnocast/issues/669>`_)
* feat(agnocastlib): add/remove node in cie (`#668 <https://github.com/tier4/agnocast/issues/668>`_)
* feat(agnocastlib): add/remove callback group in cie (`#667 <https://github.com/tier4/agnocast/issues/667>`_)
* feat(agnocastlib): add cie skelton (`#666 <https://github.com/tier4/agnocast/issues/666>`_)
* fix(agnocastlib): stop possessing shared pointer to nodes in agnocast executor (`#664 <https://github.com/tier4/agnocast/issues/664>`_)
* feat(agnocastlib) change epoll updates behavior for cie (`#663 <https://github.com/tier4/agnocast/issues/663>`_)
* feat(agnocastlib): single threaded executor for cie (`#660 <https://github.com/tier4/agnocast/issues/660>`_)
* fix(agnocastlib): use override keyword (`#662 <https://github.com/tier4/agnocast/issues/662>`_)
* feat: tracepoint definition for CARET (`#659 <https://github.com/tier4/agnocast/issues/659>`_)
* refactor(agnocastlib): lower the log level when mq_open fails (`#650 <https://github.com/tier4/agnocast/issues/650>`_)
* style: add a trailing underscore to the data member of Subscriber (`#645 <https://github.com/tier4/agnocast/issues/645>`_)

2.1.1 (2025-05-13)
------------------
* fix(agnocastlib): forbit the reader processes from resizing shmem (`#632 <https://github.com/tier4/agnocast/issues/632>`_)
* fix: add validation for add_node() (`#638 <https://github.com/tier4/agnocast/issues/638>`_)
* fix: lock for atomically obtain shmem info via ioctl and do mmap (`#639 <https://github.com/tier4/agnocast/issues/639>`_)
* Change to use topic_local_id_t as the key for opened_mqs (`#634 <https://github.com/tier4/agnocast/issues/634>`_)
* fix(agnocastlib): add error handling for map_writable_area (`#622 <https://github.com/tier4/agnocast/issues/622>`_)

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
