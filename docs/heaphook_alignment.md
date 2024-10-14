# Memory format for lockless aligned-allocation in heaphook

This document defines a memory format for providing `aligned_alloc` functionality to user programs when using an internal allocator library (e.g., TLSF allocator) that lacks an equivalent to `aligned_alloc`.
A critical requirement is lockless operation for performance optimization.

![heaphook alignment](./heaphook_alignment.jpeg "heaphook alignment")

When a user program calls `aligned_alloc(size, alignment)`, the internal allocator's allocation function is called with a size of `sizeof(*void) + size + alignment`.
The address returned by the internal allocator is defined as `start`.
Furthermore, `start2` is defined as `start + sizeof(*void)`.
The aligned address provided to the user program, `ret`, is calculated as `ret = start2 + alignment - start2 % alignment`.
This ensures that `ret` is aligned to `alignment` and the memory region provided to the user program fits within the initially allocated area from the internal allocator.
Additionally, the address value `start` is stored at the location indicated by `ret - sizeof(*void)`.

When the user program calls `free()`, `ret` is passed as the argument.
At this point, the address value to be passed to the internal allocator's `free()` function can be calculated as `*(ret - sizeof(*void))`.