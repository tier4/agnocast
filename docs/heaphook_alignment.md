# Memory format for lockless aligned-allocation in heaphook

This document defines a memory format for providing `aligned_alloc` functionality to user programs when using an internal allocator library (e.g., TLSF allocator) that lacks an equivalent to `aligned_alloc`.
A critical requirement is lockless operation for performance optimization.

![heaphook alignment](./heaphook_alignment.png "heaphook alignment")

When a user program calls `aligned_alloc(size, alignment)`, the internal allocator's allocation function is called with a size of `ALIGNMENT + size + alignment`.
The address returned by the internal allocator is defined as `start`.
The aligned address provided to the user program, `ret`, is calculated as `ret = start + ALIGNMENT + alignment - (start + ALIGNMENT) % alignment`.
This ensures that `ret` is aligned to `alignment` and the memory region provided to the user program fits within the initially allocated area from the internal allocator.
Additionally, the address value `start` is stored at the location indicated by `ret - sizeof(*usize)`.

When the user program calls `free()`, `ret` is passed as the argument.
At this point, the address value to be passed to the internal allocator's `free()` function can be calculated as `*(ret - sizeof(*usize))`.

When a regular `malloc` or similar function is called without specifying alignment, the same procedure can be followed by setting the `alignment` value to zero.
