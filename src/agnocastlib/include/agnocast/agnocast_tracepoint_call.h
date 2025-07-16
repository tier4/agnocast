// Provide fake header guard for cpplint
#undef AGNOCAST__TRACEPOINT_H_
#ifndef AGNOCAST__TRACEPOINT_H_
#define AGNOCAST__TRACEPOINT_H_

#undef TRACEPOINT_PROVIDER
#define TRACEPOINT_PROVIDER agnocast

#undef TRACEPOINT_INCLUDE
#define TRACEPOINT_INCLUDE "agnocast/agnocast_tracepoint_call.h"

#if !defined(_TP_H) || defined(TRACEPOINT_HEADER_MULTI_READ)
#define _TP_H

// clang-format off

#include <lttng/tracepoint.h>

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_publisher_init,
  TP_ARGS(
    const void *, publisher_handle_arg,
    const void *, node_handle_arg,
    const char *, topic_name_arg,
    const size_t, queue_depth_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, publisher_handle, publisher_handle_arg)
    ctf_integer_hex(const void *, node_handle, node_handle_arg)
    ctf_string(topic_name, topic_name_arg)
    ctf_integer(const size_t, queue_depth, queue_depth_arg)
  )
)

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_subscription_init,
  TP_ARGS(
    const void *, subscription_handle_arg,
    const void *, node_handle_arg,
    const void *, callback_arg,
    const void *, callback_group_arg,
    const char *, symbol_arg,
    const char *, topic_name_arg,
    const size_t, queue_depth_arg,
    const uint64_t, pid_ciid_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, subscription_handle, subscription_handle_arg)
    ctf_integer_hex(const void *, node_handle, node_handle_arg)
    ctf_integer_hex(const void *, callback, callback_arg)
    ctf_integer_hex(const void *, callback_group, callback_group_arg)
    ctf_string(symbol, symbol_arg)
    ctf_string(topic_name, topic_name_arg)
    ctf_integer(const size_t, queue_depth, queue_depth_arg)
    ctf_integer(const uint64_t, pid_ciid, pid_ciid_arg)
  )
)

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_publish,
  TP_ARGS(
    const void *, publisher_handle_arg,
    const void *, message_arg,
    const int64_t, entry_id_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, publisher_handle, publisher_handle_arg)
    ctf_integer_hex(const void *, message, message_arg)
    ctf_integer(const int64_t, entry_id, entry_id_arg)
  )
)

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_create_callable,
  TP_ARGS(
    const void *, callable_arg,
    const void *, message_arg,
    const int64_t, entry_id_arg,
    const uint64_t, pid_ciid_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, callable, callable_arg)
    ctf_integer_hex(const void *, message, message_arg)
    ctf_integer(const int64_t, entry_id, entry_id_arg)
    ctf_integer(const uint64_t, pid_ciid, pid_ciid_arg)
  )
)

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_callable_start,
  TP_ARGS(
    const void *, callable_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, callable, callable_arg)
  )
)

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_callable_end,
  TP_ARGS(
    const void *, callable_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, callable, callable_arg)
  )
)

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_take,
  TP_ARGS(
    const void *, subscription_handle_arg,
    const void *, message_arg,
    const int64_t, entry_id_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, subscription_handle, subscription_handle_arg)
    ctf_integer_hex(const void *, message, message_arg)
    ctf_integer(const int64_t, entry_id, entry_id_arg)
  )
)

TRACEPOINT_EVENT(
  TRACEPOINT_PROVIDER,
  agnocast_construct_executor,
  TP_ARGS(
    const void *, executor_addr_arg,
    const char *, executor_type_name_arg
  ),
  TP_FIELDS(
    ctf_integer_hex(const void *, executor_addr, executor_addr_arg)
    ctf_string(executor_type_name, executor_type_name_arg)
  )
)

// clang-format on

#endif /* _TP_H */

#include <lttng/tracepoint-event.h>

#endif  // AGNOCAST__TRACEPOINT_H_
