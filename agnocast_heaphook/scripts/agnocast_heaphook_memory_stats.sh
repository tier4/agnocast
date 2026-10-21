#!/bin/sh
# Periodically prints the shared heap usage of every process started with
# AGNOCAST_HEAPHOOK_MEMORY_STATS set.
#
# Usage: agnocast_heaphook_memory_stats.sh [interval_seconds]   (default: 1)

interval=${1:-1}

while true; do
  now=$(date +%T)
  for f in /dev/shm/agnocast_heaphook_*; do
    [ -e "$f" ] || continue
    pid=${f##*_}
    # Skip files left behind by processes that did not exit cleanly.
    kill -0 "$pid" 2>/dev/null || continue
    set -- $(od -An -t u8 -N16 "$f")
    printf '%s pid=%-8s current=%-12s max=%s\n' "$now" "$pid" "$1" "$2"
  done
  sleep "$interval"
done
