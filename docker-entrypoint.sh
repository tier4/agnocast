#!/bin/bash
set -e

# Source ROS 2 setup
source /opt/ros/humble/setup.bash

# Source workspace setup if it exists
if [ -f /workspace/install/setup.bash ]; then
    source /workspace/install/setup.bash
fi

# Execute the command passed to docker run
exec "$@"
