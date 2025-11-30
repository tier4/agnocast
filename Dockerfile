# Base image: ROS 2 Humble on Ubuntu 22.04
FROM ros:humble-ros-base-jammy

# Avoid interactive prompts during build
ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    cmake \
    git \
    wget \
    curl \
    python3-pip \
    python3-colcon-common-extensions \
    python3-rosdep \
    liblttng-ust-dev \
    linux-headers-generic \
    kmod \
    && rm -rf /var/lib/apt/lists/*

# Install Rust for heaphook
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain 1.75.0
ENV PATH="/root/.cargo/bin:${PATH}"

# Install pre-commit for development
RUN pip3 install pre-commit

# Set working directory
WORKDIR /workspace

# Copy source code
COPY . /workspace/

# Initialize rosdep (if not already done)
RUN rosdep update || true

# Install ROS dependencies
RUN . /opt/ros/humble/setup.sh && \
    rosdep install --from-paths src --ignore-src -r -y || true

# Build heaphook
RUN cd /workspace/agnocast_heaphook && \
    rm -f Cargo.lock && \
    cargo build --release && \
    mkdir -p /usr/local/lib && \
    cp target/release/libagnocast_heaphook.so /usr/local/lib/ && \
    ldconfig

# Build the project
RUN . /opt/ros/humble/setup.sh && \
    colcon build --symlink-install --cmake-args -DCMAKE_BUILD_TYPE=Release

# Source the workspace in bashrc
RUN echo "source /opt/ros/humble/setup.bash" >> ~/.bashrc && \
    echo "source /workspace/install/setup.bash" >> ~/.bashrc

# Set entrypoint
COPY docker-entrypoint.sh /docker-entrypoint.sh
RUN chmod +x /docker-entrypoint.sh

ENTRYPOINT ["/docker-entrypoint.sh"]
CMD ["/bin/bash"]
