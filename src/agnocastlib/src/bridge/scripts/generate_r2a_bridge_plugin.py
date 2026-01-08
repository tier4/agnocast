import sys
import os
import re

def camel_to_snake(name):
    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()

def main():
    if len(sys.argv) < 5:
        print("Usage: python generate_r2a_bridge_plugin.py <input_list_file> <output_directory> <output_deps_file> <output_clean_list_file>")
        return 1

    input_file = sys.argv[1]
    output_dir = sys.argv[2]
    output_deps_file = sys.argv[3]
    output_clean_list_file = sys.argv[4]

    os.makedirs(output_dir, exist_ok=True)

    try:
        with open(input_file, 'r') as f:
            message_types = [line.strip() for line in f if '/' in line.strip()]
    except FileNotFoundError:
        message_types = []

    package_names = set()

    for msg_type in message_types:
        pkg_name = msg_type.split('/')[0]
        package_names.add(pkg_name)

        flat_type = msg_type.replace('/', '_')
        safe_filename = "register_r2a_" + flat_type + ".cpp"
        output_cpp_path = os.path.join(output_dir, safe_filename)

        cpp_type = msg_type.replace('/', '::')
        parts = msg_type.split('/')
        parts[-1] = camel_to_snake(parts[-1])
        header_path = "/".join(parts) + ".hpp"

        function_name = "create_r2a_bridge"

        with open(output_cpp_path, 'w') as f:
            f.write(f"// Auto-generated for {msg_type}\n\n")
            f.write('#include "agnocast/bridge/agnocast_bridge_node.hpp"\n')
            f.write('#include "agnocast/bridge/agnocast_performance_bridge_plugin_api.hpp"\n')
            f.write('#include "agnocast/agnocast_publisher.hpp"\n')
            f.write('#include "rclcpp/rclcpp.hpp"\n')
            f.write(f'#include "{header_path}"\n\n')

            f.write(f'extern "C" rclcpp::SubscriptionBase::SharedPtr {function_name}(\n')
            f.write('  rclcpp::Node::SharedPtr node,\n')
            f.write('  const std::string & topic_name,\n')
            f.write('  const rclcpp::QoS & sub_qos)\n')
            f.write('{\n')

            f.write(f'  using AgnoPub = agnocast::BasicPublisher<{cpp_type}, agnocast::NoBridgeRequestPolicy>;\n\n')

            f.write(f'  auto agno_pub = std::make_shared<AgnoPub>(\n')
            f.write(f'    node.get(),\n')
            f.write(f'    topic_name,\n')
            f.write(f'    rclcpp::QoS(agnocast::DEFAULT_QOS_DEPTH).transient_local(),\n')
            f.write(f'    agnocast::PublisherOptions{{}});\n\n')

            f.write(f'  auto ros_cb_group = node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);\n\n')

            f.write(f'  rclcpp::SubscriptionOptions ros_opts;\n')
            f.write(f'  ros_opts.ignore_local_publications = true;\n')
            f.write(f'  ros_opts.callback_group = ros_cb_group;\n\n')

            f.write(f'  auto ros_sub = node->create_subscription<{cpp_type}>(\n')
            f.write(f'    topic_name,\n')
            f.write(f'    sub_qos,\n')
            f.write(f'    [agno_pub](const {cpp_type}::ConstSharedPtr msg) {{\n')
            f.write(f'      auto loaned_msg = agno_pub->borrow_loaned_message();\n')
            f.write(f'      *loaned_msg = *msg;\n')
            f.write(f'      agno_pub->publish(std::move(loaned_msg));\n')
            f.write(f'    }},\n')
            f.write(f'    ros_opts);\n\n')

            f.write(f'  return ros_sub;\n')
            f.write('}\n')

    with open(output_clean_list_file, 'w') as f:
        for msg_type in message_types:
            f.write(f"{msg_type}\n")

    sorted_package_names = sorted(list(package_names))
    with open(output_deps_file, 'w') as f:
        for pkg_name in sorted_package_names:
            f.write(f"{pkg_name}\n")

    return 0

if __name__ == '__main__':
    sys.exit(main())
