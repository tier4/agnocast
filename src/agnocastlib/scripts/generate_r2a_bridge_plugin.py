import sys
import os
import re

def camel_to_snake(name):
    name = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', name).lower()

def main():
    if len(sys.argv) < 5:
        print("Usage: python generate_plugin_registrations.py <input_list_file> <output_directory> <output_deps_file> <output_clean_list_file>")
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

    for msg_type in message_types:
        safe_filename = "register_r2a_" + msg_type.replace('/', '_') + ".cpp"
        output_cpp_path = os.path.join(output_dir, safe_filename)

        cpp_type = msg_type.replace('/', '::')
        parts = msg_type.split('/')
        parts[-1] = camel_to_snake(parts[-1])
        header_path = "/".join(parts) + ".hpp"

        with open(output_cpp_path, 'w') as f:
            f.write(f"// Auto-generated for {msg_type}\n\n")
            f.write('#include "agnocast/agnocast_bridge_plugin_api.hpp"\n')
            f.write('#include "agnocast/agnocast_publisher.hpp"\n')
            f.write(f'#include "{header_path}"\n\n')

            f.write('extern "C" rclcpp::SubscriptionBase::SharedPtr create_r2a_bridge(\n')
            f.write('  rclcpp::Node::SharedPtr node,\n')
            f.write('  const std::string & topic_name,\n')
            f.write('  const rclcpp::QoS & qos)\n')
            f.write('{\n')

            f.write(f'  agnocast::PublisherOptions pub_options;\n')
            f.write(f'  auto agno_publisher = std::make_shared<agnocast::Publisher<{cpp_type}>>(node.get(), topic_name, qos, pub_options);\n\n')

            f.write(f'  auto ros2_callback = [agno_publisher](const {cpp_type}::ConstSharedPtr msg) {{\n')
            f.write(f'    auto loaned_msg = agno_publisher->borrow_loaned_message();\n')
            f.write(f'    *loaned_msg = *msg;\n')
            f.write(f'    agno_publisher->publish(std::move(loaned_msg));\n')
            f.write(f'  }};\n\n')

            f.write(f'  rclcpp::SubscriptionOptions sub_options;\n')
            f.write(f'  sub_options.callback_group = node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);\n')
            f.write(f'  sub_options.ignore_local_publications = true;\n\n')

            f.write(f'  auto sub = node->create_subscription<{cpp_type}>(topic_name, qos, ros2_callback, sub_options);\n\n')

            f.write(f'  return sub;\n')
            f.write('}\n')

    with open(output_clean_list_file, 'w') as f:
        for msg_type in message_types:
            f.write(f"{msg_type}\n")

    package_names = sorted(list(set([msg_type.split('/')[0] for msg_type in message_types])))
    with open(output_deps_file, 'w') as f:
        for pkg_name in package_names:
            f.write(f"{pkg_name}\n")

    return 0

if __name__ == '__main__':
    sys.exit(main())
