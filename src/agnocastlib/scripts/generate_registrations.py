import sys
import os
import re

def camel_to_snake(name):
    name = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', name).lower()

def main():
    if len(sys.argv) < 4:
        print("Usage: python generate_registrations.py <input_list_file> <output_directory> <output_deps_file>")
        return 1

    input_file = sys.argv[1]
    output_dir = sys.argv[2] 
    output_deps_file = sys.argv[3]

    os.makedirs(output_dir, exist_ok=True)

    try:
        with open(input_file, 'r') as f:
            message_types = [line.strip() for line in f if '/' in line.strip()]
    except FileNotFoundError:
        print(f"Warning: Input file {input_file} not found. Proceeding with empty message list.")
        message_types = []

    # Generate registration files for each message type.
    for msg_type in message_types:
        safe_filename = "register_" + msg_type.replace('/', '_') + ".cpp"
        output_cpp_path = os.path.join(output_dir, safe_filename)

        cpp_type = msg_type.replace('/', '::')
        parts = msg_type.split('/')
        parts[-1] = camel_to_snake(parts[-1])
        header_path = "/".join(parts) + ".hpp"

        with open(output_cpp_path, 'w') as f:
            f.write("// This file is auto-generated. Do not edit.\n")
            f.write(f"// Registers message type: {msg_type}\n\n")
            f.write('#include "agnocast/agnocast_ros2_to_agnocast_bridge_daemon.hpp"\n')
            f.write('#include <rosidl_runtime_cpp/traits.hpp>\n')
            f.write(f'#include "{header_path}"\n\n')
            f.write(f'// Static registrar for the message type\n')
            f.write(f'static agnocast::BridgeRegistrar<{cpp_type}> '
                    f'registrar(rosidl_generator_traits::name<{cpp_type}>());\n')

    # Generate the dependencies file. This file lists the package names of the message types.
    package_names = sorted(list(set([msg_type.split('/')[0] for msg_type in message_types])))
    with open(output_deps_file, 'w') as f:
        for pkg_name in package_names:
            f.write(f"{pkg_name}\n")

    print(f"Generated {len(message_types)} registration files in '{output_dir}'")
    return 0

if __name__ == '__main__':
    sys.exit(main())