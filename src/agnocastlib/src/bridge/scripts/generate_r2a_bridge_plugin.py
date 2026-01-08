import sys
import os
import re
import em

def camel_to_snake(name):
    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()

def main():
    if len(sys.argv) < 6:
        print("Usage: python generate_r2a_bridge_plugin.py <input_list_file> <output_directory> <output_deps_file> <output_clean_list_file> <template_file>")
        return 1

    input_file = sys.argv[1]
    output_dir = sys.argv[2]
    output_deps_file = sys.argv[3]
    output_clean_list_file = sys.argv[4]
    template_file = sys.argv[5]

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

        data = {
            'msg_type': msg_type,        # geometry_msgs/msg/Pose
            'cpp_type': cpp_type,        # geometry_msgs::msg::Pose
            'header_path': header_path,  # geometry_msgs/msg/pose.hpp
            'function_name': 'create_r2a_bridge'
        }

        with open(output_cpp_path, 'w') as f:
            with open(template_file, 'r') as temp_f:
                interpreter = em.Interpreter(output=f, globals=data)
                interpreter.file(temp_f)
                interpreter.shutdown()

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
