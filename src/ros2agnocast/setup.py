from setuptools import find_packages, setup

package_name = 'ros2agnocast'

setup(
    name=package_name,
    version='1.0.0',
    packages=find_packages(),
    data_files=[
        ('share/' + package_name, ['package.xml']),
        ('share/ament_index/resource_index/packages',
            ['resource/' + package_name]),
    ],
    entry_points={
        'ros2topic.verb': [
            'list_agnocast = ros2agnocast.verb.list_agnocast:ListAgnocastVerb',
        ],
        'ros2node.verb': [
            'info_agnocast = ros2agnocast.verb.node_info_agnocast:NodeInfoAgnocastVerb',
        ]
    }
)
