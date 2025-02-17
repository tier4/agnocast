from setuptools import setup

package_name = 'ros2agnocast'

setup(
    name=package_name,
    version='0.0.0',
    packages=[package_name],
    data_files=[
        ('share/' + package_name, ['package.xml']),
        ('share/ament_index/resource_index/packages',
            ['resource/' + package_name]),
    ],
    entry_points={
        'ros2topic.verb': [
            'list_agnocast = ros2agnocast.verb.list_agnocast:ListAgnocastVerb',
        ],
    }
)
