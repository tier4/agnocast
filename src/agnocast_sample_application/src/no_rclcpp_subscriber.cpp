#include "agnocast/agnocast.hpp"

#include <iostream>

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);

  std::string node_name = agnocast::query_node_name();
  std::cout << "Node name: " << node_name << std::endl;

  return 0;
}
