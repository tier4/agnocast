#pragma once

#include <map>
#include <string>

namespace cie_thread_configurator
{

// Get hardware information from lscpu command
std::map<std::string, std::string> get_hardware_info();

}  // namespace cie_thread_configurator
