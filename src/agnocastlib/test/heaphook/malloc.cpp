#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

void reset_alloc_stats()
{
  using ResetAllocStatsType = void (*)();

  static ResetAllocStatsType real_reset_alloc_stats = nullptr;
  if (!real_reset_alloc_stats) {
    real_reset_alloc_stats = (ResetAllocStatsType)dlsym(RTLD_DEFAULT, "reset_alloc_stats");
    if (!real_reset_alloc_stats) {
      fprintf(stderr, "Error: reset_alloc_stats not found.\n");
      std::abort();
    }
  }
  real_reset_alloc_stats();
}

void get_alloc_stats(
  size_t * original_malloc, size_t * original_free, size_t * tlsf_alloc, size_t * tlsf_dealloc)
{
  using GetAllocStatsType = void (*)(size_t *, size_t *, size_t *, size_t *);

  static GetAllocStatsType real_get_alloc_stats = nullptr;
  if (!real_get_alloc_stats) {
    real_get_alloc_stats = (GetAllocStatsType)dlsym(RTLD_DEFAULT, "get_alloc_stats");
    if (!real_get_alloc_stats) {
      fprintf(stderr, "Error: get_alloc_stats not found.\n");
      std::abort();
    }
  }
  real_get_alloc_stats(original_malloc, original_free, tlsf_alloc, tlsf_dealloc);
}

bool is_address_in_shared_mapping(void * address)
{
  std::ifstream maps_file("/proc/self/maps");
  if (!maps_file.is_open()) {
    std::cerr << "Failed to open /proc/self/maps" << std::endl;
    return false;
  }

  std::string line;
  uintptr_t addr = reinterpret_cast<uintptr_t>(address);

  while (std::getline(maps_file, line)) {
    std::istringstream iss(line);
    std::string addr_range, perms, offset, dev, inode, pathname;

    if (!(iss >> addr_range >> perms >> offset >> dev >> inode)) {
      continue;  // Malformed line
    }

    std::getline(iss, pathname);  // Rest of the line is pathname (may be empty)

    // Parse address range
    size_t dash_pos = addr_range.find('-');
    if (dash_pos == std::string::npos) {
      continue;  // Malformed address range
    }

    uintptr_t start = std::stoull(addr_range.substr(0, dash_pos), nullptr, 16);
    uintptr_t end = std::stoull(addr_range.substr(dash_pos + 1), nullptr, 16);

    // Check if address is within this range
    if (addr >= start && addr < end) {
      // Check if mapping is shared ('s' in perms)
      if (perms.size() >= 4 && perms[3] == 's') {
        return true;
      } else {
        return false;
      }
    }
  }

  return false;
}

class HeaphookMallocTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    rclcpp::init(0, nullptr);
    node = std::make_shared<rclcpp::Node>("dummy");
  }

  void TearDown() override { rclcpp::shutdown(); }

  std::shared_ptr<rclcpp::Node> node;
};

TEST_F(HeaphookMallocTest, malloc_normal)
{
  size_t orig_malloc = 0, orig_free = 0;
  size_t tlsf_alloc = 0, tlsf_dealloc = 0;

  reset_alloc_stats();

  agnocast::validate_ld_preload();

  void * ptr1 = std::malloc(100);
  EXPECT_NE(ptr1, nullptr);
  EXPECT_EQ(is_address_in_shared_mapping(ptr1), false);

  agnocast::increment_borrowed_publisher_num();
  void * ptr2 = std::malloc(100);
  agnocast::decrement_borrowed_publisher_num();
  EXPECT_NE(ptr2, nullptr);
  EXPECT_EQ(is_address_in_shared_mapping(ptr2), true);

  void * ptr3 = std::malloc(100);
  EXPECT_NE(ptr3, nullptr);
  EXPECT_EQ(is_address_in_shared_mapping(ptr3), false);

  get_alloc_stats(&orig_malloc, &orig_free, &tlsf_alloc, &tlsf_dealloc);
  std::cout << "stats: " << orig_malloc << " " << orig_free << " " << tlsf_alloc << " "
            << tlsf_dealloc << std::endl;
}
