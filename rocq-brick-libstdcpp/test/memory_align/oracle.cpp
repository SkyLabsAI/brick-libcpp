#include <cstddef>
#include <memory>

void* oracle_align(std::size_t alignment, std::size_t size,
                   void*& ptr, std::size_t& space) {
  return std::align(alignment, size, ptr, space);
}
