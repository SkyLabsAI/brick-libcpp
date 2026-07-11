#include <cassert>
#include <memory>
#include <vector>

using IntAllocator = std::allocator<int>;
using IntVector = std::vector<int, IntAllocator>;

bool default_construction_oracle() {
  IntVector default_constructed;
  IntVector::iterator first = default_constructed.begin();
  IntVector::iterator last = default_constructed.end();

  return default_constructed.size() == 0 && first == last;
}

bool allocator_construction_oracle() {
  IntAllocator allocator;
  IntVector allocator_constructed(allocator);
  IntVector::iterator first = allocator_constructed.begin();
  IntVector::iterator last = allocator_constructed.end();

  return allocator_constructed.size() == 0 && first == last;
}

bool sized_and_fill_construction_oracle() {
  IntAllocator allocator;
  IntVector default_values(3, allocator);
  IntVector fill_values(3, 7, allocator);

  return default_values.size() == 3 && default_values[0] == 0 &&
         default_values[1] == 0 && default_values[2] == 0 &&
         fill_values.size() == 3 && fill_values[0] == 7 &&
         fill_values[1] == 7 && fill_values[2] == 7;
}

bool copy_construction_oracle() {
  IntVector source;
  const int initial_value = 4;
  source.push_back(initial_value);
  source.push_back(initial_value);
  source.push_back(initial_value);
  source[1] = 8;

  IntVector copied(source);
  source[1] = 1;

  return copied.size() == 3 && copied[0] == 4 && copied[1] == 8 &&
         copied[2] == 4 && source[1] == 1;
}

bool copy_with_allocator_oracle() {
  IntAllocator allocator;
  IntVector source;
  const int initial_value = 4;
  source.push_back(initial_value);
  source.push_back(initial_value);
  source.push_back(initial_value);
  source[1] = 8;

  IntVector copied_with_allocator(source, allocator);
  source[1] = 1;

  return copied_with_allocator.size() == 3 &&
         copied_with_allocator[0] == 4 && copied_with_allocator[1] == 8 &&
         copied_with_allocator[2] == 4 && source[1] == 1;
}

bool move_construction_oracle() {
  IntVector source;
  const int first_value = 5;
  const int second_value = 8;
  source.push_back(first_value);
  source.push_back(second_value);
  IntVector moved(static_cast<IntVector&&>(source));

  // The moved-from vector remains live but has a valid, unspecified state.
  return moved.size() == 2 && moved[0] == 5 && moved[1] == 8;
}

bool move_with_allocator_oracle() {
  IntAllocator allocator;
  IntVector allocator_source;
  const int first_value = 6;
  const int second_value = 9;
  allocator_source.push_back(first_value);
  allocator_source.push_back(second_value);
  IntVector moved_with_allocator(static_cast<IntVector&&>(allocator_source),
                                 allocator);

  // The moved-from vector remains live but has a valid, unspecified state.
  return moved_with_allocator.size() == 2 && moved_with_allocator[0] == 6 &&
         moved_with_allocator[1] == 9;
}

bool scoped_destruction_oracle() {
  int observed = 0;
  {
    IntVector owned;
    const int value = 5;
    owned.push_back(value);
    owned.push_back(value);
    observed = owned.front() + owned.back();
  }
  return observed == 10;
}

bool accessor_oracle() {
  IntVector values;
  const int initial_value = 1;
  values.push_back(initial_value);
  values.push_back(initial_value);
  values.push_back(initial_value);
  values[1] = 5;
  values.front() = 2;
  values.back() = 7;

  const IntVector& const_values = values;
  return values.size() == 3 && values[0] == 2 && values[1] == 5 &&
         values[2] == 7 && values.front() == 2 && values.back() == 7 &&
         const_values[0] == 2 && const_values[1] == 5 &&
         const_values[2] == 7 && const_values.front() == 2 &&
         const_values.back() == 7;
}

bool modifier_oracle() {
  IntVector values;
  const int copied_value = 4;
  int moved_value = 9;

  values.push_back(copied_value);
  values.push_back(static_cast<int&&>(moved_value));
  const bool after_push =
      values.size() == 2 && values.front() == 4 && values.back() == 9;

  values.pop_back();
  const bool after_pop =
      values.size() == 1 && values.front() == 4 && values.back() == 4;

  values.clear();
  IntVector::iterator first = values.begin();
  IntVector::iterator last = values.end();
  return after_push && after_pop && values.size() == 0 &&
         first == last;
}

bool resize_oracle() {
  IntVector default_values;
  const int default_seed = 3;
  default_values.push_back(default_seed);
  default_values.push_back(default_seed);
  default_values.push_back(default_seed);
  default_values.push_back(default_seed);
  default_values.resize(2);
  const bool shrunk = default_values.size() == 2 &&
                      default_values[0] == 3 && default_values[1] == 3;

  default_values.resize(4);
  const bool default_grown =
      default_values.size() == 4 && default_values[0] == 3 &&
      default_values[1] == 3 && default_values[2] == 0 &&
      default_values[3] == 0;
  default_values.resize(4);
  const bool same_size = default_values.size() == 4 &&
                         default_values[2] == 0 && default_values[3] == 0;

  IntVector fill_values;
  const int fill_seed = 1;
  fill_values.push_back(fill_seed);
  fill_values.push_back(fill_seed);
  fill_values.resize(5, 7);
  const bool fill_grown =
      fill_values.size() == 5 && fill_values[0] == 1 &&
      fill_values[1] == 1 && fill_values[2] == 7 &&
      fill_values[3] == 7 && fill_values[4] == 7;
  fill_values.resize(1, 99);
  const bool fill_shrunk = fill_values.size() == 1 && fill_values[0] == 1;

  return shrunk && default_grown && same_size && fill_grown && fill_shrunk;
}

bool iterator_oracle() {
  IntVector empty;
  IntVector::iterator empty_begin = empty.begin();
  IntVector::iterator empty_end = empty.end();
  const IntVector& const_empty = empty;
  IntVector::const_iterator const_empty_begin = const_empty.begin();
  IntVector::const_iterator const_empty_end = const_empty.end();
  const bool empty_bounds = empty_begin == empty_end &&
                            const_empty_begin == const_empty_end;

  IntVector values;
  const int first_value = 2;
  const int second_value = 3;
  const int third_value = 5;
  values.push_back(first_value);
  values.push_back(second_value);
  values.push_back(third_value);

  IntVector::iterator current = values.begin();
  IntVector::iterator finish = values.end();
  const bool mutable_first = current != finish && *current == 2;
  ++current;
  const bool mutable_second = current != finish && *current == 3;
  ++current;
  const bool mutable_third = current != finish && *current == 5;
  ++current;
  const bool mutable_done = current == finish;

  const IntVector& const_values = values;
  IntVector::const_iterator const_current = const_values.begin();
  IntVector::const_iterator const_finish = const_values.end();
  const bool const_first = const_current != const_finish && *const_current == 2;
  ++const_current;
  ++const_current;
  ++const_current;
  const bool const_done = const_current == const_finish;

  return empty_bounds && mutable_first && mutable_second && mutable_third &&
         mutable_done && const_first && const_done;
}

int main() {
  assert(default_construction_oracle());
  assert(allocator_construction_oracle());
  assert(sized_and_fill_construction_oracle());
  assert(copy_construction_oracle());
  assert(copy_with_allocator_oracle());
  assert(move_construction_oracle());
  assert(move_with_allocator_oracle());
  assert(scoped_destruction_oracle());
  assert(accessor_oracle());
  assert(modifier_oracle());
  assert(resize_oracle());
  assert(iterator_oracle());
  return 0;
}
