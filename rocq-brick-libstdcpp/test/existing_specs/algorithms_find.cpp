#include <algorithm>
#include <cassert>

int find_present_first_match() {
  int values[] = {4, 7, 7, 9, 11};
  int* result = std::find(values, values + 5, 7);

  assert(result == values + 1);
  assert(*result == 7);
  return *result;
}

bool find_missing_returns_end() {
  int values[] = {4, 7, 9, 11};
  int* result = std::find(values, values + 4, 6);
  bool is_end = result == values + 4;

  assert(is_end);
  return is_end;
}

int find_in_subrange() {
  int values[] = {3, 5, 3, 8, 3};
  int* result = std::find(values + 1, values + 5, 3);

  assert(result == values + 2);
  assert(*result == 3);
  return *result;
}

bool find_in_empty_range_returns_end() {
  int values[] = {1, 2, 3};
  int* first = values + 1;
  int* result = std::find(first, first, 2);
  bool unchanged = result == first;

  assert(unchanged);
  return unchanged;
}

int update_through_found_iterator() {
  int values[] = {10, 20, 30, 40};
  int* result = std::find(values, values + 4, 30);

  assert(result == values + 2);
  *result = 31;
  assert(values[2] == 31);
  return values[2];
}

int main() {
  assert(find_present_first_match() == 7);
  assert(find_missing_returns_end());
  assert(find_in_subrange() == 3);
  assert(find_in_empty_range_returns_end());
  assert(update_through_found_iterator() == 31);
  return 0;
}
