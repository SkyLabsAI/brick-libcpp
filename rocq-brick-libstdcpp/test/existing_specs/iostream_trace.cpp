#include <iostream>

using ostream_manipulator = std::ostream& (*)(std::ostream&);

bool trace_insert_c_string(std::ostream& out) {
  std::ostream& result = out << "trace";
  return &result == &out;
}

bool trace_insert_int(std::ostream& out) {
  std::ostream& result = out << -17;
  return &result == &out;
}

bool trace_insert_unsigned_long(std::ostream& out) {
  std::ostream& result = out << 42UL;
  return &result == &out;
}

bool trace_apply_endl(std::ostream& out) {
  std::ostream& result =
      std::endl<char, std::char_traits<char>>(out);
  return &result == &out;
}

bool trace_insert_endl_manipulator(std::ostream& out) {
  ostream_manipulator manipulator =
      std::endl<char, std::char_traits<char>>;
  std::ostream& result = out << manipulator;
  return &result == &out;
}

bool trace_take_int(std::istream& in, int& value) {
  std::istream& result = in >> value;
  // The inventoried trace contract deliberately does not determine value.
  return &result == &in;
}

bool trace_output_composition(std::ostream& out) {
  std::ostream& string_result = out << "trace=";
  std::ostream& int_result = out << -17;
  std::ostream& ulong_result = out << 42UL;

  ostream_manipulator manipulator =
      std::endl<char, std::char_traits<char>>;
  std::ostream& manipulator_result = out << manipulator;

  return &string_result == &out && &int_result == &out &&
         &ulong_result == &out && &manipulator_result == &out;
}

#ifdef IOSTREAM_TRACE_PHASE_A_NATIVE_ORACLE
#include <cassert>
#include <locale>
#include <sstream>
#include <string>

int main() {
  std::ostringstream composed;
  composed.imbue(std::locale::classic());
  assert(trace_output_composition(composed));
  assert(composed.str() == "trace=-1742\n");

  std::ostringstream direct_endl;
  direct_endl.imbue(std::locale::classic());
  assert(trace_apply_endl(direct_endl));
  assert(direct_endl.str() == "\n");

  std::ostringstream c_string;
  c_string.imbue(std::locale::classic());
  assert(trace_insert_c_string(c_string));
  assert(c_string.str() == "trace");

  std::ostringstream integer;
  integer.imbue(std::locale::classic());
  assert(trace_insert_int(integer));
  assert(integer.str() == "-17");

  std::ostringstream unsigned_long;
  unsigned_long.imbue(std::locale::classic());
  assert(trace_insert_unsigned_long(unsigned_long));
  assert(unsigned_long.str() == "42");

  std::ostringstream manipulator;
  manipulator.imbue(std::locale::classic());
  assert(trace_insert_endl_manipulator(manipulator));
  assert(manipulator.str() == "\n");

  std::istringstream input("37");
  input.imbue(std::locale::classic());
  int value = 0;
  assert(trace_take_int(input, value));
  return 0;
}
#endif
