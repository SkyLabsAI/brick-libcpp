#include <cassert>
#include <iostream>

#ifdef IOSTREAM_NATIVE_HARNESS
#include <locale>
#include <sstream>
#include <string>
#endif

using char_ostream = std::basic_ostream<char, std::char_traits<char>>;
using char_istream = std::basic_istream<char, std::char_traits<char>>;
using char_ostream_manipulator = char_ostream& (*)(char_ostream&);

void test_ostream_c_string(char_ostream& out, const char* text) {
  char_ostream& returned =
      std::operator<< <std::char_traits<char>>(out, text);
  assert(&returned == &out);
}

void test_ostream_int(char_ostream& out) {
  char_ostream& returned = out.operator<<(-27);
  assert(&returned == &out);
}

void test_ostream_unsigned_long(char_ostream& out) {
  char_ostream& returned = out.operator<<(42UL);
  assert(&returned == &out);
}

void test_endl_direct(char_ostream& out) {
  char_ostream& returned =
      std::endl<char, std::char_traits<char>>(out);
  assert(&returned == &out);
}

void test_endl_manipulator_overload(char_ostream& out) {
  char_ostream_manipulator newline =
      &std::endl<char, std::char_traits<char>>;
  char_ostream& returned = out.operator<<(newline);
  assert(&returned == &out);
}

void test_istream_int(char_istream& in, int& destination) {
  char_istream& returned = in.operator>>(destination);
  assert(&returned == &in);
}

void test_output_composition(char_ostream& out) {
  char_ostream& after_text =
      std::operator<< <std::char_traits<char>>(out, "value=");
  char_ostream& after_int = after_text.operator<<(-27);
  char_ostream& after_unsigned_long = after_int.operator<<(42UL);
  char_ostream_manipulator newline =
      &std::endl<char, std::char_traits<char>>;
  char_ostream& returned = after_unsigned_long.operator<<(newline);
  assert(&returned == &out);
}

void test_input_output_composition(char_istream& in, char_ostream& out) {
  int value = 0;
  char_istream& read_result = in.operator>>(value);
  assert(&read_result == &in);
  char_ostream& write_result = out.operator<<(value);
  assert(&write_result == &out);
}

#ifdef IOSTREAM_NATIVE_HARNESS
class counting_stringbuf final : public std::stringbuf {
 public:
  int sync_count() const { return sync_count_; }

 protected:
  int sync() override {
    ++sync_count_;
    return std::stringbuf::sync();
  }

 private:
  int sync_count_ = 0;
};

int main() {
  {
    std::ostringstream out;
    out.imbue(std::locale::classic());
    test_ostream_c_string(out, "brick");
    assert(out.str() == "brick");
  }

  {
    std::ostringstream out;
    out.imbue(std::locale::classic());
    test_ostream_int(out);
    assert(out.str() == "-27");
  }

  {
    std::ostringstream out;
    out.imbue(std::locale::classic());
    test_ostream_unsigned_long(out);
    assert(out.str() == "42");
  }

  {
    counting_stringbuf buffer;
    char_ostream out(&buffer);
    out.imbue(std::locale::classic());
    test_endl_direct(out);
    assert(buffer.str() == "\n");
    assert(buffer.sync_count() == 1);
  }

  {
    counting_stringbuf buffer;
    char_ostream out(&buffer);
    out.imbue(std::locale::classic());
    test_endl_manipulator_overload(out);
    assert(buffer.str() == "\n");
    assert(buffer.sync_count() == 1);
  }

  {
    std::istringstream in(" 42;");
    in.imbue(std::locale::classic());
    int destination = -1;
    test_istream_int(in, destination);
    assert(destination == 42);
    assert(in.peek() == ';');
  }

  {
    std::istringstream in("not-an-int");
    in.imbue(std::locale::classic());
    int destination = 7;
    test_istream_int(in, destination);
    assert(in.fail());
  }

  {
    std::ostringstream out;
    out.imbue(std::locale::classic());
    test_output_composition(out);
    assert(out.str() == "value=-2742\n");
  }

  {
    std::istringstream in("17;");
    std::ostringstream out;
    in.imbue(std::locale::classic());
    out.imbue(std::locale::classic());
    test_input_output_composition(in, out);
    assert(out.str() == "17");
    assert(in.peek() == ';');
  }
}
#endif
