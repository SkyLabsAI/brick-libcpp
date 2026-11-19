#include <cctype>
#include <cassert>

void test_isalpha() {
    // Upper boundary cases
    assert(std::isalpha('A') != 0);  // First uppercase letter
    assert(std::isalpha('Z') != 0);  // Last uppercase letter
    assert(std::isalpha('Z' + 1) == 0);  // Just after uppercase

    // Lower boundary cases
    assert(std::isalpha('a') != 0);  // First lowercase letter
    assert(std::isalpha('z') != 0);  // Last lowercase letter
    assert(std::isalpha('a' - 1) == 0);  // Just before lowercase
    assert(std::isalpha('z' + 1) == 0);  // Just after lowercase

    // Non-alpha characters
    assert(std::isalpha('0') == 0);
    assert(std::isalpha(' ') == 0);
    assert(std::isalpha('\t') == 0);
    assert(std::isalpha('\n') == 0);
    assert(std::isalpha('.') == 0);

    // Extended ASCII and negative values
    assert(std::isalpha(128) == 0);  // Extended ASCII start
    assert(std::isalpha(-1) == 0);   // Negative value
}

void test_isdigit() {
    // Boundary cases
    assert(std::isdigit('0') != 0);  // First digit
    assert(std::isdigit('9') != 0);  // Last digit
    assert(std::isdigit('0' - 1) == 0);  // Just before first digit
    assert(std::isdigit('9' + 1) == 0);  // Just after last digit

    // Non-digit characters
    assert(std::isdigit('a') == 0);
    assert(std::isdigit('A') == 0);
    assert(std::isdigit(' ') == 0);
    assert(std::isdigit('-') == 0);  // Not a digit, just a minus sign

    // Extended ASCII and negative values
    assert(std::isdigit(128) == 0);
    assert(std::isdigit(-1) == 0);
}

void test_isalnum() {
    // Digit boundary cases
    assert(std::isalnum('0') != 0);
    assert(std::isalnum('9') != 0);
    assert(std::isalnum('0' - 1) == 0);
    assert(std::isalnum('9' + 1) == 0);

    // Letter boundary cases
    assert(std::isalnum('A') != 0);
    assert(std::isalnum('Z') != 0);
    assert(std::isalnum('a') != 0);
    assert(std::isalnum('z') != 0);
    assert(std::isalnum('Z' + 1) == 0);
    assert(std::isalnum('a' - 1) == 0);

    // Non-alphanumeric characters
    assert(std::isalnum(' ') == 0);
    assert(std::isalnum('.') == 0);
    assert(std::isalnum('\n') == 0);

    // Extended ASCII and negative values
    assert(std::isalnum(128) == 0);
    assert(std::isalnum(-1) == 0);
}

void test_isspace() {
    // All whitespace characters
    assert(std::isspace(' ') != 0);    // Space
    assert(std::isspace('\t') != 0);   // Horizontal tab
    assert(std::isspace('\n') != 0);   // Line feed
    assert(std::isspace('\v') != 0);   // Vertical tab
    assert(std::isspace('\f') != 0);   // Form feed
    assert(std::isspace('\r') != 0);   // Carriage return

    // Boundary cases
    assert(std::isspace('\t' - 1) == 0);  // Before tab
    assert(std::isspace('\r' + 1) == 0);  // After CR

    // Non-space characters
    assert(std::isspace('a') == 0);
    assert(std::isspace('0') == 0);
    assert(std::isspace('.') == 0);

    // Extended ASCII and negative values
    assert(std::isspace(128) == 0);
    assert(std::isspace(-1) == 0);
}

void test_islower() {
    // Boundary cases
    assert(std::islower('a') != 0);  // First lowercase letter
    assert(std::islower('z') != 0);  // Last lowercase letter
    assert(std::islower('a' - 1) == 0);  // Just before lowercase
    assert(std::islower('z' + 1) == 0);  // Just after lowercase

    // Non-lowercase characters
    assert(std::islower('A') == 0);
    assert(std::islower('0') == 0);
    assert(std::islower(' ') == 0);

    // Extended ASCII and negative values
    assert(std::islower(128) == 0);
    assert(std::islower(-1) == 0);
}

void test_isupper() {
    // Boundary cases
    assert(std::isupper('A') != 0);  // First uppercase letter
    assert(std::isupper('Z') != 0);  // Last uppercase letter
    assert(std::isupper('A' - 1) == 0);  // Just before uppercase
    assert(std::isupper('Z' + 1) == 0);  // Just after uppercase

    // Non-uppercase characters
    assert(std::isupper('a') == 0);
    assert(std::isupper('0') == 0);
    assert(std::isupper(' ') == 0);

    // Extended ASCII and negative values
    assert(std::isupper(128) == 0);
    assert(std::isupper(-1) == 0);
}

void test_isprint() {
    // Boundary cases
    assert(std::isprint(' ') != 0);  // First printable (space)
    assert(std::isprint('~') != 0);  // Last printable
    assert(std::isprint(' ' - 1) == 0);  // Just before space
    assert(std::isprint('~' + 1) == 0);  // Just after last printable

    // Sample printable characters
    assert(std::isprint('A') != 0);
    assert(std::isprint('z') != 0);
    assert(std::isprint('0') != 0);
    assert(std::isprint('!') != 0);

    // Non-printable characters
    assert(std::isprint('\0') == 0);
    assert(std::isprint('\n') == 0);
    assert(std::isprint('\t') == 0);

    // Extended ASCII and negative values
    assert(std::isprint(128) == 0);
    assert(std::isprint(-1) == 0);
}

void test_ispunct() {
    // Sample punctuation marks
    assert(std::ispunct('.') != 0);
    assert(std::ispunct(',') != 0);
    assert(std::ispunct('!') != 0);
    assert(std::ispunct(';') != 0);
    assert(std::ispunct(':') != 0);
    assert(std::ispunct('?') != 0);
    assert(std::ispunct('/') != 0);
    assert(std::ispunct('-') != 0);
    assert(std::ispunct('+') != 0);
    assert(std::ispunct('(') != 0);
    assert(std::ispunct(')') != 0);
    assert(std::ispunct('[') != 0);
    assert(std::ispunct(']') != 0);
    assert(std::ispunct('{') != 0);
    assert(std::ispunct('}') != 0);

    // Non-punctuation characters
    assert(std::ispunct('a') == 0);
    assert(std::ispunct('A') == 0);
    assert(std::ispunct('0') == 0);
    assert(std::ispunct(' ') == 0);
    assert(std::ispunct('\n') == 0);

    // Extended ASCII and negative values
    assert(std::ispunct(128) == 0);
    assert(std::ispunct(-1) == 0);
}

void test_iscntrl() {
    // Control characters (0-31 and 127)
    assert(std::iscntrl('\0') != 0);   // NUL
    assert(std::iscntrl('\a') != 0);   // BEL
    assert(std::iscntrl('\b') != 0);   // BS
    assert(std::iscntrl('\t') != 0);   // HT
    assert(std::iscntrl('\n') != 0);   // LF
    assert(std::iscntrl('\v') != 0);   // VT
    assert(std::iscntrl('\f') != 0);   // FF
    assert(std::iscntrl('\r') != 0);   // CR
    assert(std::iscntrl(31) != 0);     // Last control char before space
    assert(std::iscntrl(127) != 0);    // DEL

    // Boundary cases
    assert(std::iscntrl(32) == 0);     // Space (just after control chars)
    assert(std::iscntrl(126) == 0);    // ~ (just before DEL)
    assert(std::iscntrl(128) == 0);    // Just after DEL

    // Non-control characters
    assert(std::iscntrl('A') == 0);
    assert(std::iscntrl('0') == 0);
    assert(std::iscntrl(' ') == 0);

    // Negative values
    assert(std::iscntrl(-1) == 0);
}

void test_isgraph() {
    // Boundary cases
    assert(std::isgraph('!') != 0);    // First graphical character
    assert(std::isgraph('~') != 0);    // Last graphical character
    assert(std::isgraph(' ') == 0);    // Space is not graphical
    assert(std::isgraph('!' - 1) == 0); // Just before first graphical
    assert(std::isgraph('~' + 1) == 0); // Just after last graphical

    // Sample graphical characters
    assert(std::isgraph('A') != 0);
    assert(std::isgraph('z') != 0);
    assert(std::isgraph('0') != 0);
    assert(std::isgraph('#') != 0);

    // Non-graphical characters
    assert(std::isgraph('\0') == 0);
    assert(std::isgraph('\n') == 0);
    assert(std::isgraph('\t') == 0);

    // Extended ASCII and negative values
    assert(std::isgraph(128) == 0);
    assert(std::isgraph(-1) == 0);
}

void test_isxdigit() {
    // Decimal digit boundary cases
    assert(std::isxdigit('0') != 0);
    assert(std::isxdigit('9') != 0);
    assert(std::isxdigit('0' - 1) == 0);
    assert(std::isxdigit('9' + 1) == 0);

    // Uppercase hex boundary cases
    assert(std::isxdigit('A') != 0);
    assert(std::isxdigit('F') != 0);
    assert(std::isxdigit('A' - 1) == 0);  // Just before 'A'
    assert(std::isxdigit('F' + 1) == 0);  // Just after 'F'

    // Lowercase hex boundary cases
    assert(std::isxdigit('a') != 0);
    assert(std::isxdigit('f') != 0);
    assert(std::isxdigit('a' - 1) == 0);  // Just before 'a'
    assert(std::isxdigit('f' + 1) == 0);  // Just after 'f'

    // Non-hex characters
    assert(std::isxdigit('g') == 0);
    assert(std::isxdigit('G') == 0);
    assert(std::isxdigit(' ') == 0);
    assert(std::isxdigit('.') == 0);

    // Extended ASCII and negative values
    assert(std::isxdigit(128) == 0);
    assert(std::isxdigit(-1) == 0);
}

void test_tolower() {
    // Uppercase to lowercase conversion
    assert(std::tolower('A') == 'a');
    assert(std::tolower('Z') == 'z');

    // Boundary cases
    assert(std::tolower('A' - 1) == 'A' - 1);  // Doesn't change non-uppercase
    assert(std::tolower('Z' + 1) == 'Z' + 1);  // Doesn't change non-uppercase

    // Already lowercase (should not change)
    assert(std::tolower('a') == 'a');
    assert(std::tolower('z') == 'z');

    // Non-alphabetic characters (should not change)
    assert(std::tolower('0') == '0');
    assert(std::tolower(' ') == ' ');
    assert(std::tolower('.') == '.');

    // Extended ASCII and negative values
    assert(std::tolower(128) == 128);
    assert(std::tolower(-1) == -1);
}

void test_toupper() {
    // Lowercase to uppercase conversion
    assert(std::toupper('a') == 'A');
    assert(std::toupper('z') == 'Z');

    // Boundary cases
    assert(std::toupper('a' - 1) == 'a' - 1);  // Doesn't change non-lowercase
    assert(std::toupper('z' + 1) == 'z' + 1);  // Doesn't change non-lowercase

    // Already uppercase (should not change)
    assert(std::toupper('A') == 'A');
    assert(std::toupper('Z') == 'Z');

    // Non-alphabetic characters (should not change)
    assert(std::toupper('0') == '0');
    assert(std::toupper(' ') == ' ');
    assert(std::toupper('.') == '.');

    // Extended ASCII and negative values
    assert(std::toupper(128) == 128);
    assert(std::toupper(-1) == -1);
}

int main() {
    test_isalpha();
    test_isdigit();
    test_isalnum();
    test_isspace();
    test_islower();
    test_isupper();
    test_isprint();
    test_ispunct();
    test_iscntrl();
    test_isgraph();
    test_isxdigit();
    test_tolower();
    test_toupper();

    return 0;
}
