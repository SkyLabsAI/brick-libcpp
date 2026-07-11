#include <cassert>
#include <cctype>
#include <cstdio>

void test_alphanumeric_classes() {
    int alpha_letter = std::isalpha('A');
    int alpha_digit = std::isalpha('7');
    assert(alpha_letter != 0);
    assert(alpha_digit == 0);

    int digit_digit = std::isdigit('7');
    int digit_letter = std::isdigit('A');
    assert(digit_digit != 0);
    assert(digit_letter == 0);

    int alnum_letter = std::isalnum('q');
    int alnum_digit = std::isalnum('4');
    int alnum_punctuation = std::isalnum('!');
    assert(alnum_letter != 0);
    assert(alnum_digit != 0);
    assert(alnum_punctuation == 0);
}

void test_space_and_case_classes() {
    int space_newline = std::isspace('\n');
    int space_space = std::isspace(' ');
    int space_letter = std::isspace('A');
    assert(space_newline != 0);
    assert(space_space != 0);
    assert(space_letter == 0);

    int lower_lower = std::islower('a');
    int lower_upper = std::islower('A');
    assert(lower_lower != 0);
    assert(lower_upper == 0);

    int upper_upper = std::isupper('A');
    int upper_lower = std::isupper('a');
    assert(upper_upper != 0);
    assert(upper_lower == 0);
}

void test_printing_classes() {
    int print_space = std::isprint(' ');
    int print_newline = std::isprint('\n');
    assert(print_space != 0);
    assert(print_newline == 0);

    int punct_bang = std::ispunct('!');
    int punct_letter = std::ispunct('A');
    assert(punct_bang != 0);
    assert(punct_letter == 0);

    int control_newline = std::iscntrl('\n');
    int control_letter = std::iscntrl('A');
    assert(control_newline != 0);
    assert(control_letter == 0);

    int graph_bang = std::isgraph('!');
    int graph_space = std::isgraph(' ');
    assert(graph_bang != 0);
    assert(graph_space == 0);

    int hex_upper = std::isxdigit('F');
    int hex_lower = std::isxdigit('f');
    int hex_outside = std::isxdigit('G');
    assert(hex_upper != 0);
    assert(hex_lower != 0);
    assert(hex_outside == 0);
}

void test_case_conversion() {
    int lower_converted = std::tolower('A');
    int lower_identity = std::tolower('a');
    int lower_digit = std::tolower('7');
    assert(lower_converted == 'a');
    assert(lower_identity == 'a');
    assert(lower_digit == '7');

    int upper_converted = std::toupper('a');
    int upper_identity = std::toupper('A');
    int upper_digit = std::toupper('7');
    assert(upper_converted == 'A');
    assert(upper_identity == 'A');
    assert(upper_digit == '7');
}

void test_eof_cases() {
    int alpha_eof = std::isalpha(EOF);
    int digit_eof = std::isdigit(EOF);
    int alnum_eof = std::isalnum(EOF);
    int space_eof = std::isspace(EOF);
    int lower_eof = std::islower(EOF);
    int upper_eof = std::isupper(EOF);
    int print_eof = std::isprint(EOF);
    int punct_eof = std::ispunct(EOF);
    int control_eof = std::iscntrl(EOF);
    int graph_eof = std::isgraph(EOF);
    int hex_eof = std::isxdigit(EOF);
    int tolower_eof = std::tolower(EOF);
    int toupper_eof = std::toupper(EOF);

    assert(alpha_eof == 0);
    assert(digit_eof == 0);
    assert(alnum_eof == 0);
    assert(space_eof == 0);
    assert(lower_eof == 0);
    assert(upper_eof == 0);
    assert(print_eof == 0);
    assert(punct_eof == 0);
    assert(control_eof == 0);
    assert(graph_eof == 0);
    assert(hex_eof == 0);
    assert(tolower_eof == EOF);
    assert(toupper_eof == EOF);
}

bool safe_isalpha(char ch) {
    unsigned char safe = static_cast<unsigned char>(ch);
    return std::isalpha(safe) != 0;
}

int canonical_hex(char ch) {
    unsigned char safe = static_cast<unsigned char>(ch);
    int is_hex = std::isxdigit(safe);
    if (is_hex == 0) {
        return -1;
    }
    return std::toupper(safe);
}

void test_realistic_composition() {
    bool alpha = safe_isalpha('q');
    int lower_hex = canonical_hex('a');
    int digit_hex = canonical_hex('9');
    int invalid_hex = canonical_hex('g');

    assert(alpha);
    assert(lower_hex == 'A');
    assert(digit_hex == '9');
    assert(invalid_hex == -1);
}

int main() {
    test_alphanumeric_classes();
    test_space_and_case_classes();
    test_printing_classes();
    test_case_conversion();
    test_eof_cases();
    test_realistic_composition();
    return 0;
}
