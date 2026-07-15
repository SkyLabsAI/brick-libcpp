#include <cassert>
#include <cwctype>

void test_letter_and_number_classes() {
    assert(std::iswalpha(64) == 0);
    assert(std::iswalpha(65) != 0);
    assert(std::iswalpha(90) != 0);
    assert(std::iswalpha(91) == 0);
    assert(std::iswlower(97) != 0);
    assert(std::iswlower(122) != 0);
    assert(std::iswupper(65) != 0);
    assert(std::iswupper(90) != 0);
    assert(std::iswdigit(48) != 0);
    assert(std::iswdigit(57) != 0);
    assert(std::iswalnum(48) != 0);
    assert(std::iswalnum(65) != 0);
    assert(std::iswxdigit(70) != 0);
    assert(std::iswxdigit(71) == 0);
}

void test_space_and_display_classes() {
    assert(std::iswblank(9) != 0);
    assert(std::iswblank(10) == 0);
    assert(std::iswblank(32) != 0);
    assert(std::iswspace(9) != 0);
    assert(std::iswspace(10) != 0);
    assert(std::iswspace(13) != 0);
    assert(std::iswspace(14) == 0);
    assert(std::iswcntrl(0) != 0);
    assert(std::iswcntrl(127) != 0);
    assert(std::iswprint(32) != 0);
    assert(std::iswprint(127) == 0);
    assert(std::iswgraph(32) == 0);
    assert(std::iswgraph(33) != 0);
    assert(std::iswpunct(33) != 0);
    assert(std::iswpunct(65) == 0);
}

void test_weof_boundary() {
    assert(std::iswalnum(WEOF) == 0);
    assert(std::iswalpha(WEOF) == 0);
    assert(std::iswblank(WEOF) == 0);
    assert(std::iswcntrl(WEOF) == 0);
    assert(std::iswdigit(WEOF) == 0);
    assert(std::iswgraph(WEOF) == 0);
    assert(std::iswlower(WEOF) == 0);
    assert(std::iswprint(WEOF) == 0);
    assert(std::iswpunct(WEOF) == 0);
    assert(std::iswspace(WEOF) == 0);
    assert(std::iswupper(WEOF) == 0);
    assert(std::iswxdigit(WEOF) == 0);
    assert(std::towlower(WEOF) == WEOF);
    assert(std::towupper(WEOF) == WEOF);
}

void test_case_conversion() {
    assert(std::towlower(64) == 64);
    assert(std::towlower(65) == 97);
    assert(std::towlower(90) == 122);
    assert(std::towlower(91) == 91);
    assert(std::towupper(96) == 96);
    assert(std::towupper(97) == 65);
    assert(std::towupper(122) == 90);
    assert(std::towupper(123) == 123);
}

void test_classification_conversion_composition() {
    assert(std::iswupper(65) != 0);
    assert(std::towlower(65) == 97);
    assert(std::iswlower(std::towlower(65)) != 0);
    assert(std::iswlower(122) != 0);
    assert(std::towupper(122) == 90);
    assert(std::iswupper(std::towupper(122)) != 0);
}

int main() {
    test_letter_and_number_classes();
    test_space_and_display_classes();
    test_weof_boundary();
    test_case_conversion();
    test_classification_conversion_composition();
    return 0;
}
