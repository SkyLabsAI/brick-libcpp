#include <cwchar>

wchar_t* oracle_wcscpy(wchar_t* dest, const wchar_t* src) {
  return ::wcscpy(dest, src);
}

wchar_t* oracle_wcsncpy(wchar_t* dest, const wchar_t* src,
                         std::size_t count) {
  return ::wcsncpy(dest, src, count);
}

wchar_t* oracle_wcscat(wchar_t* dest, const wchar_t* src) {
  return ::wcscat(dest, src);
}

wchar_t* oracle_wcsncat(wchar_t* dest, const wchar_t* src,
                         std::size_t count) {
  return ::wcsncat(dest, src, count);
}

wchar_t* oracle_wmemcpy(wchar_t* dest, const wchar_t* src,
                         std::size_t count) {
  return ::wmemcpy(dest, src, count);
}

wchar_t* oracle_wmemmove(wchar_t* dest, const wchar_t* src,
                          std::size_t count) {
  return ::wmemmove(dest, src, count);
}

wchar_t* oracle_wmemset(wchar_t* dest, wchar_t value,
                         std::size_t count) {
  return ::wmemset(dest, value, count);
}

int oracle_wcscoll(const wchar_t* lhs, const wchar_t* rhs) {
  return ::wcscoll(lhs, rhs);
}

std::size_t oracle_wcsxfrm(wchar_t* dest, const wchar_t* src,
                            std::size_t count) {
  return ::wcsxfrm(dest, src, count);
}
