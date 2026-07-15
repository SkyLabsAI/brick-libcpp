#include <cwchar>

std::size_t oracle_wcslen(const wchar_t* text) {
  return ::wcslen(text);
}

int oracle_wcscmp(const wchar_t* lhs, const wchar_t* rhs) {
  return ::wcscmp(lhs, rhs);
}

int oracle_wcsncmp(const wchar_t* lhs, const wchar_t* rhs,
                   std::size_t count) {
  return ::wcsncmp(lhs, rhs, count);
}

const wchar_t* oracle_wcschr_const(const wchar_t* text, wchar_t target) {
  return ::wcschr(text, target);
}

wchar_t* oracle_wcschr_mutable(wchar_t* text, wchar_t target) {
  return std::wcschr(text, target);
}

const wchar_t* oracle_wcsrchr_const(const wchar_t* text, wchar_t target) {
  return ::wcsrchr(text, target);
}

wchar_t* oracle_wcsrchr_mutable(wchar_t* text, wchar_t target) {
  return std::wcsrchr(text, target);
}

int oracle_wmemcmp(const wchar_t* lhs, const wchar_t* rhs,
                   std::size_t count) {
  return ::wmemcmp(lhs, rhs, count);
}

const wchar_t* oracle_wmemchr_const(const wchar_t* text, wchar_t target,
                                    std::size_t count) {
  return ::wmemchr(text, target, count);
}

wchar_t* oracle_wmemchr_mutable(wchar_t* text, wchar_t target,
                                std::size_t count) {
  return std::wmemchr(text, target, count);
}
