#include <string>
#include <vector>
#include <array>
struct WithArray  { std::array<unsigned long, 1> v; };
struct Plain      { std::vector<unsigned long> v; };
struct WithString { std::string s; };
unsigned long size_plain(const Plain& p)    { return p.v.size(); }
unsigned long size_str(const WithString& w) { return w.s.size(); }
