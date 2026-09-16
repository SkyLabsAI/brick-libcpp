#include <thread>

template std::thread::thread(void (*&)());
template std::thread::thread(void (&)());
