#include <ctime>

void test_clock() {
    (void)std::clock();
}

void test_time_null() {
    (void)std::time(nullptr);
}

void test_time_store() {
    std::time_t t = 0;
    (void)std::time(&t);
}

void test_timespec_get(std::timespec *ts) {
    (void)std::timespec_get(ts, TIME_UTC);
}

void test_mktime(std::tm *tm) {
    (void)std::mktime(tm);
}

void test_gmtime(std::time_t const *t) {
    (void)std::gmtime(t);
}

void test_asctime(std::tm const *tm) {
    (void)std::asctime(tm);
}

void test_localtime(std::time_t const *t) {
    (void)std::localtime(t);
}

void test_ctime(std::time_t const *t) {
    (void)std::ctime(t);
}

void test_strftime(char *buf, std::size_t maxsize, std::tm const *tm) {
    (void)std::strftime(buf, maxsize, "%Y", tm);
}

void test_repeated_static_calls(std::time_t const *t) {
    (void)std::gmtime(t);
    (void)std::localtime(t);
    (void)std::ctime(t);
    (void)std::ctime(t);
}

int main() {
    std::time_t t = 0;

    test_clock();
    test_time_null();
    test_time_store();
    test_gmtime(&t);
    test_localtime(&t);
    test_ctime(&t);
    test_repeated_static_calls(&t);
    return 0;
}
