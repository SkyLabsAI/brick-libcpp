#include <ctime>

void test_time_null() {
    (void)std::time(nullptr);
}

void test_time_store() {
    std::time_t t = 0;
    (void)std::time(&t);
}

void test_timespec_get() {
    std::timespec ts{};
    (void)std::timespec_get(&ts, TIME_UTC);
}

void test_tm_dtor_bug() {
    std::tm tm;
//     ::wpOperand
// [region: "tm" @ tm_addr; return {?: "void"}]
// (Eimplicit_init "const char*")
}

void test_mktime() {
    std::tm tm{};
    tm.tm_mday = 1;
    tm.tm_mon = 0;
    tm.tm_year = 124;
    (void)std::mktime(&tm);
}

void test_gmtime_and_asctime() {
    std::time_t t = 0;
    std::tm *tm = std::gmtime(&t);
    if (tm != nullptr) {
        (void)std::asctime(tm);
    }
}

void test_localtime_and_ctime() {
    std::time_t t = 0;
    (void)std::localtime(&t);
    (void)std::ctime(&t);
}

void test_strftime() {
    std::time_t t = 0;
    std::tm *tm = std::gmtime(&t);
    char buf[32] = {};
    if (tm != nullptr) {
        (void)std::strftime(buf, sizeof(buf), "%Y", tm);
    }
}

void test_repeated_static_calls() {
    std::time_t t = 0;
    (void)std::gmtime(&t);
    (void)std::localtime(&t);
    (void)std::ctime(&t);
    (void)std::ctime(&t);
}

int main() {
    test_time_null();
    test_time_store();
    test_timespec_get();
    test_mktime();
    test_gmtime_and_asctime();
    test_localtime_and_ctime();
    test_strftime();
    test_repeated_static_calls();
    return 0;
}
