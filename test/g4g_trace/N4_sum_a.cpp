// https://www.geeksforgeeks.org/cpp/cpp-add-numbers/, 2nd version

#include <iostream>
using namespace std;

int main() {
    int a = 11, b = 9;

    // If b is positive, increment a to b times
    for (int i = 0; i < b; i++)
        a++;

    // If b is negative, decrement a to |b| times
    for (int i = 0; i > b; i--)
        a--;

    cout << a;

    return 0;
}
