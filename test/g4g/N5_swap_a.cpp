// https://www.geeksforgeeks.org/cpp/cpp-program-to-swap-two-numbers/, 2nd version without using temporary variable
#include <iostream>
using namespace std;

int main(){
    int a = 2, b = 3;

    cout << "Before swapping a = " << a << " , b = " << b << endl;

    b = a + b;
    a = b - a;
    b = b - a;

    cout << "After swapping a = " << a << " , b = " << b << endl;
    return 0;
}
