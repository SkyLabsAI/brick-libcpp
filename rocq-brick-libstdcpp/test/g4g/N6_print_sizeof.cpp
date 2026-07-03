// https://www.geeksforgeeks.org/cpp/cpp-program-to-find-the-size-of-int-float-double-and-char/
#include <iostream>
using namespace std;

int main()
{
    int integerType;
    char charType;
    float floatType;
    double doubleType;

    // Calculate and Print
    // the size of integer type
    cout << "Size of int is: " << sizeof(integerType)
         << "\n";

    // Calculate and Print
    // the size of doubleType
    cout << "Size of char is: " << sizeof(charType) << "\n";

    // Calculate and Print
    // the size of charType
    cout << "Size of float is: " << sizeof(floatType)
         << "\n";

    // Calculate and Print
    // the size of floatType
    cout << "Size of double is: " << sizeof(doubleType)
         << "\n";

    return 0;
}
