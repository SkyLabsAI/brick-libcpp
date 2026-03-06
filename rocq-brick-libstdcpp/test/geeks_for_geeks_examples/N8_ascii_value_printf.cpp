// C program to print ASCII Value of Character using
// implicit conversion with format specifier.
#include <stdio.h>

int main() {
    char c = 'k';

    // %d displays the integer value of
    // a character
    // %c displays the actual character
    printf("The ASCII value of %c is %d", c, c);
    return 0;
}
