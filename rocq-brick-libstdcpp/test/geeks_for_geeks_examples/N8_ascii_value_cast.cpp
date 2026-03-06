// C program to print ASCII Value of Character using
// typecasting into integer
#include <stdio.h>

int main() {

    char ch = 'A';

    // Find the ASCII value of a character using typecasting
    int asciiValue = (int)ch;

    printf("ASCII value of %c is %d\n", ch, asciiValue);
    return 0;
}
