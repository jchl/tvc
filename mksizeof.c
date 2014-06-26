#include <stdio.h>
#include <stddef.h>

#define PRINT_SIZEOF(t) \
  do { printf("  (\"" #t "\", %zd),\n", sizeof(t)); } while (0)

int main() {
  printf("sizeof = {\n");

  PRINT_SIZEOF(char);

  PRINT_SIZEOF(signed char);
  PRINT_SIZEOF(signed short);
  PRINT_SIZEOF(signed int);
  PRINT_SIZEOF(signed long);
  PRINT_SIZEOF(signed long long);

  PRINT_SIZEOF(unsigned char);
  PRINT_SIZEOF(unsigned short);
  PRINT_SIZEOF(unsigned int);
  PRINT_SIZEOF(unsigned long);
  PRINT_SIZEOF(unsigned long long);

  PRINT_SIZEOF(size_t);
  PRINT_SIZEOF(ptrdiff_t);

  printf("}\n");
}
