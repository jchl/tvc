#include <stdio.h>
#include <limits.h>

#define PRINT_VALUES(t, v, fs) \
  do { printf("  \"" t "\": (" fs ", " fs "),\n", v ## _MIN, v ## _MAX); } while(0)

#define PRINT_UVALUES(t, v, fs) \
  do { printf("  \"" t "\": (0, " fs "),\n", v ## _MAX); } while(0)

int main() {
  printf("int_limits = {\n");

  PRINT_VALUES("char", CHAR, "%d");
  PRINT_VALUES("signed char", SCHAR, "%d");
  PRINT_VALUES("signed short", SHRT, "%d");
  PRINT_VALUES("signed int", INT, "%d");
  PRINT_VALUES("signed long", LONG, "%ld");
  PRINT_VALUES("signed long long", LLONG, "%lld");

  PRINT_UVALUES("unsigned char", UCHAR, "%u");
  PRINT_UVALUES("unsigned short", USHRT, "%u");
  PRINT_UVALUES("unsigned int", UINT, "%u");
  PRINT_UVALUES("unsigned long", ULONG, "%lu");
  PRINT_UVALUES("unsigned long long", ULLONG, "%llu");

  printf("}\n");

  return 0;
}
