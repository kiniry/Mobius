#include <stdio.h>

char buf[1024];

int main(int argc, char** argv) {
  FILE *fa, *fb;
  char *s;
  if (argc != 3) {
    printf("Usage: %s file1 file2\n", argv[0]);
    return 1;
  }
  fa = fopen(argv[1], "r");
  fb = fopen(argv[2], "r");
  if (!fa||!fb) {
    printf("At least one of %s and %s can't be open.\n", argv[1], argv[2]);
    return 2;
  }
  while (!feof(fa) || !feof(fb)) {
    fgets(buf, 1024, fa);
    for (s = buf; *s != '\n' && *s; s++) putchar(*s);
    putchar(' ');
    fgets(buf, 1024, fb);
    for (s = buf; *s; s++) putchar(*s);
  }
  return 0; 
}
