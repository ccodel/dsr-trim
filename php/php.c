#include <stdio.h>
#include <stdlib.h>

int main (int argc, char** argv) {
  int size = atoi (argv[1]) + 1;
  int nVar = size * (size - 1);
  int nCls = size + size * (size - 1) * (size - 1) / 2;

  printf("p cnf %i %i\n", nVar, nCls);

  // at least one pigeon per hole
  for (int i = 0; i < size; ++i) {
    for (int j = 1; j < size; ++j)
      printf("%i ", i * (size - 1) + j);
    printf("0\n"); }

  // at most one pigeon per hole
  for (int i = 1; i < size; ++i)
    for (int j = 0; j < size; ++j)
      for (int k = j + 1; k < size; ++k)
        printf("-%i -%i 0\n", j * (size-1) + i, k * (size-1) + i);
}
