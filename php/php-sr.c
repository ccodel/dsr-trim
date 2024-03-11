#include <stdio.h>
#include <stdlib.h>

int main (int argc, char** argv) {
  int p = atoi (argv[1]);

  for (int k = 1; k < p; k++) {
    int i;
    for (i = p; i >= k; i--) {
      printf ("-%i -%i %i -%i ", i*p + k, i*p + k, (i-1)*p + k, i*p + k);
      for (int j = k+1; j <= p; j++)
        printf ("%i %i %i %i ", (i-1)*p + j, i*p + j, i*p + j, (i-1)*p + j);
      printf ("0\n");
    }
    printf ("%i 0\n", (i)*p + k);
    for (int j = k+1; j <= p; j++)
      printf ("-%i 0\n", i*p + j);
  }

  printf ("0\n");
}
