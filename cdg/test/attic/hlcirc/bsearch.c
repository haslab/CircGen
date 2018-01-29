/*
  Binary Search
*/

#ifdef __COMPCERT__

#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

#else
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
void read_INPUT(char *inb, long size) {
  long i;
  char cbuf[3] = {0, 0, 0};
  /* initialize memory region */
  for (i=0; i<size; i++) inb[i] = 0;
  /* read given input */
  for (i=0; i<size; i++) {
    if ((cbuf[0]=getchar()) == EOF || !isxdigit(cbuf[0])) break;
    if ((cbuf[1]=getchar()) == EOF || !isxdigit(cbuf[1])) break;
    inb[i] = strtol(cbuf, NULL, 16);
  }
}

void write_OUTPUT(char *outb, long size) {
  while (size-- > 0)
    printf("%02x",(unsigned char)*outb++);
}

#define AddInput(X) read_INPUT((char*)&X, sizeof(X));
#define AddOutput(X) write_OUTPUT((char*)&X, sizeof(X));

#endif

int binsearch(int size, int v[], int x) {
  int l=0, u=size-1, m;
  while (u>=l) {
    m = (l+u)/2;
    if (v[m]==x) return m;
    if (v[m]>x) u = m-1;
    else l=m+1;
  }
  return -1;
}


/* Circuit inputs */
#define SIZE 4
int data[SIZE];
int x;

/* Circuit outputs */
int i; 

int main() {
  AddInput(data);
  AddInput(x);
  i = binsearch(SIZE, data, x);
  AddOutput(i);
  return 0;
}
