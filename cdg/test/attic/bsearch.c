/*
  Binary Search
*/

#include "../circgen.h"

int bsearch(int size, int v[], int x) {
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
#define SIZE 10
int data[SIZE];
int x;

/* Circuit outputs */
int i; 

int main() {
  AddInput(data);
  AddInput(x);
  i = bsearch(SIZE, data, x);
  AddOutput(i);
  return 0;
}
