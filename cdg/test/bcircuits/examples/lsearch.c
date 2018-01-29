/*
  Linear Search
*/


#include "../circgen.h"

int lsearch(int size, int v[], int x) {
  while (size-- > 0)
    if (v[size]==x) return size;
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
  BeginCirc();
  i = lsearch(SIZE, data, x);
  EndCirc();
  AddOutput(i);
  return 0;
}
