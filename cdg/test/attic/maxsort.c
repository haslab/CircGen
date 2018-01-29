/*
  Max Sort
*/


#include "../circgen.h"

int maxInd(int size, int v[]) {
  int i, pos=0;
  for (i=1; i<size; i++)
    if (v[i]>v[pos]) pos=i;
  return pos;
}

void swap(int *xp, int *yp) {
  int temp = *xp;
  *xp = *yp;
  *yp = temp;
}

void maxsort(int size, int v[]) {
  int i, m;
  while (size>1) {
    m = maxInd(size,v);
    size--;
    swap(v+size, v+m);
  }
}

/* Circuit inputs/outputs */
#define SIZE 10
int data[SIZE];

int main() {
  AddInput(data);
  maxsort(SIZE, data);
  AddOutput(data);
  return 0;
}
