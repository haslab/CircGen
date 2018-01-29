#ifdef __COMPCERT__
#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));
#else
#include <stdio.h>
#include <stdlib.h>
#define VMAX 10
void addInp(int *x, int size) {
  size /= sizeof(int);
  while (size-->0) {
    *x++ = (rand()%VMAX);
  }
}
#define AddInput(X) addInp(X, sizeof(X));

//#define DBG
void addOut(int *x, int size) {
#ifdef DBG
  size /= sizeof(int);
  printf("OUT: ");
  while (size-->0) {
    printf("%d ",*x++);
  }
  printf("\n");
#endif //DBG
}
#define AddOutput(X) addOut(X, sizeof(X));
#endif


/* Circuit inputs/outputs */
#define SIZE 2048
int data[SIZE];
int tmp[SIZE];

/*
  Merge Sort
*/

/* obs: r[] sould be disjoint with v1[] and v2[] */
void merge(int s1, int s2, int v1[], int v2[], int r[]) {
  while (s1>0 && s2>0) {
    if (*v1<*v2) {*r++ = *v1++; s1--;}
    else {*r++=*v2++; s2--;}
  }
  while (s1-->0) {
    *r++ = *v1++;
  }
  while (s2>0) {
    *r++ = *v2++; s2--;
  }
}

/* r[] and v[] are disjoint */
void copyA(int size, int v[], int r[]) {
  while (size--) *r++ = *v++;
}

void msort(int size, int v[]) {
  //int tmp[size];
  int *vt[2], flag;
  int left,rght, rend;
  int k;
  
  flag=0; vt[flag]=v; vt[1-flag]=tmp;
  for (k=1; k < size; k *= 2, flag=1-flag ) {       
    for (left=0; left+k < size; left += k*2 ) {
      rght = left + k;        
      rend = rght + k;
      if (rend > size) rend = size;
      merge(k, rend-rght, vt[flag]+left, vt[flag]+rght, vt[1-flag]+left);
      //copyA(k+rend-rght, tmp, v+left);
    }
  }
  if (flag) 
    for (k=0;k<size;k++) v[k]= tmp[k];
}

#define TIMING
#define NREP 10000
int main() {
#ifdef TIMING
  long n = NREP;
  while (n--) {
#endif //TIMING
  AddInput(data);
  msort(SIZE, data);
  AddOutput(data);
#ifdef TIMING
  }
#endif //TIMING
  return 0;
}
