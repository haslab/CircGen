#ifdef __COMPCERT__
#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));
#else
#include <stdio.h>
#include <stdlib.h>
#define VMAX 100
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
#define BSIZE 8
#define ALPHA (1<<BSIZE)
#define MN (1<<(8*sizeof(int)-1))

#define SIZE 2048
int data[SIZE];
unsigned int aux[SIZE];
//unsigned int freqs[ALPHA];


void normaliza (unsigned int v[], int N) {
	int i;
	for (i=0;i<N;v[i++] += MN);
}

void countingSort (int N, unsigned int v[N], unsigned int aux[N], int mask, int r) {
  int freqs[ALPHA], i;
  int prev, tmp, ind;
  for (i=0;i<ALPHA; freqs[i++]=0);
  
  for (i=0;i<N;i++)
    freqs [(v[i]&mask)>>(r*BSIZE)]++;
  
  prev    = freqs[0];
  freqs[0] = 0;
  for (i=1;i<ALPHA;i++){
    tmp = freqs[i];
    freqs [i] = freqs[i-1] + prev;
    prev = tmp;
  }
  
  for (i=0;i<N;i++){
    ind = (v[i]&mask)>>(r*BSIZE);
    aux[freqs[ind]++]=v[i];
  }
}

void radixSortU (int N, unsigned int v[N]){
  unsigned int *vs[2];
  vs[0] =  v; vs[1] = aux;
  int i, flag, r, mask = (1<<BSIZE)-1;
  for (r=0, flag=0; mask; r++, mask=mask<<BSIZE, flag=1-flag)
    countingSort (N,vs[flag], vs[1-flag], mask, r);
  if (flag) 
    for (i=0;i<N;i++)
      v[i]= aux[i];
}

void radixSort (int N, int v[N]){	
  unsigned int *u = (unsigned int *) v;
  normaliza (u,N);
  radixSortU (N,u);
  normaliza (u,N);
}

#define TIMING
#define NREP 10000
int main () {
#ifdef TIMING
  long n = NREP;
  while (n--) {
#endif //TIMING
  AddInput(data);
  radixSort (SIZE, data);
  AddOutput(data);
#ifdef TIMING
  }
#endif //TIMING
  return 0;
}
