#include "../circgen.h"

/* checks if out[] is the sorting of in[] */
int isort_chk(int in[], int out[], int n) {
  int chk=0;
  int i,j,aux;
  for (i=1; i<n; i++) {
    aux = in[i];
    for (j=i; j>0 && aux<in[j-1]; j--) {
      in[j]=in[j-1];
    }
    in[j]=aux;
  }
  for (i=0; i<n; i++) {
    if (out[i] != in[i])
      chk = 1;
  }
  return chk;
}

#define SIZE 10

int res[SIZE];
int v[SIZE];
int accept=0;

int main() {
  AddInput(v);
  AddInput(res);
  BeginCirc();
  accept = isort_chk(v, res, SIZE);
  EndCirc();
  AddOutput(accept);
  return 0;
}
