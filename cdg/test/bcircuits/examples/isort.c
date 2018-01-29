#include "../circgen.h"

/* checks if out[] is the sorting of in[] */
void isort(int v[], int n) {
  int chk=0;
  int i,j,aux;
  for (i=1; i<n; i++) {
    aux = v[i];
    for (j=i; j>0 && aux<v[j-1]; j--) {
      v[j]=v[j-1];
    }
    v[j]=aux;
  }
}

#define SIZE 20

int res[SIZE];
int v[SIZE];
int accept=0;

int main() {
  AddInputR(v);
  BeginCirc();
  isort(v, SIZE);
  EndCirc();
  AddOutput(v);
  return 0;
}
