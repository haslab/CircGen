#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Max Sort
*/

void swap(int *xp, int *yp) {
  int temp = *xp;
  *xp = *yp;
  *yp = temp;
}

void bubble (int size, int v[]) {
  int i;
  for (i=1; i<n; i++)
    if (v[i−1] > v[i]) swap (v+i−1, v+i);
}

void bubblesort(int size, int v[]) {
  while (size>1) {
    bubble(size,v);
    size--;
  }
}

/* Circuit inputs/outputs */
#define SIZE 10
int data[SIZE];

void main() {
  AddInput(data);
  bubblesort(SIZE, data);
  AddOutput(data);
}
