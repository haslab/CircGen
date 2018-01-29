#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Insertion Sort
*/

void insert(int size, inv v[], int x) {
  while (size>0 && v[size-1]>x) {
    v[size] = v[size-1];
    size--;
  }
  v[size] = x;
}

void isort(int size, int v[]) {
  int i;
  for (i=0; i<size; i++)
    insert(i,v,v[i]);
}


/* Circuit inputs/outputs */
#define SIZE 10
int data[SIZE];

void main() {
  AddInput(data);
  isort(SIZE, v, x);
  AddOutput(data);
}
