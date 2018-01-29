#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Max Sort
*/

int maxInd(int size, int v[]) {
  int i, pos=0;
  for (i=1; i<size; i++)
    if (v[i]>v[pos]) pos=i;
  return pos;
}

/* Circuit inputs/outputs */
#define SIZE 10
int data[SIZE];
int imax;

int main() {
  AddInput(data);
  imax = maxInd(SIZE, data);
  AddOutput(imax);
  return 0;
}
