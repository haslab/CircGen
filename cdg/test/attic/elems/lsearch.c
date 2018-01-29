/*
  Linear Search
*/


#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));


void lsearch(int size, int v[], int x) {
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

void main() {
  AddInput(data);
  AddInput(x);
  i = lsearch(sizeof(v)/sizeof(int), v, x);
  AddOutput(i);
}
