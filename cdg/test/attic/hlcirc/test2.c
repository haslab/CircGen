#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Test 2
*/

#define SIZE 10
int idata[SIZE], odata[SIZE];

int main() {
  int i;
  AddInput(idata);
  for (i=0; i<SIZE; i++) odata[i] = idata[i];
  AddOutput(odata);
  return 0;
}
