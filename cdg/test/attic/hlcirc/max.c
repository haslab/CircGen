#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Max Sort
*/

int idata odata;

int main() {
  AddInput(idata);
  odata = idata;
  AddOutput(omax);
  return 0;
}
