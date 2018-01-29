#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Test 5

  different branches acting on a local variable (cond-phi)
*/

int idata[2], odata;

int main() {
  AddInput(idata);
  int temp;
  if (idata[0] < idata[1])
    temp = idata[0];
  else
    temp = idata[1];
  odata = temp;
  AddOutput(odata);
  return 0;
}
