#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Test 3

  two different branches acting on a global variable
*/

int idata[2], temp, odata;

int main() {
  AddInput(idata);
  if (idata[0] < idata[1])
    temp = 2;
  else
    temp = 3;
  odata = temp;
  AddOutput(odata);
  return 0;
}
