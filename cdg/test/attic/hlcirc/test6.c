#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Test 6

  two different branches acting on a local variable (mixed xor/cond-phi)
*/

int idata[2], odata;

int main() {
  AddInput(idata);
  int temp;
  if (idata[0] < idata[1]) {
    if (idata[0] < 0)
      temp = idata[0];
    else
      temp = idata[1];
  } else {
    if (idata[0] < 0)
      temp = 3;
    else
      temp = 4;
  }
  odata = temp;
  AddOutput(odata);
  return 0;
}
