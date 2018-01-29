#define AddInput(X) __builtin_mem_in(&X, sizeof(X));
#define AddOutput(X) __builtin_mem_out(&X, sizeof(X));

/*
  Test 1
*/

int idata, odata, glob;

void fcirc() {
  int temp;
  if (idata >= 0) {
    glob = idata;
    temp = 3;
  } else {
    glob = -idata;
    temp = 7;
  }
  odata = temp * glob;
}

int main() {
  AddInput(idata);
  fcirc();
  AddOutput(odata);
  return 0;
}
