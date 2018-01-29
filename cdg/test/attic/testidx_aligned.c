#include "circgen.h"

#define SIZE 257
char idx_in, idx_out;
int out;
int v[SIZE];

int main() {
  AddInput(idx_in);
  AddInput(idx_out);
  int i;
__LOOP_UNROLL(SIZE)
  for (i=0; i<SIZE; i++) v[i]=i;
  out = v[idx_out] = v[idx_in];
  AddOutput(out);
  return 0;
}
