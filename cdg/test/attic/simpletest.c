#include "../circgen.h"

#define SIZE 100  // size of inputs/output (in bytes)

unsigned char in1[SIZE], in2[SIZE], out[SIZE];

void bxor(unsigned int n, unsigned char out[],
          unsigned char in1[], unsigned char in2[]) {
__LOOP_UNROLL(SIZE)
  for (;n>0;) {n--; out[n] = in1[n] ^ in2[n];}
}

int main() {
  AddInput(in1);
  AddInput(in2);
  BeginCirc();
  bxor(SIZE,out,in1,in2);
  EndCirc();
  AddOutput(out);
  return 0;
}
