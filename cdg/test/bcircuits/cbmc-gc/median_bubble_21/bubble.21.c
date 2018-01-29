#include "../../circgen.h"

  int INPUT_A_a0;
  int INPUT_A_a1;
  int INPUT_A_a2;
  int INPUT_A_a3;
  int INPUT_A_a4;
  int INPUT_A_a5;
  int INPUT_A_a6;
  int INPUT_A_a7;
  int INPUT_A_a8;
  int INPUT_A_a9;
  int INPUT_A_a10;
  int INPUT_A_a11;
  int INPUT_A_a12;
  int INPUT_A_a13;
  int INPUT_A_a14;
  int INPUT_A_a15;
  int INPUT_A_a16;
  int INPUT_A_a17;
  int INPUT_A_a18;
  int INPUT_A_a19;
  int INPUT_A_a20;
  int OUTPUT_median;


int main() {
  AddInput(INPUT_A_a0);
  AddInput(INPUT_A_a1);
  AddInput(INPUT_A_a2);
  AddInput(INPUT_A_a3);
  AddInput(INPUT_A_a4);
  AddInput(INPUT_A_a5);
  AddInput(INPUT_A_a6);
  AddInput(INPUT_A_a7);
  AddInput(INPUT_A_a8);
  AddInput(INPUT_A_a9);
  AddInput(INPUT_A_a10);
  AddInput(INPUT_A_a11);
  AddInput(INPUT_A_a12);
  AddInput(INPUT_A_a13);
  AddInput(INPUT_A_a14);
  AddInput(INPUT_A_a15);
  AddInput(INPUT_A_a16);
  AddInput(INPUT_A_a17);
  AddInput(INPUT_A_a18);
  AddInput(INPUT_A_a19);
  AddInput(INPUT_A_a20);
  BeginCirc();

  int arr[21];

  int i, j, tmp1, tmp2, inc;
  arr[0] = INPUT_A_a0;
  arr[1] = INPUT_A_a1;
  arr[2] = INPUT_A_a2;
  arr[3] = INPUT_A_a3;
  arr[4] = INPUT_A_a4;
  arr[5] = INPUT_A_a5;
  arr[6] = INPUT_A_a6;
  arr[7] = INPUT_A_a7;
  arr[8] = INPUT_A_a8;
  arr[9] = INPUT_A_a9;
  arr[10] = INPUT_A_a10;
  arr[11] = INPUT_A_a11;
  arr[12] = INPUT_A_a12;
  arr[13] = INPUT_A_a13;
  arr[14] = INPUT_A_a14;
  arr[15] = INPUT_A_a15;
  arr[16] = INPUT_A_a16;
  arr[17] = INPUT_A_a17;
  arr[18] = INPUT_A_a18;
  arr[19] = INPUT_A_a19;
  arr[20] = INPUT_A_a20;

  for (i = 20; i > 0; i--) {
    for (j = 0; j < i; j++) {
      inc = j + 1;
      tmp1 = arr[j];
      tmp2 = arr[inc];
      if (tmp1 > tmp2) {
	arr[j] = tmp2;
	arr[inc] = tmp1;
      }
    }
  }

  OUTPUT_median = arr[10];

  EndCirc();
  AddOutput(OUTPUT_median);

  return 0;
}
