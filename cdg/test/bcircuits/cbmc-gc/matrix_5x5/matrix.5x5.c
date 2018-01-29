#include "../../circgen.h"

#define S 5

int A[25];
int B[25];
int C[25];

void multiply();

int INPUT_A_0;
int INPUT_A_1;
int INPUT_A_2;
int INPUT_A_3;
int INPUT_A_4;
int INPUT_A_5;
int INPUT_A_6;
int INPUT_A_7;
int INPUT_A_8;
int INPUT_A_9;
int INPUT_A_10;
int INPUT_A_11;
int INPUT_A_12;
int INPUT_A_13;
int INPUT_A_14;
int INPUT_A_15;
int INPUT_A_16;
int INPUT_A_17;
int INPUT_A_18;
int INPUT_A_19;
int INPUT_A_20;
int INPUT_A_21;
int INPUT_A_22;
int INPUT_A_23;
int INPUT_A_24;
int INPUT_B_0;
int INPUT_B_1;
int INPUT_B_2;
int INPUT_B_3;
int INPUT_B_4;
int INPUT_B_5;
int INPUT_B_6;
int INPUT_B_7;
int INPUT_B_8;
int INPUT_B_9;
int INPUT_B_10;
int INPUT_B_11;
int INPUT_B_12;
int INPUT_B_13;
int INPUT_B_14;
int INPUT_B_15;
int INPUT_B_16;
int INPUT_B_17;
int INPUT_B_18;
int INPUT_B_19;
int INPUT_B_20;
int INPUT_B_21;
int INPUT_B_22;
int INPUT_B_23;
int INPUT_B_24;

int OUTPUT_0;
int OUTPUT_1;
int OUTPUT_2;
int OUTPUT_3;
int OUTPUT_4;
int OUTPUT_5;
int OUTPUT_6;
int OUTPUT_7;
int OUTPUT_8;
int OUTPUT_9;
int OUTPUT_10;
int OUTPUT_11;
int OUTPUT_12;
int OUTPUT_13;
int OUTPUT_14;
int OUTPUT_15;
int OUTPUT_16;
int OUTPUT_17;
int OUTPUT_18;
int OUTPUT_19;
int OUTPUT_20;
int OUTPUT_21;
int OUTPUT_22;
int OUTPUT_23;
int OUTPUT_24;

int main() {


  unsigned i;

  AddInput(INPUT_A_0);
  AddInput(INPUT_A_1);
  AddInput(INPUT_A_2);
  AddInput(INPUT_A_3);
  AddInput(INPUT_A_4);
  AddInput(INPUT_A_5);
  AddInput(INPUT_A_6);
  AddInput(INPUT_A_7);
  AddInput(INPUT_A_8);
  AddInput(INPUT_A_9);
  AddInput(INPUT_A_10);
  AddInput(INPUT_A_11);
  AddInput(INPUT_A_12);
  AddInput(INPUT_A_13);
  AddInput(INPUT_A_14);
  AddInput(INPUT_A_15);
  AddInput(INPUT_A_16);
  AddInput(INPUT_A_17);
  AddInput(INPUT_A_18);
  AddInput(INPUT_A_19);
  AddInput(INPUT_A_20);
  AddInput(INPUT_A_21);
  AddInput(INPUT_A_22);
  AddInput(INPUT_A_23);
  AddInput(INPUT_A_24);
  AddInput(INPUT_B_0);
  AddInput(INPUT_B_1);
  AddInput(INPUT_B_2);
  AddInput(INPUT_B_3);
  AddInput(INPUT_B_4);
  AddInput(INPUT_B_5);
  AddInput(INPUT_B_6);
  AddInput(INPUT_B_7);
  AddInput(INPUT_B_8);
  AddInput(INPUT_B_9);
  AddInput(INPUT_B_10);
  AddInput(INPUT_B_11);
  AddInput(INPUT_B_12);
  AddInput(INPUT_B_13);
  AddInput(INPUT_B_14);
  AddInput(INPUT_B_15);
  AddInput(INPUT_B_16);
  AddInput(INPUT_B_17);
  AddInput(INPUT_B_18);
  AddInput(INPUT_B_19);
  AddInput(INPUT_B_20);
  AddInput(INPUT_B_21);
  AddInput(INPUT_B_22);
  AddInput(INPUT_B_23);
  AddInput(INPUT_B_24);
  BeginCirc();

  A[0] = INPUT_A_0;
  A[1] = INPUT_A_1;
  A[2] = INPUT_A_2;
  A[3] = INPUT_A_3;
  A[4] = INPUT_A_4;
  A[5] = INPUT_A_5;
  A[6] = INPUT_A_6;
  A[7] = INPUT_A_7;
  A[8] = INPUT_A_8;
  A[9] = INPUT_A_9;
  A[10] = INPUT_A_10;
  A[11] = INPUT_A_11;
  A[12] = INPUT_A_12;
  A[13] = INPUT_A_13;
  A[14] = INPUT_A_14;
  A[15] = INPUT_A_15;
  A[16] = INPUT_A_16;
  A[17] = INPUT_A_17;
  A[18] = INPUT_A_18;
  A[19] = INPUT_A_19;
  A[20] = INPUT_A_20;
  A[21] = INPUT_A_21;
  A[22] = INPUT_A_22;
  A[23] = INPUT_A_23;
  A[24] = INPUT_A_24;

  B[0] = INPUT_B_0;
  B[1] = INPUT_B_1;
  B[2] = INPUT_B_2;
  B[3] = INPUT_B_3;
  B[4] = INPUT_B_4;
  B[5] = INPUT_B_5;
  B[6] = INPUT_B_6;
  B[7] = INPUT_B_7;
  B[8] = INPUT_B_8;
  B[9] = INPUT_B_9;
  B[10] = INPUT_B_10;
  B[11] = INPUT_B_11;
  B[12] = INPUT_B_12;
  B[13] = INPUT_B_13;
  B[14] = INPUT_B_14;
  B[15] = INPUT_B_15;
  B[16] = INPUT_B_16;
  B[17] = INPUT_B_17;
  B[18] = INPUT_B_18;
  B[19] = INPUT_B_19;
  B[20] = INPUT_B_20;
  B[21] = INPUT_B_21;
  B[22] = INPUT_B_22;
  B[23] = INPUT_B_23;
  B[24] = INPUT_B_24;

  for (i = 0; i < 25; i++) {
    C[i] = 0;
  }

  multiply();

  OUTPUT_0 = C[0];
  OUTPUT_1 = C[1];
  OUTPUT_2 = C[2];
  OUTPUT_3 = C[3];
  OUTPUT_4 = C[4];
  OUTPUT_5 = C[5];
  OUTPUT_6 = C[6];
  OUTPUT_7 = C[7];
  OUTPUT_8 = C[8];
  OUTPUT_9 = C[9];
  OUTPUT_10 = C[10];
  OUTPUT_11 = C[11];
  OUTPUT_12 = C[12];
  OUTPUT_13 = C[13];
  OUTPUT_14 = C[14];
  OUTPUT_15 = C[15];
  OUTPUT_16 = C[16];
  OUTPUT_17 = C[17];
  OUTPUT_18 = C[18];
  OUTPUT_19 = C[19];
  OUTPUT_20 = C[20];
  OUTPUT_21 = C[21];
  OUTPUT_22 = C[22];
  OUTPUT_23 = C[23];
  OUTPUT_24 = C[24];

  EndCirc();
  AddOutput(OUTPUT_0);
  AddOutput(OUTPUT_1);
  AddOutput(OUTPUT_2);
  AddOutput(OUTPUT_3);
  AddOutput(OUTPUT_4);
  AddOutput(OUTPUT_5);
  AddOutput(OUTPUT_6);
  AddOutput(OUTPUT_7);
  AddOutput(OUTPUT_8);
  AddOutput(OUTPUT_9);
  AddOutput(OUTPUT_10);
  AddOutput(OUTPUT_11);
  AddOutput(OUTPUT_12);
  AddOutput(OUTPUT_13);
  AddOutput(OUTPUT_14);
  AddOutput(OUTPUT_15);
  AddOutput(OUTPUT_16);
  AddOutput(OUTPUT_17);
  AddOutput(OUTPUT_18);
  AddOutput(OUTPUT_19);
  AddOutput(OUTPUT_20);
  AddOutput(OUTPUT_21);
  AddOutput(OUTPUT_22);
  AddOutput(OUTPUT_23);
  AddOutput(OUTPUT_24);

  return 0;
}


void multiply() {
  int i = 0;
  int j = 0;
  int k = 0;
  int index = 0;
  int tmp_a;
  int tmp_b;
  int tmp_c;

  for (i = 0; i < S; i++) {
    for (j = 0; j < S; j++) {
      for (k = 0; k < S; k++) {
        C[S * i + j] += A[S * i + k] * B[S * k + j];
      }
    }
  }
}

