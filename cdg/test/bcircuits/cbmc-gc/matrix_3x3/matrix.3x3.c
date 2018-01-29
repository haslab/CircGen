#include "../../circgen.h"

#define S 3

int A[9];
int B[9];
int C[9];

void multiply();

int INPUT_A_a; 
int INPUT_A_b; 
int INPUT_A_c; 
int INPUT_A_d; 
int INPUT_A_e; 
int INPUT_A_f; 
int INPUT_A_g; 
int INPUT_A_h; 
int INPUT_A_i;
int INPUT_B_a; 
int INPUT_B_b; 
int INPUT_B_c; 
int INPUT_B_d; 
int INPUT_B_e; 
int INPUT_B_f; 
int INPUT_B_g; 
int INPUT_B_h; 
int INPUT_B_i;

int OUTPUT_r1, OUTPUT_r2, OUTPUT_r3, OUTPUT_r4, OUTPUT_r5, OUTPUT_r6, OUTPUT_r7, OUTPUT_r8, OUTPUT_r9;
	
int main() {

  AddInput(INPUT_A_a); 
  AddInput(INPUT_A_b); 
  AddInput(INPUT_A_c); 
  AddInput(INPUT_A_d); 
  AddInput(INPUT_A_e); 
  AddInput(INPUT_A_f); 
  AddInput(INPUT_A_g); 
  AddInput(INPUT_A_h); 
  AddInput(INPUT_A_i);
  AddInput(INPUT_B_a); 
  AddInput(INPUT_B_b); 
  AddInput(INPUT_B_c); 
  AddInput(INPUT_B_d); 
  AddInput(INPUT_B_e); 
  AddInput(INPUT_B_f); 
  AddInput(INPUT_B_g); 
  AddInput(INPUT_B_h); 
  AddInput(INPUT_B_i);
  BeginCirc();

  unsigned i;

  A[0] = INPUT_A_a;
  A[1] = INPUT_A_b;
  A[2] = INPUT_A_c;
  A[3] = INPUT_A_d;
  A[4] = INPUT_A_e;
  A[5] = INPUT_A_f;
  A[6] = INPUT_A_g;
  A[7] = INPUT_A_h;
  A[8] = INPUT_A_i;

  B[0] = INPUT_B_a;
  B[1] = INPUT_B_b;
  B[2] = INPUT_B_c;
  B[3] = INPUT_B_d;
  B[4] = INPUT_B_e;
  B[5] = INPUT_B_f;
  B[6] = INPUT_B_g;
  B[7] = INPUT_B_h;
  B[8] = INPUT_B_i;

  for (i = 0; i < 9; i++) {
    C[i] = 0;
  }

  multiply();

  OUTPUT_r1 = C[0];
  OUTPUT_r2 = C[1];
  OUTPUT_r3 = C[2];
  OUTPUT_r4 = C[3];
  OUTPUT_r5 = C[4];
  OUTPUT_r6 = C[5];
  OUTPUT_r7 = C[6];
  OUTPUT_r8 = C[7];
  OUTPUT_r9 = C[8];

  EndCirc();
  AddOutput(OUTPUT_r1);
  AddOutput(OUTPUT_r2);
  AddOutput(OUTPUT_r3);
  AddOutput(OUTPUT_r4);
  AddOutput(OUTPUT_r5);
  AddOutput(OUTPUT_r6);
  AddOutput(OUTPUT_r7);
  AddOutput(OUTPUT_r8);
  AddOutput(OUTPUT_r9);

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

