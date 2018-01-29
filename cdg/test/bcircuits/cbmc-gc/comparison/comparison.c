#include "../../circgen.h"

int INPUT_B_x;
int INPUT_A_y;
int OUTPUTz;

int main(){

	int z;

	AddInput(INPUT_A_y);
	AddInput(INPUT_B_x);
	BeginCirc();

	z = 1;

	if (INPUT_B_x > INPUT_A_y) {
		z = 0;
	}

	OUTPUTz = z;

	EndCirc();
	AddOutput(OUTPUTz);

	return 0;
}

