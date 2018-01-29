#include "../circgen.h"

int millionaires(int x, int y) {
	if (x < y)
		return 1;
	else
		return 0;
}

int main(void) {
	static int a, b, result;
	AddInput(a);
	AddInput(b);
	BeginCirc();
	result = millionaires(a, b);
	EndCirc();
	AddOutput(result);
	return 0;
}
