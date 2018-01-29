#include "../circgen.h"

static
int
data[] = { 123, 456, 789, 0xFFFF };

int
ce(int x)
{
	int idx;
	if (x) idx = 1; else idx = 2;
	return data[idx];
}

int
main(void)
{
	static int a, result;
	AddInput(a);
        AddInput(data);
	BeginCirc();
	result = ce(a);
	EndCirc();
	AddOutput(result);
	return 0;
}
