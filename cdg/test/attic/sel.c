#include "../circgen.h"

#define SIZE 23

static
unsigned int
data[SIZE];


int
main(void)
{
	static unsigned int a, result;
	AddInputR(a);
        AddInputR(data);
	BeginCirc();
	result = data[a%SIZE];
	EndCirc();
	AddOutput(result);
	return 0;
}
