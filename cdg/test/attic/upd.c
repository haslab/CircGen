#include "../circgen.h"

#define SIZE 23

static
unsigned int
data[SIZE];


int
main(void)
{
	static unsigned int a;
	AddInputR(a);
        AddInputR(data);
	BeginCirc();
	data[a%SIZE] = 0xFF557733;
	EndCirc();
	AddOutput(data);
	return 0;
}
