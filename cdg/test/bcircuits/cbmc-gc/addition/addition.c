#include "../../circgen.h"

int INPUT_A_y;
int INPUT_B_x;
int OUTPUTw;

int main()
{
  AddInput(INPUT_A_y);
  AddInput(INPUT_B_x);
  BeginCirc();
  OUTPUTw = INPUT_B_x + INPUT_A_y;
  EndCirc();
  AddOutput(OUTPUTw);
  return 0;
}
