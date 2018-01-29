#include "../../circgen.h"

const unsigned int m1  = 0x55555555; //binary: 0101...
const unsigned int m2  = 0x33333333; //binary: 00110011..
const unsigned int m4  = 0x0f0f0f0f; //binary:  4 zeros,  4 ones ...
const unsigned int m8  = 0x00ff00ff; //binary:  8 zeros,  8 ones ...
const unsigned int m16 = 0x0000ffff; //binary: 16 zeros, 16 ones ...

int popcount_2(unsigned int y) {
    int x = y - ((y >> 1) & 0x55555555);             //put count of each 2 bits into those 2 bits
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333); //put count of each 4 bits into those 4 bits
    x = (x + (x >> 4)) & 0x0f0f0f0f;        //put count of each 8 bits into those 8 bits
    x += x >>  8;  //put count of each 16 bits into their lowest 8 bits
    x += x >> 16;  //put count of each 32 bits into their lowest 8 bits
    return x & 0x7f;
}


// 10 x 32 bit = 320 bit for each party
unsigned int INPUT_A_v; 
unsigned int INPUT_A_w; 
unsigned int INPUT_A_x; 
unsigned int INPUT_A_y; 
unsigned int INPUT_A_z; 
unsigned int INPUT_A_x0; 
unsigned int INPUT_A_x1; 
unsigned int INPUT_A_x2; 
unsigned int INPUT_A_x3; 
unsigned int INPUT_A_x4;

unsigned int INPUT_B_v; 
unsigned int INPUT_B_w; 
unsigned int INPUT_B_x; 
unsigned int INPUT_B_y; 
unsigned int INPUT_B_z;
unsigned int INPUT_B_y0; 
unsigned int INPUT_B_y1; 
unsigned int INPUT_B_y2; 
unsigned int INPUT_B_y3; 
unsigned int INPUT_B_y4;
int OUTPUTw;

int main(){
  AddInput(INPUT_A_v); 
  AddInput(INPUT_A_w); 
  AddInput(INPUT_A_x); 
  AddInput(INPUT_A_y); 
  AddInput(INPUT_A_z); 
  AddInput(INPUT_A_x0); 
  AddInput(INPUT_A_x1); 
  AddInput(INPUT_A_x2); 
  AddInput(INPUT_A_x3); 
  AddInput(INPUT_A_x4);
  AddInput(INPUT_B_v); 
  AddInput(INPUT_B_w); 
  AddInput(INPUT_B_x); 
  AddInput(INPUT_B_y); 
  AddInput(INPUT_B_z);
  AddInput(INPUT_B_y0); 
  AddInput(INPUT_B_y1); 
  AddInput(INPUT_B_y2); 
  AddInput(INPUT_B_y3); 
  AddInput(INPUT_B_y4);
  BeginCirc();

  int a = popcount_2(INPUT_B_v^INPUT_A_v) 
    + popcount_2(INPUT_A_w^INPUT_B_w) 
    + popcount_2(INPUT_A_x^INPUT_B_x) 
    + popcount_2(INPUT_A_y^INPUT_B_y) 
    + popcount_2(INPUT_A_z^INPUT_B_z) 
    + popcount_2(INPUT_A_x0^INPUT_B_y0) 
    + popcount_2(INPUT_A_x1^INPUT_B_y1) 
    + popcount_2(INPUT_A_x2^INPUT_B_y2) 
    + popcount_2(INPUT_A_x3^INPUT_B_y3) 
    + popcount_2(INPUT_A_x4^INPUT_B_y4);

  OUTPUTw = a;

  EndCirc();
  AddOutput(OUTPUTw);
	
  return 0;
}
