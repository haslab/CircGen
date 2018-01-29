#include "../circgen.h"

int a, b, c;
int f(){
  int res;
  if (a > b) {
    if (a > c) {res = a;} else { res = c; }
  }
  else {
    if (b > c) {res = b;} else { res = c; }
  }
  return res;
}

int main() {
  AddInput(a);
  AddInput(b);
  AddInput(c);
  BeginCirc();
  a = f();
  EndCirc();
  AddOutput(a);
  return 0;
}

