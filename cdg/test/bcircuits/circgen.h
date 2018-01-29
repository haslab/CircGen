
#ifndef __CIRCGEN_H__

#define __CIRCGEN_H__

#ifdef __COMPCERT__

#define _EXEC_PRAGMA(X) _Pragma(#X)
#define __LOOP_UNROLL(S) _EXEC_PRAGMA(loop_unroll S)

#include <stdint.h>

static
volatile
uint8_t
__circgen_input_output;

static
void
circgen_input(void * X, uint32_t len)
{
	unsigned char * const t = X;
__LOOP_UNROLL(0)
	for (uint32_t i = 0; i < len; ++i)
		t[i] = __circgen_input_output;
}

static
void
circgen_output(const void * X, uint32_t len)
{
	const unsigned char * const t = X;
__LOOP_UNROLL(0)
	for (uint32_t i = 0; i < len; ++i)
		__circgen_input_output = t[i];
}

#define AddInput(X) circgen_input(&X, sizeof(X))
#define AddOutput(X) circgen_output(&X, sizeof(X))

#define AddInputR(X) AddInput(X)

void __circgen_fence(void);

#define BeginCirc __circgen_fence
#define EndCirc __circgen_fence

#else

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <time.h>

/* Reads hex input (lsb first) */
void __read_INPUT(char *inb, long size) {
  long i;
  char cbuf[3] = {0, 0, 0};
  /* initialize memory region */
  for (i=0; i<size; i++) inb[i] = 0;
  /* read given input */
  for (i=0; i<size; i++) {
    if ((cbuf[0]=getchar()) == EOF || !isxdigit(cbuf[0])) break;
    if ((cbuf[1]=getchar()) == EOF || !isxdigit(cbuf[1])) break;
    inb[i] = strtol(cbuf, NULL, 16);
  }
}

#define AddInput(X) __read_INPUT((char*)&X, sizeof(X));

void __rnd_INPUT(unsigned char *inb, long size) {
  long i;
  srand(time(NULL));
  for (i=0; i<size; i++) {
    inb[i] = rand();
    printf("%02x",inb[i]);
  }

}

#define AddInputR(X) __rnd_INPUT((unsigned char*)&X, sizeof(X));

/* Reads hex output (lsb first) */
void __write_OUTPUT(char *outb, long size) {
  printf("\n");
  while (size-- > 0)
    printf("%02x",(unsigned char)*outb++);
  printf("\n");
}

#define AddOutput(X) __write_OUTPUT((char*)&X, sizeof(X));

#define __LOOP_UNROLL(X)

#define BeginCirc()
#define EndCirc()

#endif /* __COMPCERT__ */


#define __GET_POS(x,p) (((unsigned int)(unsigned char)x << (31-p)) >> 31)
#define __GET0(x) __GET_POS(x,0)
#define __GET1(x) __GET_POS(x,1)
#define __GET2(x) __GET_POS(x,2)
#define __GET3(x) __GET_POS(x,3)
#define __GET4(x) __GET_POS(x,4)
#define __GET5(x) __GET_POS(x,5)
#define __GET6(x) __GET_POS(x,6)
#define __GET7(x) __GET_POS(x,7)

#define __SET0(x,b) (((unsigned int)(unsigned char)x>>1) << 1) ^ b
#define __SET_POS(x,b,P) (((((unsigned int)(unsigned char)x>>(P+1)) << 1) ^ b) << P) ^ (((unsigned int)(unsigned char)x<<(32-P))>>(32-P))
#define __SET1(x,b) __SET_POS(x,b,1)
#define __SET2(x,b) __SET_POS(x,b,2)
#define __SET3(x,b) __SET_POS(x,b,3)
#define __SET4(x,b) __SET_POS(x,b,4)
#define __SET5(x,b) __SET_POS(x,b,5)
#define __SET6(x,b) __SET_POS(x,b,6)
#define __SET7(x,b) __SET_POS(x,b,7)

#define __ADD(a,b) (a^b)
#define __MUL(a,b) (a&b)
#define __XNOR(a,b) (__ADD(__ADD(a,b),1))

#endif /* __CIRCGEN_H__ */
