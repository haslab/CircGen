/*

This is an implementation of the AES128 algorithm, specifically ECB and CBC mode.

The implementation is verified against the test vectors in:
  National Institute of Standards and Technology Special Publication 800-38A 2001 ED

ECB-AES128
----------

  plain-text:
    6bc1bee22e409f96e93d7e117393172a
    ae2d8a571e03ac9c9eb76fac45af8e51
    30c81c46a35ce411e5fbc1191a0a52ef
    f69f2445df4f9b17ad2b417be66c3710

  key:
    2b7e151628aed2a6abf7158809cf4f3c

  resulting cipher
    3ad77bb40d7a3660a89ecaf32466ef97 
    f5d3d58503b9699de785895a96fdbaaf 
    43b1cd7f598ece23881b00e3ed030688 
    7b0c785e27e8ad3f8223207104725dd4 


NOTE:   String length must be evenly divisible by 16byte (str_len % 16 == 0)
        You should pad the end of the string with zeros if this is not the case.

*/


/*****************************************************************************/
/* Includes:                                                                 */
/*****************************************************************************/
#include <stdint.h>
//#include <string.h> // CBC mode, for memset
#include "circgen.h"




/* Optimized circuit for the AES SBox (forward direction).
   SOURCE: http://www.cs.yale.edu/homes/peralta/CircuitStuff/CMT.html
*/
uint8_t aes_sbox(uint8_t in) {
  uint32_t x0, x1, x2, x3, x4, x5, x6, x7;
  uint32_t y0, y1, y2, y3, y4, y5, y6, y7, y8, y9;
  uint32_t y10, y11, y12, y13, y14, y15, y16, y17, y18, y19;
  uint32_t y20, y21;
  uint32_t t0, t1, t2, t3, t4, t5, t6, t7, t8, t9;
  uint32_t t10, t11, t12, t13, t14, t15, t16, t17, t18, t19;
  uint32_t t20, t21, t22, t23, t24, t25, t26, t27, t28, t29;
  uint32_t t30, t31, t32, t33, t34, t35, t36, t37, t38, t39;
  uint32_t t40, t41, t42, t43, t44, t45, t46, t47, t48, t49;
  uint32_t t50, t51, t52, t53, t54, t55, t56, t57, t58, t59;
  uint32_t t60, t61, t62, t63, t64, t65, t66, t67;
  uint32_t z0, z1, z2, z3, z4, z5, z6, z7, z8, z9;
  uint32_t z10, z11, z12, z13, z14, z15, z16, z17;
  uint32_t s0, s1, s2, s3, s4, s5, s6, s7;

  x0 = __GET7(in);
  x1 = __GET6(in);
  x2 = __GET5(in);
  x3 = __GET4(in);
  x4 = __GET3(in);
  x5 = __GET2(in);
  x6 = __GET1(in);
  x7 = __GET0(in);

  // begin top linear transformation 
  y14 = __ADD(x3,x5);
  y13 = __ADD(x0,x6);
  y9 = __ADD(x0,x3);
  y8 = __ADD(x0,x5);
  t0 = __ADD(x1,x2);
  y1 = __ADD(t0,x7);
  y4 = __ADD(y1,x3);
  y12 = __ADD(y13,y14);
  y2 = __ADD(y1,x0);
  y5 = __ADD(y1,x6);
  y3 = __ADD(y5,y8);
  t1 = __ADD(x4,y12);
  y15 = __ADD(t1,x5);
  y20 = __ADD(t1,x1);
  y6 = __ADD(y15,x7);
  y10 = __ADD(y15,t0);
  y11 = __ADD(y20,y9);
  y7 = __ADD(x7,y11);
  y17 = __ADD(y10,y11);
  y19 = __ADD(y10,y8);
  y16 = __ADD(t0,y11);
  y21 = __ADD(y13,y16);
  y18 = __ADD(x0,y16);
  // end top linear transformation 
  t2 = __MUL(y12,y15);
  t3 = __MUL(y3,y6);
  t4 = __ADD(t3,t2);
  t5 = __MUL(y4,x7);
  t6 = __ADD(t5,t2); 
  t7 = __MUL(y13,y16);
  t8 = __MUL(y5,y1);
  t9 = __ADD(t8,t7);
  t10 = __MUL(y2,y7);
  t11 = __ADD(t10,t7);
  t12 = __MUL(y9,y11);
  t13 = __MUL(y14,y17);
  t14 = __ADD(t13,t12);
  t15 = __MUL(y8,y10);
  t16 = __ADD(t15,t12);
  t17 = __ADD(t4,t14);
  t18 = __ADD(t6,t16);
  t19 = __ADD(t9,t14);
  t20 = __ADD(t11,t16);
  t21 = __ADD(t17,y20);
  t22 = __ADD(t18,y19);
  t23 = __ADD(t19,y21);
  t24 = __ADD(t20,y18);
  // this next piece of the circuit is 
  // inversion in GF16, inputs are t21..24
  // and outputs are T37,T33,T40,T29.
  // Refer to paper for representation details
  // (tower field construction, normal basis (W,W^2) for extension   
  // from GF2 to GF4 and (Z^2,Z^8) for extension from GF4 to GF16).
  t25 = __ADD(t21,t22);
  t26 = __MUL(t21,t23);
  t27 = __ADD(t24,t26);
  t28 = __MUL(t25,t27); 
  t29 = __ADD(t28,t22);
  t30 = __ADD(t23,t24);
  t31 = __ADD(t22,t26);
  t32 = __MUL(t31,t30);
  t33 = __ADD(t32,t24);
  t34 = __ADD(t23,t33);
  t35 = __ADD(t27,t33);
  t36 = __MUL(t24,t35); 
  t37 = __ADD(t36,t34);
  t38 = __ADD(t27,t36);
  t39 = __MUL(t29,t38);
  t40 = __ADD(t25,t39);
  // end GF16 inversion
  t41 = __ADD(t40,t37);
  t42 = __ADD(t29,t33);
  t43 = __ADD(t29,t40);
  t44 = __ADD(t33,t37);
  t45 = __ADD(t42,t41);
  z0 = __MUL(t44,y15);
  z1 = __MUL(t37,y6);
  z2 = __MUL(t33,x7);
  z3 = __MUL(t43,y16);
  z4 = __MUL(t40,y1);
  z5 = __MUL(t29,y7);
  z6 = __MUL(t42,y11);
  z7 = __MUL(t45,y17);
  z8 = __MUL(t41,y10);
  z9 = __MUL(t44,y12);
  z10 = __MUL(t37,y3);
  z11 = __MUL(t33,y4);
  z12 = __MUL(t43,y13);
  z13 = __MUL(t40,y5);
  z14 = __MUL(t29,y2);
  z15 = __MUL(t42,y9);
  z16 = __MUL(t45,y14);
  z17 = __MUL(t41,y8);
  // begin end linear transformation 
  t46 = __ADD(z15,z16);
  t47 = __ADD(z10,z11);
  t48 = __ADD(z5,z13);
  t49 = __ADD(z9,z10);
  t50 = __ADD(z2,z12);
  t51 = __ADD(z2,z5);
  t52 = __ADD(z7,z8);
  t53 = __ADD(z0,z3);
  t54 = __ADD(z6,z7);
  t55 = __ADD(z16,z17);
  t56 = __ADD(z12,t48);
  t57 = __ADD(t50,t53);
  t58 = __ADD(z4,t46);
  t59 = __ADD(z3,t54);
  t60 = __ADD(t46,t57);
  t61 = __ADD(z14,t57);
  t62 = __ADD(t52,t58);
  t63 = __ADD(t49,t58);
  t64 = __ADD(z4,t59);
  t65 = __ADD(t61,t62);
  t66 = __ADD(z1,t63);
  s0 = __ADD(t59,t63);
  s6 = __XNOR(t56,t62); 
  s7 = __XNOR(t48,t60); 
  t67 = __ADD(t64,t65);
  s3 = __ADD(t53,t66);
  s4 = __ADD(t51,t66);
  s5 = __ADD(t47,t65);
  s1 = __XNOR(t64,s3); 
  s2 = __XNOR(t55,t67); 

  uint8_t out = 0;
  out = __SET7(out,s0);
  out = __SET6(out,s1);
  out = __SET5(out,s2);
  out = __SET4(out,s3);
  out = __SET3(out,s4);
  out = __SET2(out,s5);
  out = __SET1(out,s6);
  out = __SET0(out,s7);
  return out;
}

static const uint8_t sbox[256] =   {
  //0     1    2      3     4    5     6     7      8    9     A      B    C     D     E     F
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 };


/*****************************************************************************/
/* Defines:                                                                  */
/*****************************************************************************/
// The number of columns comprising a state in AES. This is a constant in AES. Value=4
#define Nb 4
// The number of 32 bit words in a key.
#define Nk 4
// Key length in bytes [128 bit]
#define KEYLEN 16
// The number of rounds in AES Cipher.
#define Nr 10


/*****************************************************************************/
/* Private variables:                                                        */
/*****************************************************************************/
// state - array holding the intermediate results during decryption.
typedef uint8_t state_t[4][4];

// The round constant word array, Rcon[i], contains the values given by 
// x to th e power (i-1) being powers of x (x is denoted as {02}) in the field GF(2^8)
// Note that i starts at 1, not 0).
static const uint8_t Rcon[255] = {
  0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 
  0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 
  0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 
  0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 
  0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 
  0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 
  0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 
  0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 
  0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 
  0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 
  0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 
  0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 
  0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 
  0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 
  0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 
  0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb  };


/*****************************************************************************/
/* Private functions:                                                        */
/*****************************************************************************/
static uint8_t getSBoxValue(uint8_t num)
{
  return aes_sbox(num); //sbox[num]; 
}


// This function produces Nb(Nr+1) round keys. The round keys are used in each round to decrypt the states. 
static void KeyExpansion(uint8_t Key[], uint8_t RoundKey[])
{
  uint32_t i, j, k;
  uint8_t tempa[4]; // Used for the column/row operations
  
  // The first round key is the key itself.
__LOOP_UNROLL(4)
  for(i = 0; i < Nk; ++i)
  {
    RoundKey[(i * 4) + 0] = Key[(i * 4) + 0];
    RoundKey[(i * 4) + 1] = Key[(i * 4) + 1];
    RoundKey[(i * 4) + 2] = Key[(i * 4) + 2];
    RoundKey[(i * 4) + 3] = Key[(i * 4) + 3];
  }

  // All other round keys are found from the previous round keys.
__LOOP_UNROLL(40)
  for(i=4; (i < (Nb * (Nr + 1))); ++i)
  {
__LOOP_UNROLL(4)
    for(j = 0; j < 4; ++j)
    {
      tempa[j]=RoundKey[(i-1) * 4 + j];
    }
    if (i % Nk == 0)
    {
      // This function rotates the 4 bytes in a word to the left once.
      // [a0,a1,a2,a3] becomes [a1,a2,a3,a0]

      // Function RotWord()
      {
        k = tempa[0];
        tempa[0] = tempa[1];
        tempa[1] = tempa[2];
        tempa[2] = tempa[3];
        tempa[3] = k;
      }

      // SubWord() is a function that takes a four-byte input word and 
      // applies the S-box to each of the four bytes to produce an output word.

      // Function Subword()
      {
        tempa[0] = getSBoxValue(tempa[0]);
        tempa[1] = getSBoxValue(tempa[1]);
        tempa[2] = getSBoxValue(tempa[2]);
        tempa[3] = getSBoxValue(tempa[3]);
      }

      tempa[0] =  tempa[0] ^ Rcon[i/Nk];
    }
    else if (Nk > 6 && i % Nk == 4)
    {
      // Function Subword()
      {
        tempa[0] = getSBoxValue(tempa[0]);
        tempa[1] = getSBoxValue(tempa[1]);
        tempa[2] = getSBoxValue(tempa[2]);
        tempa[3] = getSBoxValue(tempa[3]);
      }
    }
    RoundKey[i * 4 + 0] = RoundKey[(i - Nk) * 4 + 0] ^ tempa[0];
    RoundKey[i * 4 + 1] = RoundKey[(i - Nk) * 4 + 1] ^ tempa[1];
    RoundKey[i * 4 + 2] = RoundKey[(i - Nk) * 4 + 2] ^ tempa[2];
    RoundKey[i * 4 + 3] = RoundKey[(i - Nk) * 4 + 3] ^ tempa[3];
  }
}

// This function adds the round key to state.
// The round key is added to the state by an XOR function.
static void AddRoundKey(uint8_t round, uint8_t RoundKey[], state_t state)
{
  uint8_t i,j;
__LOOP_UNROLL(4)
  for(i=0;i<4;++i)
  {
__LOOP_UNROLL(4)
    for(j = 0; j < 4; ++j)
    {
      state[i][j] ^= RoundKey[round * Nb * 4 + i * Nb + j];
    }
  }
}

// The SubBytes Function Substitutes the values in the
// state matrix with values in an S-box.
static void SubBytes(state_t state)
{
  uint8_t i, j;
__LOOP_UNROLL(4)
  for(i = 0; i < 4; ++i)
  {
__LOOP_UNROLL(4)
    for(j = 0; j < 4; ++j)
    {
      state[j][i] = getSBoxValue(state[j][i]);
    }
  }
}

// The ShiftRows() function shifts the rows in the state to the left.
// Each row is shifted with different offset.
// Offset = Row number. So the first row is not shifted.
static void ShiftRows(state_t state)
{
  uint8_t temp;

  // Rotate first row 1 columns to left  
  temp           = state[0][1];
  state[0][1] = state[1][1];
  state[1][1] = state[2][1];
  state[2][1] = state[3][1];
  state[3][1] = temp;

  // Rotate second row 2 columns to left  
  temp        = state[0][2];
  state[0][2] = state[2][2];
  state[2][2] = temp;

  temp        = state[1][2];
  state[1][2] = state[3][2];
  state[3][2] = temp;

  // Rotate third row 3 columns to left
  temp        = state[0][3];
  state[0][3] = state[3][3];
  state[3][3] = state[2][3];
  state[2][3] = state[1][3];
  state[1][3] = temp;
}

static uint8_t xtime(uint8_t x)
{
  return ((x<<1) ^ (((x>>7) & 1) * 0x1b));
}

// MixColumns function mixes the columns of the state matrix
static void MixColumns(state_t state)
{
  uint8_t i;
  uint8_t Tmp,Tm,t;
__LOOP_UNROLL(4)
  for(i = 0; i < 4; ++i)
  {  
    t   = state[i][0];
    Tmp = state[i][0] ^ state[i][1] ^ state[i][2] ^ state[i][3] ;
    Tm  = state[i][0] ^ state[i][1] ; Tm = xtime(Tm);  state[i][0] ^= Tm ^ Tmp ;
    Tm  = state[i][1] ^ state[i][2] ; Tm = xtime(Tm);  state[i][1] ^= Tm ^ Tmp ;
    Tm  = state[i][2] ^ state[i][3] ; Tm = xtime(Tm);  state[i][2] ^= Tm ^ Tmp ;
    Tm  = state[i][3] ^ t ;           Tm = xtime(Tm);  state[i][3] ^= Tm ^ Tmp ;
  }
}

static uint8_t Multiply(uint8_t x, uint8_t y)
{
  return (((y & 1) * x) ^
       ((y>>1 & 1) * xtime(x)) ^
       ((y>>2 & 1) * xtime(xtime(x))) ^
       ((y>>3 & 1) * xtime(xtime(xtime(x)))) ^
       ((y>>4 & 1) * xtime(xtime(xtime(xtime(x))))));
  }



// Cipher is the main function that encrypts the PlainText.
static void Cipher(uint8_t RoundKey[], state_t state)
{
  uint8_t round = 0;

  // Add the First round key to the state before starting the rounds.
  AddRoundKey(0, RoundKey, state); 
  
  // There will be Nr rounds.
  // The first Nr-1 rounds are identical.
  // These Nr-1 rounds are executed in the loop below.
__LOOP_UNROLL(Nr)
  for(round = 1; round < Nr; ++round)
  {
    SubBytes(state);
    ShiftRows(state);
    MixColumns(state);
    AddRoundKey(round, RoundKey, state);
  }
  
  // The last round is given below.
  // The MixColumns function is not here in the last round.
  SubBytes(state);
  ShiftRows(state);
  AddRoundKey(Nr, RoundKey, state);
}


static void BlockCopy(uint8_t* output, uint8_t* input)
{
  uint8_t i;
__LOOP_UNROLL(KEYLEN)
  for (i=0;i<KEYLEN;++i)
  {
    output[i] = input[i];
  }
}



/*****************************************************************************/
/* Public functions:                                                         */
/*****************************************************************************/


// The array that stores the round keys.
uint8_t RoundKey[KEYLEN*(Nr+1)];

// The Key input to the AES Program
static const uint8_t Key[KEYLEN];
uint8_t inout[KEYLEN];


int main() {
  AddInput(Key);
  AddInput(inout);
  KeyExpansion(Key, RoundKey);
  Cipher(RoundKey, inout);
  AddOutput(inout);
  return 0;
}


