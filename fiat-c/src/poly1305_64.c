/* Autogenerated: src/ExtractionOCaml/unsaturated_solinas --static poly1305 3 '2^130 - 5' 64 carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes */
/* curve description: poly1305 */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes */
/* n = 3 (from "3") */
/* s-c = 2^130 - [(1, 5)] (from "2^130 - 5") */
/* machine_wordsize = 64 (from "64") */

/* Computed values: */
/* carry_chain = [0, 1, 2, 0, 1] */

#include <stdint.h>
typedef unsigned char fiat_poly1305_uint1;
typedef signed char fiat_poly1305_int1;
typedef signed __int128 fiat_poly1305_int128;
typedef unsigned __int128 fiat_poly1305_uint128;

#if (-1 & 3) != 3
#error "This code only works on a two's complement system"
#endif


/*
 * The function fiat_poly1305_addcarryx_u44 is an addition with carry.
 * Postconditions:
 *   out1 = (arg1 + arg2 + arg3) mod 2^44
 *   out2 = ⌊(arg1 + arg2 + arg3) / 2^44⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xfffffffffff]
 *   arg3: [0x0 ~> 0xfffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xfffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_poly1305_addcarryx_u44(uint64_t* out1, fiat_poly1305_uint1* out2, fiat_poly1305_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  uint64_t x1 = ((arg1 + arg2) + arg3);
  uint64_t x2 = (x1 & UINT64_C(0xfffffffffff));
  fiat_poly1305_uint1 x3 = (fiat_poly1305_uint1)(x1 >> 44);
  *out1 = x2;
  *out2 = x3;
}

/*
 * The function fiat_poly1305_subborrowx_u44 is a subtraction with borrow.
 * Postconditions:
 *   out1 = (-arg1 + arg2 + -arg3) mod 2^44
 *   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^44⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xfffffffffff]
 *   arg3: [0x0 ~> 0xfffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xfffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_poly1305_subborrowx_u44(uint64_t* out1, fiat_poly1305_uint1* out2, fiat_poly1305_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  int64_t x1 = ((int64_t)(arg2 - (int64_t)arg1) - (int64_t)arg3);
  fiat_poly1305_int1 x2 = (fiat_poly1305_int1)(x1 >> 44);
  uint64_t x3 = (x1 & UINT64_C(0xfffffffffff));
  *out1 = x3;
  *out2 = (fiat_poly1305_uint1)(0x0 - x2);
}

/*
 * The function fiat_poly1305_addcarryx_u43 is an addition with carry.
 * Postconditions:
 *   out1 = (arg1 + arg2 + arg3) mod 2^43
 *   out2 = ⌊(arg1 + arg2 + arg3) / 2^43⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x7ffffffffff]
 *   arg3: [0x0 ~> 0x7ffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x7ffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_poly1305_addcarryx_u43(uint64_t* out1, fiat_poly1305_uint1* out2, fiat_poly1305_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  uint64_t x1 = ((arg1 + arg2) + arg3);
  uint64_t x2 = (x1 & UINT64_C(0x7ffffffffff));
  fiat_poly1305_uint1 x3 = (fiat_poly1305_uint1)(x1 >> 43);
  *out1 = x2;
  *out2 = x3;
}

/*
 * The function fiat_poly1305_subborrowx_u43 is a subtraction with borrow.
 * Postconditions:
 *   out1 = (-arg1 + arg2 + -arg3) mod 2^43
 *   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^43⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x7ffffffffff]
 *   arg3: [0x0 ~> 0x7ffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x7ffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_poly1305_subborrowx_u43(uint64_t* out1, fiat_poly1305_uint1* out2, fiat_poly1305_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  int64_t x1 = ((int64_t)(arg2 - (int64_t)arg1) - (int64_t)arg3);
  fiat_poly1305_int1 x2 = (fiat_poly1305_int1)(x1 >> 43);
  uint64_t x3 = (x1 & UINT64_C(0x7ffffffffff));
  *out1 = x3;
  *out2 = (fiat_poly1305_uint1)(0x0 - x2);
}

/*
 * The function fiat_poly1305_cmovznz_u64 is a single-word conditional move.
 * Postconditions:
 *   out1 = (if arg1 = 0 then arg2 else arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xffffffffffffffff]
 *   arg3: [0x0 ~> 0xffffffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffffffffffff]
 */
static void fiat_poly1305_cmovznz_u64(uint64_t* out1, fiat_poly1305_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  fiat_poly1305_uint1 x1 = (!(!arg1));
  uint64_t x2 = ((fiat_poly1305_int1)(0x0 - x1) & UINT64_C(0xffffffffffffffff));
  uint64_t x3 = ((x2 & arg3) | ((~x2) & arg2));
  *out1 = x3;
}

/*
 * The function fiat_poly1305_carry_mul multiplies two field elements and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x34cccccccccb], [0x0 ~> 0x1a6666666664], [0x0 ~> 0x1a6666666664]]
 *   arg2: [[0x0 ~> 0x34cccccccccb], [0x0 ~> 0x1a6666666664], [0x0 ~> 0x1a6666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 */
static void fiat_poly1305_carry_mul(uint64_t out1[3], const uint64_t arg1[3], const uint64_t arg2[3]) {
  fiat_poly1305_uint128 x1 = ((fiat_poly1305_uint128)(arg1[2]) * ((arg2[2]) * 0x5));
  fiat_poly1305_uint128 x2 = ((fiat_poly1305_uint128)(arg1[2]) * ((arg2[1]) * 0xa));
  fiat_poly1305_uint128 x3 = ((fiat_poly1305_uint128)(arg1[1]) * ((arg2[2]) * 0xa));
  fiat_poly1305_uint128 x4 = ((fiat_poly1305_uint128)(arg1[2]) * (arg2[0]));
  fiat_poly1305_uint128 x5 = ((fiat_poly1305_uint128)(arg1[1]) * ((arg2[1]) * 0x2));
  fiat_poly1305_uint128 x6 = ((fiat_poly1305_uint128)(arg1[1]) * (arg2[0]));
  fiat_poly1305_uint128 x7 = ((fiat_poly1305_uint128)(arg1[0]) * (arg2[2]));
  fiat_poly1305_uint128 x8 = ((fiat_poly1305_uint128)(arg1[0]) * (arg2[1]));
  fiat_poly1305_uint128 x9 = ((fiat_poly1305_uint128)(arg1[0]) * (arg2[0]));
  fiat_poly1305_uint128 x10 = (x9 + (x3 + x2));
  uint64_t x11 = (uint64_t)(x10 >> 44);
  uint64_t x12 = (uint64_t)(x10 & UINT64_C(0xfffffffffff));
  fiat_poly1305_uint128 x13 = (x7 + (x5 + x4));
  fiat_poly1305_uint128 x14 = (x8 + (x6 + x1));
  fiat_poly1305_uint128 x15 = (x11 + x14);
  uint64_t x16 = (uint64_t)(x15 >> 43);
  uint64_t x17 = (uint64_t)(x15 & UINT64_C(0x7ffffffffff));
  fiat_poly1305_uint128 x18 = (x16 + x13);
  uint64_t x19 = (uint64_t)(x18 >> 43);
  uint64_t x20 = (uint64_t)(x18 & UINT64_C(0x7ffffffffff));
  uint64_t x21 = (x19 * 0x5);
  uint64_t x22 = (x12 + x21);
  uint64_t x23 = (x22 >> 44);
  uint64_t x24 = (x22 & UINT64_C(0xfffffffffff));
  uint64_t x25 = (x23 + x17);
  fiat_poly1305_uint1 x26 = (fiat_poly1305_uint1)(x25 >> 43);
  uint64_t x27 = (x25 & UINT64_C(0x7ffffffffff));
  uint64_t x28 = (x26 + x20);
  out1[0] = x24;
  out1[1] = x27;
  out1[2] = x28;
}

/*
 * The function fiat_poly1305_carry_square squares a field element and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg1) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x34cccccccccb], [0x0 ~> 0x1a6666666664], [0x0 ~> 0x1a6666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 */
static void fiat_poly1305_carry_square(uint64_t out1[3], const uint64_t arg1[3]) {
  uint64_t x1 = ((arg1[2]) * 0x5);
  uint64_t x2 = (x1 * 0x2);
  uint64_t x3 = ((arg1[2]) * 0x2);
  uint64_t x4 = ((arg1[1]) * 0x2);
  fiat_poly1305_uint128 x5 = ((fiat_poly1305_uint128)(arg1[2]) * x1);
  fiat_poly1305_uint128 x6 = ((fiat_poly1305_uint128)(arg1[1]) * (x2 * 0x2));
  fiat_poly1305_uint128 x7 = ((fiat_poly1305_uint128)(arg1[1]) * ((arg1[1]) * 0x2));
  fiat_poly1305_uint128 x8 = ((fiat_poly1305_uint128)(arg1[0]) * x3);
  fiat_poly1305_uint128 x9 = ((fiat_poly1305_uint128)(arg1[0]) * x4);
  fiat_poly1305_uint128 x10 = ((fiat_poly1305_uint128)(arg1[0]) * (arg1[0]));
  fiat_poly1305_uint128 x11 = (x10 + x6);
  uint64_t x12 = (uint64_t)(x11 >> 44);
  uint64_t x13 = (uint64_t)(x11 & UINT64_C(0xfffffffffff));
  fiat_poly1305_uint128 x14 = (x8 + x7);
  fiat_poly1305_uint128 x15 = (x9 + x5);
  fiat_poly1305_uint128 x16 = (x12 + x15);
  uint64_t x17 = (uint64_t)(x16 >> 43);
  uint64_t x18 = (uint64_t)(x16 & UINT64_C(0x7ffffffffff));
  fiat_poly1305_uint128 x19 = (x17 + x14);
  uint64_t x20 = (uint64_t)(x19 >> 43);
  uint64_t x21 = (uint64_t)(x19 & UINT64_C(0x7ffffffffff));
  uint64_t x22 = (x20 * 0x5);
  uint64_t x23 = (x13 + x22);
  uint64_t x24 = (x23 >> 44);
  uint64_t x25 = (x23 & UINT64_C(0xfffffffffff));
  uint64_t x26 = (x24 + x18);
  fiat_poly1305_uint1 x27 = (fiat_poly1305_uint1)(x26 >> 43);
  uint64_t x28 = (x26 & UINT64_C(0x7ffffffffff));
  uint64_t x29 = (x27 + x21);
  out1[0] = x25;
  out1[1] = x28;
  out1[2] = x29;
}

/*
 * The function fiat_poly1305_carry reduces a field element.
 * Postconditions:
 *   eval out1 mod m = eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x34cccccccccb], [0x0 ~> 0x1a6666666664], [0x0 ~> 0x1a6666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 */
static void fiat_poly1305_carry(uint64_t out1[3], const uint64_t arg1[3]) {
  uint64_t x1 = (arg1[0]);
  uint64_t x2 = ((x1 >> 44) + (arg1[1]));
  uint64_t x3 = ((x2 >> 43) + (arg1[2]));
  uint64_t x4 = ((x1 & UINT64_C(0xfffffffffff)) + ((x3 >> 43) * 0x5));
  uint64_t x5 = ((fiat_poly1305_uint1)(x4 >> 44) + (x2 & UINT64_C(0x7ffffffffff)));
  uint64_t x6 = (x4 & UINT64_C(0xfffffffffff));
  uint64_t x7 = (x5 & UINT64_C(0x7ffffffffff));
  uint64_t x8 = ((fiat_poly1305_uint1)(x5 >> 43) + (x3 & UINT64_C(0x7ffffffffff)));
  out1[0] = x6;
  out1[1] = x7;
  out1[2] = x8;
}

/*
 * The function fiat_poly1305_add adds two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 + eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 *   arg2: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x34cccccccccb], [0x0 ~> 0x1a6666666664], [0x0 ~> 0x1a6666666664]]
 */
static void fiat_poly1305_add(uint64_t out1[3], const uint64_t arg1[3], const uint64_t arg2[3]) {
  uint64_t x1 = ((arg1[0]) + (arg2[0]));
  uint64_t x2 = ((arg1[1]) + (arg2[1]));
  uint64_t x3 = ((arg1[2]) + (arg2[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/*
 * The function fiat_poly1305_sub subtracts two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 - eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 *   arg2: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x34cccccccccb], [0x0 ~> 0x1a6666666664], [0x0 ~> 0x1a6666666664]]
 */
static void fiat_poly1305_sub(uint64_t out1[3], const uint64_t arg1[3], const uint64_t arg2[3]) {
  uint64_t x1 = ((UINT64_C(0x1ffffffffff6) + (arg1[0])) - (arg2[0]));
  uint64_t x2 = ((UINT64_C(0xffffffffffe) + (arg1[1])) - (arg2[1]));
  uint64_t x3 = ((UINT64_C(0xffffffffffe) + (arg1[2])) - (arg2[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/*
 * The function fiat_poly1305_opp negates a field element.
 * Postconditions:
 *   eval out1 mod m = -eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x34cccccccccb], [0x0 ~> 0x1a6666666664], [0x0 ~> 0x1a6666666664]]
 */
static void fiat_poly1305_opp(uint64_t out1[3], const uint64_t arg1[3]) {
  uint64_t x1 = (UINT64_C(0x1ffffffffff6) - (arg1[0]));
  uint64_t x2 = (UINT64_C(0xffffffffffe) - (arg1[1]));
  uint64_t x3 = (UINT64_C(0xffffffffffe) - (arg1[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/*
 * The function fiat_poly1305_selectznz is a multi-limb conditional select.
 * Postconditions:
 *   eval out1 = (if arg1 = 0 then eval arg2 else eval arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
static void fiat_poly1305_selectznz(uint64_t out1[3], fiat_poly1305_uint1 arg1, const uint64_t arg2[3], const uint64_t arg3[3]) {
  uint64_t x1;
  fiat_poly1305_cmovznz_u64(&x1, arg1, (arg2[0]), (arg3[0]));
  uint64_t x2;
  fiat_poly1305_cmovznz_u64(&x2, arg1, (arg2[1]), (arg3[1]));
  uint64_t x3;
  fiat_poly1305_cmovznz_u64(&x3, arg1, (arg2[2]), (arg3[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/*
 * The function fiat_poly1305_to_bytes serializes a field element to bytes in little-endian order.
 * Postconditions:
 *   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..16]
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 */
static void fiat_poly1305_to_bytes(uint8_t out1[17], const uint64_t arg1[3]) {
  uint64_t x1;
  fiat_poly1305_uint1 x2;
  fiat_poly1305_subborrowx_u44(&x1, &x2, 0x0, (arg1[0]), UINT64_C(0xffffffffffb));
  uint64_t x3;
  fiat_poly1305_uint1 x4;
  fiat_poly1305_subborrowx_u43(&x3, &x4, x2, (arg1[1]), UINT64_C(0x7ffffffffff));
  uint64_t x5;
  fiat_poly1305_uint1 x6;
  fiat_poly1305_subborrowx_u43(&x5, &x6, x4, (arg1[2]), UINT64_C(0x7ffffffffff));
  uint64_t x7;
  fiat_poly1305_cmovznz_u64(&x7, x6, 0x0, UINT64_C(0xffffffffffffffff));
  uint64_t x8;
  fiat_poly1305_uint1 x9;
  fiat_poly1305_addcarryx_u44(&x8, &x9, 0x0, x1, (x7 & UINT64_C(0xffffffffffb)));
  uint64_t x10;
  fiat_poly1305_uint1 x11;
  fiat_poly1305_addcarryx_u43(&x10, &x11, x9, x3, (x7 & UINT64_C(0x7ffffffffff)));
  uint64_t x12;
  fiat_poly1305_uint1 x13;
  fiat_poly1305_addcarryx_u43(&x12, &x13, x11, x5, (x7 & UINT64_C(0x7ffffffffff)));
  uint64_t x14 = (x12 << 7);
  uint64_t x15 = (x10 << 4);
  uint64_t x16 = (x8 >> 8);
  uint8_t x17 = (uint8_t)(x8 & UINT8_C(0xff));
  uint64_t x18 = (x16 >> 8);
  uint8_t x19 = (uint8_t)(x16 & UINT8_C(0xff));
  uint64_t x20 = (x18 >> 8);
  uint8_t x21 = (uint8_t)(x18 & UINT8_C(0xff));
  uint64_t x22 = (x20 >> 8);
  uint8_t x23 = (uint8_t)(x20 & UINT8_C(0xff));
  uint8_t x24 = (uint8_t)(x22 >> 8);
  uint8_t x25 = (uint8_t)(x22 & UINT8_C(0xff));
  uint64_t x26 = (x24 + x15);
  uint64_t x27 = (x26 >> 8);
  uint8_t x28 = (uint8_t)(x26 & UINT8_C(0xff));
  uint64_t x29 = (x27 >> 8);
  uint8_t x30 = (uint8_t)(x27 & UINT8_C(0xff));
  uint64_t x31 = (x29 >> 8);
  uint8_t x32 = (uint8_t)(x29 & UINT8_C(0xff));
  uint64_t x33 = (x31 >> 8);
  uint8_t x34 = (uint8_t)(x31 & UINT8_C(0xff));
  uint8_t x35 = (uint8_t)(x33 >> 8);
  uint8_t x36 = (uint8_t)(x33 & UINT8_C(0xff));
  uint64_t x37 = (x35 + x14);
  uint64_t x38 = (x37 >> 8);
  uint8_t x39 = (uint8_t)(x37 & UINT8_C(0xff));
  uint64_t x40 = (x38 >> 8);
  uint8_t x41 = (uint8_t)(x38 & UINT8_C(0xff));
  uint64_t x42 = (x40 >> 8);
  uint8_t x43 = (uint8_t)(x40 & UINT8_C(0xff));
  uint64_t x44 = (x42 >> 8);
  uint8_t x45 = (uint8_t)(x42 & UINT8_C(0xff));
  uint64_t x46 = (x44 >> 8);
  uint8_t x47 = (uint8_t)(x44 & UINT8_C(0xff));
  uint8_t x48 = (uint8_t)(x46 >> 8);
  uint8_t x49 = (uint8_t)(x46 & UINT8_C(0xff));
  out1[0] = x17;
  out1[1] = x19;
  out1[2] = x21;
  out1[3] = x23;
  out1[4] = x25;
  out1[5] = x28;
  out1[6] = x30;
  out1[7] = x32;
  out1[8] = x34;
  out1[9] = x36;
  out1[10] = x39;
  out1[11] = x41;
  out1[12] = x43;
  out1[13] = x45;
  out1[14] = x47;
  out1[15] = x49;
  out1[16] = x48;
}

/*
 * The function fiat_poly1305_from_bytes deserializes a field element from bytes in little-endian order.
 * Postconditions:
 *   eval out1 mod m = bytes_eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x119999999999], [0x0 ~> 0x8cccccccccc], [0x0 ~> 0x8cccccccccc]]
 */
static void fiat_poly1305_from_bytes(uint64_t out1[3], const uint8_t arg1[17]) {
  uint64_t x1 = ((uint64_t)(arg1[16]) << 41);
  uint64_t x2 = ((uint64_t)(arg1[15]) << 33);
  uint64_t x3 = ((uint64_t)(arg1[14]) << 25);
  uint64_t x4 = ((uint64_t)(arg1[13]) << 17);
  uint64_t x5 = ((uint64_t)(arg1[12]) << 9);
  uint64_t x6 = ((uint64_t)(arg1[11]) * 0x2);
  uint64_t x7 = ((uint64_t)(arg1[10]) << 36);
  uint64_t x8 = ((uint64_t)(arg1[9]) << 28);
  uint64_t x9 = ((uint64_t)(arg1[8]) << 20);
  uint64_t x10 = ((uint64_t)(arg1[7]) << 12);
  uint64_t x11 = ((uint64_t)(arg1[6]) << 4);
  uint64_t x12 = ((uint64_t)(arg1[5]) << 40);
  uint64_t x13 = ((uint64_t)(arg1[4]) << 32);
  uint64_t x14 = ((uint64_t)(arg1[3]) << 24);
  uint64_t x15 = ((uint64_t)(arg1[2]) << 16);
  uint64_t x16 = ((uint64_t)(arg1[1]) << 8);
  uint8_t x17 = (arg1[0]);
  uint64_t x18 = (x17 + (x16 + (x15 + (x14 + (x13 + x12)))));
  uint8_t x19 = (uint8_t)(x18 >> 44);
  uint64_t x20 = (x18 & UINT64_C(0xfffffffffff));
  uint64_t x21 = (x6 + (x5 + (x4 + (x3 + (x2 + x1)))));
  uint64_t x22 = (x11 + (x10 + (x9 + (x8 + x7))));
  uint64_t x23 = (x19 + x22);
  fiat_poly1305_uint1 x24 = (fiat_poly1305_uint1)(x23 >> 43);
  uint64_t x25 = (x23 & UINT64_C(0x7ffffffffff));
  uint64_t x26 = (x24 + x21);
  out1[0] = x20;
  out1[1] = x25;
  out1[2] = x26;
}
