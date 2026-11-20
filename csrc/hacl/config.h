/* Hand-written equivalent of the file produced by HACL*'s ./configure for x86-64 Linux/gcc,
   with the SIMD (VEC128/VEC256) variants deliberately disabled (portable C + Vale asm only). */
#define TARGET_ARCHITECTURE TARGET_ARCHITECTURE_ID_X64
#define HACL_CAN_COMPILE_INTRINSICS 1
#define HACL_CAN_COMPILE_VALE 1
#define HACL_CAN_COMPILE_INLINE_ASM 1
#define HACL_CAN_COMPILE_UINT128 1
