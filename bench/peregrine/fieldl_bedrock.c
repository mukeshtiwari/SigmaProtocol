// Generated from Bedrock code. Avoid editing directly.
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;

static_assert(sizeof(br_word_t) == sizeof(br_signed_t), "signed size");
static_assert(UINTPTR_MAX <= BR_WORD_MAX, "pointer fits in int");
static_assert(~(br_signed_t)0 == -(br_signed_t)1, "two's complement");

#if __STDC_VERSION__ >= 202311L && __has_include(<stdbit.h>)
  #include <stdbit.h>
  static_assert(__STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__, "little-endian");
#elif defined(__GNUC__) && defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "little-endian");
#elif defined(_MSC_VER) && !defined(__clang__) &&                              \
    (defined(_M_IX86) || defined(_M_X64) || defined(_M_ARM) || defined(_M_ARM64))
  // these MSVC targets are little-endian
#else
  #error "failed to confirm that target is little-endian"
#endif

// "An object shall have its stored value accessed only ... a character type."
static inline br_word_t _br_load1(br_word_t a) {
  return *((uint8_t *)a);
}

static inline br_word_t _br_load2(br_word_t a) {
  uint16_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load4(br_word_t a) {
  uint32_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load(br_word_t a) {
  br_word_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline void _br_store1(br_word_t a, uint8_t v) {
  *((uint8_t *)a) = v;
}

static inline void _br_store2(br_word_t a, uint16_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store4(br_word_t a, uint32_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store(br_word_t a, br_word_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if BR_WORD_MAX == UINT32_MAX
	  return ((uint64_t)a * b) >> 32;
  #elif BR_WORD_MAX == UINT64_MAX && (defined(__GNUC__) || defined(__clang__))
    return ((unsigned __int128)a * b) >> 64;
  #elif defined(_M_X64)
    uint64_t hi;
    _umul128(a, b, &hi);
    return hi;
  #elif defined(_M_ARM64)
    return __umulh(a, b);
  #else
    // See full_mul.v
    br_word_t hh, lh, hl, low, second_halfword_w_oflow, n, ll, M;
    n = ((((0u-(br_word_t)0x1)>>27)&0x3f)+0x1)>>1;
    M = ((br_word_t)0x1<<n)-0x1;
    ll = (a&M)*(b&M);
    lh = (a&M)*(b>>n);
    hl = (a>>n)*(b&M);
    hh = (a>>n)*(b>>n);
    second_halfword_w_oflow = ((ll>>n)+(lh&M))+(hl&M);
    return ((hh+(lh>>n))+(hl>>n))+(second_halfword_w_oflow>>n);
  #endif
}

static inline br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}

static void zl_add_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b);
static void zl_sub_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b);
static void zl_opp_bytes(br_word_t p_out, br_word_t p_a);
static void fl_mul(br_word_t out0, br_word_t in0, br_word_t in1);
static void fl_add(br_word_t out0, br_word_t in0, br_word_t in1);
static void fl_sub(br_word_t out0, br_word_t in0, br_word_t in1);
static void fl_opp(br_word_t out0, br_word_t in0);
static void fl_to_mont(br_word_t out0, br_word_t in0);
static void fl_from_bytes(br_word_t out0, br_word_t in0);
static void fl_to_bytes(br_word_t out0, br_word_t in0);

void zl_mul_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b) {
  br_word_t p_y, p_x, p_ym, p_o;
  uint8_t _br_stackalloc_p_x[32] = {0}; p_x = (br_word_t)&_br_stackalloc_p_x;
  uint8_t _br_stackalloc_p_y[32] = {0}; p_y = (br_word_t)&_br_stackalloc_p_y;
  uint8_t _br_stackalloc_p_ym[32] = {0}; p_ym = (br_word_t)&_br_stackalloc_p_ym;
  uint8_t _br_stackalloc_p_o[32] = {0}; p_o = (br_word_t)&_br_stackalloc_p_o;
  fl_from_bytes(p_x, p_a);
  fl_from_bytes(p_y, p_b);
  fl_to_mont(p_ym, p_y);
  fl_mul(p_o, p_x, p_ym);
  fl_to_bytes(p_out, p_o);
}

static void zl_add_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b) {
  br_word_t p_x, p_y, p_o;
  uint8_t _br_stackalloc_p_x[32] = {0}; p_x = (br_word_t)&_br_stackalloc_p_x;
  uint8_t _br_stackalloc_p_y[32] = {0}; p_y = (br_word_t)&_br_stackalloc_p_y;
  uint8_t _br_stackalloc_p_o[32] = {0}; p_o = (br_word_t)&_br_stackalloc_p_o;
  fl_from_bytes(p_x, p_a);
  fl_from_bytes(p_y, p_b);
  fl_add(p_o, p_x, p_y);
  fl_to_bytes(p_out, p_o);
}

static void zl_sub_bytes(br_word_t p_out, br_word_t p_a, br_word_t p_b) {
  br_word_t p_x, p_y, p_o;
  uint8_t _br_stackalloc_p_x[32] = {0}; p_x = (br_word_t)&_br_stackalloc_p_x;
  uint8_t _br_stackalloc_p_y[32] = {0}; p_y = (br_word_t)&_br_stackalloc_p_y;
  uint8_t _br_stackalloc_p_o[32] = {0}; p_o = (br_word_t)&_br_stackalloc_p_o;
  fl_from_bytes(p_x, p_a);
  fl_from_bytes(p_y, p_b);
  fl_sub(p_o, p_x, p_y);
  fl_to_bytes(p_out, p_o);
}

static void zl_opp_bytes(br_word_t p_out, br_word_t p_a) {
  br_word_t p_x, p_o;
  uint8_t _br_stackalloc_p_x[32] = {0}; p_x = (br_word_t)&_br_stackalloc_p_x;
  uint8_t _br_stackalloc_p_o[32] = {0}; p_o = (br_word_t)&_br_stackalloc_p_o;
  fl_from_bytes(p_x, p_a);
  fl_opp(p_o, p_x);
  fl_to_bytes(p_out, p_o);
}

static void fl_mul(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x1, x2, x3, x0, x11, x16, x19, x21, x17, x22, x14, x23, x25, x26, x15, x27, x12, x28, x30, x31, x13, x33, x36, x39, x41, x37, x38, x43, x18, x44, x20, x45, x40, x46, x48, x49, x24, x50, x42, x51, x53, x54, x29, x55, x34, x56, x58, x59, x32, x60, x35, x61, x63, x8, x69, x72, x74, x70, x75, x67, x76, x78, x79, x68, x80, x65, x81, x83, x84, x66, x71, x47, x87, x52, x88, x73, x89, x91, x92, x57, x93, x77, x94, x96, x97, x62, x98, x82, x99, x101, x102, x64, x103, x85, x104, x106, x108, x111, x114, x116, x112, x113, x118, x86, x119, x90, x120, x115, x121, x123, x124, x95, x125, x117, x126, x128, x129, x100, x130, x109, x131, x133, x134, x105, x135, x110, x136, x138, x139, x107, x9, x145, x148, x150, x146, x151, x143, x152, x154, x155, x144, x156, x141, x157, x159, x160, x142, x147, x122, x163, x127, x164, x149, x165, x167, x168, x132, x169, x153, x170, x172, x173, x137, x174, x158, x175, x177, x178, x140, x179, x161, x180, x182, x184, x187, x190, x192, x188, x189, x194, x162, x195, x166, x196, x191, x197, x199, x200, x171, x201, x193, x202, x204, x205, x176, x206, x185, x207, x209, x210, x181, x211, x186, x212, x214, x215, x183, x7, x6, x5, x10, x4, x221, x224, x226, x222, x227, x219, x228, x230, x231, x220, x232, x217, x233, x235, x236, x218, x223, x198, x239, x203, x240, x225, x241, x243, x244, x208, x245, x229, x246, x248, x249, x213, x250, x234, x251, x253, x254, x216, x255, x237, x256, x258, x260, x263, x266, x268, x264, x265, x270, x238, x271, x242, x272, x267, x273, x275, x276, x247, x277, x269, x278, x280, x281, x252, x282, x261, x283, x285, x286, x257, x287, x262, x288, x290, x291, x259, x294, x295, x296, x298, x299, x301, x302, x303, x305, x306, x292, x307, x274, x309, x293, x310, x279, x312, x297, x313, x284, x315, x300, x316, x308, x289, x318, x304, x319, x311, x314, x317, x320, x321, x322, x323, x324;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  x4 = _br_load(in1+0);
  x5 = _br_load(in1+8);
  x6 = _br_load(in1+16);
  x7 = _br_load(in1+24);
  /*skip*/
  /*skip*/
  x8 = x1;
  x9 = x2;
  x10 = x3;
  x11 = x0;
  x12 = x11*x7;
  x13 = _br_mulhuu(x11, x7);
  x14 = x11*x6;
  x15 = _br_mulhuu(x11, x6);
  x16 = x11*x5;
  x17 = _br_mulhuu(x11, x5);
  x18 = x11*x4;
  x19 = _br_mulhuu(x11, x4);
  x20 = x19+x16;
  x21 = (br_word_t)(x20<x19);
  x22 = x21+x17;
  x23 = (br_word_t)(x22<x17);
  x24 = x22+x14;
  x25 = (br_word_t)(x24<x14);
  x26 = x23+x25;
  x27 = x26+x15;
  x28 = (br_word_t)(x27<x15);
  x29 = x27+x12;
  x30 = (br_word_t)(x29<x12);
  x31 = x28+x30;
  x32 = x31+x13;
  x33 = x18*0xd2b51da312547e1b;
  x34 = x33*0x1000000000000000;
  x35 = _br_mulhuu(x33, (br_word_t)0x1000000000000000);
  x36 = x33*0x14def9dea2f79cd6;
  x37 = _br_mulhuu(x33, (br_word_t)0x14def9dea2f79cd6);
  x38 = x33*0x5812631a5cf5d3ed;
  x39 = _br_mulhuu(x33, (br_word_t)0x5812631a5cf5d3ed);
  x40 = x39+x36;
  x41 = (br_word_t)(x40<x39);
  x42 = x41+x37;
  x43 = x18+x38;
  x44 = (br_word_t)(x43<x18);
  x45 = x44+x20;
  x46 = (br_word_t)(x45<x20);
  x47 = x45+x40;
  x48 = (br_word_t)(x47<x40);
  x49 = x46+x48;
  x50 = x49+x24;
  x51 = (br_word_t)(x50<x24);
  x52 = x50+x42;
  x53 = (br_word_t)(x52<x42);
  x54 = x51+x53;
  x55 = x54+x29;
  x56 = (br_word_t)(x55<x29);
  x57 = x55+x34;
  x58 = (br_word_t)(x57<x34);
  x59 = x56+x58;
  x60 = x59+x32;
  x61 = (br_word_t)(x60<x32);
  x62 = x60+x35;
  x63 = (br_word_t)(x62<x35);
  x64 = x61+x63;
  x65 = x8*x7;
  x66 = _br_mulhuu(x8, x7);
  x67 = x8*x6;
  x68 = _br_mulhuu(x8, x6);
  x69 = x8*x5;
  x70 = _br_mulhuu(x8, x5);
  x71 = x8*x4;
  x72 = _br_mulhuu(x8, x4);
  x73 = x72+x69;
  x74 = (br_word_t)(x73<x72);
  x75 = x74+x70;
  x76 = (br_word_t)(x75<x70);
  x77 = x75+x67;
  x78 = (br_word_t)(x77<x67);
  x79 = x76+x78;
  x80 = x79+x68;
  x81 = (br_word_t)(x80<x68);
  x82 = x80+x65;
  x83 = (br_word_t)(x82<x65);
  x84 = x81+x83;
  x85 = x84+x66;
  x86 = x47+x71;
  x87 = (br_word_t)(x86<x47);
  x88 = x87+x52;
  x89 = (br_word_t)(x88<x52);
  x90 = x88+x73;
  x91 = (br_word_t)(x90<x73);
  x92 = x89+x91;
  x93 = x92+x57;
  x94 = (br_word_t)(x93<x57);
  x95 = x93+x77;
  x96 = (br_word_t)(x95<x77);
  x97 = x94+x96;
  x98 = x97+x62;
  x99 = (br_word_t)(x98<x62);
  x100 = x98+x82;
  x101 = (br_word_t)(x100<x82);
  x102 = x99+x101;
  x103 = x102+x64;
  x104 = (br_word_t)(x103<x64);
  x105 = x103+x85;
  x106 = (br_word_t)(x105<x85);
  x107 = x104+x106;
  x108 = x86*0xd2b51da312547e1b;
  x109 = x108*0x1000000000000000;
  x110 = _br_mulhuu(x108, (br_word_t)0x1000000000000000);
  x111 = x108*0x14def9dea2f79cd6;
  x112 = _br_mulhuu(x108, (br_word_t)0x14def9dea2f79cd6);
  x113 = x108*0x5812631a5cf5d3ed;
  x114 = _br_mulhuu(x108, (br_word_t)0x5812631a5cf5d3ed);
  x115 = x114+x111;
  x116 = (br_word_t)(x115<x114);
  x117 = x116+x112;
  x118 = x86+x113;
  x119 = (br_word_t)(x118<x86);
  x120 = x119+x90;
  x121 = (br_word_t)(x120<x90);
  x122 = x120+x115;
  x123 = (br_word_t)(x122<x115);
  x124 = x121+x123;
  x125 = x124+x95;
  x126 = (br_word_t)(x125<x95);
  x127 = x125+x117;
  x128 = (br_word_t)(x127<x117);
  x129 = x126+x128;
  x130 = x129+x100;
  x131 = (br_word_t)(x130<x100);
  x132 = x130+x109;
  x133 = (br_word_t)(x132<x109);
  x134 = x131+x133;
  x135 = x134+x105;
  x136 = (br_word_t)(x135<x105);
  x137 = x135+x110;
  x138 = (br_word_t)(x137<x110);
  x139 = x136+x138;
  x140 = x139+x107;
  x141 = x9*x7;
  x142 = _br_mulhuu(x9, x7);
  x143 = x9*x6;
  x144 = _br_mulhuu(x9, x6);
  x145 = x9*x5;
  x146 = _br_mulhuu(x9, x5);
  x147 = x9*x4;
  x148 = _br_mulhuu(x9, x4);
  x149 = x148+x145;
  x150 = (br_word_t)(x149<x148);
  x151 = x150+x146;
  x152 = (br_word_t)(x151<x146);
  x153 = x151+x143;
  x154 = (br_word_t)(x153<x143);
  x155 = x152+x154;
  x156 = x155+x144;
  x157 = (br_word_t)(x156<x144);
  x158 = x156+x141;
  x159 = (br_word_t)(x158<x141);
  x160 = x157+x159;
  x161 = x160+x142;
  x162 = x122+x147;
  x163 = (br_word_t)(x162<x122);
  x164 = x163+x127;
  x165 = (br_word_t)(x164<x127);
  x166 = x164+x149;
  x167 = (br_word_t)(x166<x149);
  x168 = x165+x167;
  x169 = x168+x132;
  x170 = (br_word_t)(x169<x132);
  x171 = x169+x153;
  x172 = (br_word_t)(x171<x153);
  x173 = x170+x172;
  x174 = x173+x137;
  x175 = (br_word_t)(x174<x137);
  x176 = x174+x158;
  x177 = (br_word_t)(x176<x158);
  x178 = x175+x177;
  x179 = x178+x140;
  x180 = (br_word_t)(x179<x140);
  x181 = x179+x161;
  x182 = (br_word_t)(x181<x161);
  x183 = x180+x182;
  x184 = x162*0xd2b51da312547e1b;
  x185 = x184*0x1000000000000000;
  x186 = _br_mulhuu(x184, (br_word_t)0x1000000000000000);
  x187 = x184*0x14def9dea2f79cd6;
  x188 = _br_mulhuu(x184, (br_word_t)0x14def9dea2f79cd6);
  x189 = x184*0x5812631a5cf5d3ed;
  x190 = _br_mulhuu(x184, (br_word_t)0x5812631a5cf5d3ed);
  x191 = x190+x187;
  x192 = (br_word_t)(x191<x190);
  x193 = x192+x188;
  x194 = x162+x189;
  x195 = (br_word_t)(x194<x162);
  x196 = x195+x166;
  x197 = (br_word_t)(x196<x166);
  x198 = x196+x191;
  x199 = (br_word_t)(x198<x191);
  x200 = x197+x199;
  x201 = x200+x171;
  x202 = (br_word_t)(x201<x171);
  x203 = x201+x193;
  x204 = (br_word_t)(x203<x193);
  x205 = x202+x204;
  x206 = x205+x176;
  x207 = (br_word_t)(x206<x176);
  x208 = x206+x185;
  x209 = (br_word_t)(x208<x185);
  x210 = x207+x209;
  x211 = x210+x181;
  x212 = (br_word_t)(x211<x181);
  x213 = x211+x186;
  x214 = (br_word_t)(x213<x186);
  x215 = x212+x214;
  x216 = x215+x183;
  x217 = x10*x7;
  x218 = _br_mulhuu(x10, x7);
  x219 = x10*x6;
  x220 = _br_mulhuu(x10, x6);
  x221 = x10*x5;
  x222 = _br_mulhuu(x10, x5);
  x223 = x10*x4;
  x224 = _br_mulhuu(x10, x4);
  x225 = x224+x221;
  x226 = (br_word_t)(x225<x224);
  x227 = x226+x222;
  x228 = (br_word_t)(x227<x222);
  x229 = x227+x219;
  x230 = (br_word_t)(x229<x219);
  x231 = x228+x230;
  x232 = x231+x220;
  x233 = (br_word_t)(x232<x220);
  x234 = x232+x217;
  x235 = (br_word_t)(x234<x217);
  x236 = x233+x235;
  x237 = x236+x218;
  x238 = x198+x223;
  x239 = (br_word_t)(x238<x198);
  x240 = x239+x203;
  x241 = (br_word_t)(x240<x203);
  x242 = x240+x225;
  x243 = (br_word_t)(x242<x225);
  x244 = x241+x243;
  x245 = x244+x208;
  x246 = (br_word_t)(x245<x208);
  x247 = x245+x229;
  x248 = (br_word_t)(x247<x229);
  x249 = x246+x248;
  x250 = x249+x213;
  x251 = (br_word_t)(x250<x213);
  x252 = x250+x234;
  x253 = (br_word_t)(x252<x234);
  x254 = x251+x253;
  x255 = x254+x216;
  x256 = (br_word_t)(x255<x216);
  x257 = x255+x237;
  x258 = (br_word_t)(x257<x237);
  x259 = x256+x258;
  x260 = x238*0xd2b51da312547e1b;
  x261 = x260*0x1000000000000000;
  x262 = _br_mulhuu(x260, (br_word_t)0x1000000000000000);
  x263 = x260*0x14def9dea2f79cd6;
  x264 = _br_mulhuu(x260, (br_word_t)0x14def9dea2f79cd6);
  x265 = x260*0x5812631a5cf5d3ed;
  x266 = _br_mulhuu(x260, (br_word_t)0x5812631a5cf5d3ed);
  x267 = x266+x263;
  x268 = (br_word_t)(x267<x266);
  x269 = x268+x264;
  x270 = x238+x265;
  x271 = (br_word_t)(x270<x238);
  x272 = x271+x242;
  x273 = (br_word_t)(x272<x242);
  x274 = x272+x267;
  x275 = (br_word_t)(x274<x267);
  x276 = x273+x275;
  x277 = x276+x247;
  x278 = (br_word_t)(x277<x247);
  x279 = x277+x269;
  x280 = (br_word_t)(x279<x269);
  x281 = x278+x280;
  x282 = x281+x252;
  x283 = (br_word_t)(x282<x252);
  x284 = x282+x261;
  x285 = (br_word_t)(x284<x261);
  x286 = x283+x285;
  x287 = x286+x257;
  x288 = (br_word_t)(x287<x257);
  x289 = x287+x262;
  x290 = (br_word_t)(x289<x262);
  x291 = x288+x290;
  x292 = x291+x259;
  x293 = x274-0x5812631a5cf5d3ed;
  x294 = (br_word_t)(x274<x293);
  x295 = x279-0x14def9dea2f79cd6;
  x296 = (br_word_t)(x279<x295);
  x297 = x295-x294;
  x298 = (br_word_t)(x295<x297);
  x299 = x296+x298;
  x300 = x284-x299;
  x301 = (br_word_t)(x284<x300);
  x302 = x289-0x1000000000000000;
  x303 = (br_word_t)(x289<x302);
  x304 = x302-x301;
  x305 = (br_word_t)(x302<x304);
  x306 = x303+x305;
  x307 = x292-x306;
  x308 = (br_word_t)(x292<x307);
  x309 = (0u-(br_word_t)1)+((br_word_t)(x308==(br_word_t)0));
  x310 = x309^0xffffffffffffffff;
  x311 = (x274&x309)|(x293&x310);
  x312 = (0u-(br_word_t)1)+((br_word_t)(x308==(br_word_t)0));
  x313 = x312^0xffffffffffffffff;
  x314 = (x279&x312)|(x297&x313);
  x315 = (0u-(br_word_t)1)+((br_word_t)(x308==(br_word_t)0));
  x316 = x315^0xffffffffffffffff;
  x317 = (x284&x315)|(x300&x316);
  x318 = (0u-(br_word_t)1)+((br_word_t)(x308==(br_word_t)0));
  x319 = x318^0xffffffffffffffff;
  x320 = (x289&x318)|(x304&x319);
  x321 = x311;
  x322 = x314;
  x323 = x317;
  x324 = x320;
  /*skip*/
  _br_store(out0+0, x321);
  _br_store(out0+8, x322);
  _br_store(out0+16, x323);
  _br_store(out0+24, x324);
  /*skip*/
}

static void fl_add(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x4, x0, x9, x1, x5, x11, x2, x6, x13, x3, x7, x17, x15, x20, x8, x23, x16, x24, x10, x26, x18, x27, x12, x29, x19, x30, x22, x14, x32, x21, x33, x25, x28, x31, x34, x35, x36, x37, x38;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  x4 = _br_load(in1+0);
  x5 = _br_load(in1+8);
  x6 = _br_load(in1+16);
  x7 = _br_load(in1+24);
  /*skip*/
  /*skip*/
  x8 = x0+x4;
  x9 = ((br_word_t)(x8<x0))+x1;
  x10 = x9+x5;
  x11 = (((br_word_t)(x9<x1))+((br_word_t)(x10<x5)))+x2;
  x12 = x11+x6;
  x13 = (((br_word_t)(x11<x2))+((br_word_t)(x12<x6)))+x3;
  x14 = x13+x7;
  x15 = ((br_word_t)(x13<x3))+((br_word_t)(x14<x7));
  x16 = x8-0x5812631a5cf5d3ed;
  x17 = x10-0x14def9dea2f79cd6;
  x18 = x17-((br_word_t)(x8<x16));
  x19 = x12-(((br_word_t)(x10<x17))+((br_word_t)(x17<x18)));
  x20 = x14-0x1000000000000000;
  x21 = x20-((br_word_t)(x12<x19));
  x22 = (br_word_t)(x15<(x15-(((br_word_t)(x14<x20))+((br_word_t)(x20<x21)))));
  x23 = (0u-(br_word_t)1)+((br_word_t)(x22==(br_word_t)0));
  x24 = x23^0xffffffffffffffff;
  x25 = (x8&x23)|(x16&x24);
  x26 = (0u-(br_word_t)1)+((br_word_t)(x22==(br_word_t)0));
  x27 = x26^0xffffffffffffffff;
  x28 = (x10&x26)|(x18&x27);
  x29 = (0u-(br_word_t)1)+((br_word_t)(x22==(br_word_t)0));
  x30 = x29^0xffffffffffffffff;
  x31 = (x12&x29)|(x19&x30);
  x32 = (0u-(br_word_t)1)+((br_word_t)(x22==(br_word_t)0));
  x33 = x32^0xffffffffffffffff;
  x34 = (x14&x32)|(x21&x33);
  x35 = x25;
  x36 = x28;
  x37 = x31;
  x38 = x34;
  /*skip*/
  _br_store(out0+0, x35);
  _br_store(out0+8, x36);
  _br_store(out0+16, x37);
  _br_store(out0+24, x38);
  /*skip*/
}

static void fl_sub(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x4, x5, x0, x6, x1, x9, x7, x2, x11, x3, x13, x8, x17, x10, x12, x14, x15, x16, x18, x19, x20, x21, x22, x23, x24;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  x4 = _br_load(in1+0);
  x5 = _br_load(in1+8);
  x6 = _br_load(in1+16);
  x7 = _br_load(in1+24);
  /*skip*/
  /*skip*/
  x8 = x0-x4;
  x9 = x1-x5;
  x10 = x9-((br_word_t)(x0<x8));
  x11 = x2-x6;
  x12 = x11-(((br_word_t)(x1<x9))+((br_word_t)(x9<x10)));
  x13 = x3-x7;
  x14 = x13-(((br_word_t)(x2<x11))+((br_word_t)(x11<x12)));
  x15 = (0u-(br_word_t)1)+((br_word_t)((((br_word_t)(x3<x13))+((br_word_t)(x13<x14)))==(br_word_t)0));
  x16 = x8+(x15&0x5812631a5cf5d3ed);
  x17 = ((br_word_t)(x16<x8))+x10;
  x18 = x17+(x15&0x14def9dea2f79cd6);
  x19 = (((br_word_t)(x17<x10))+((br_word_t)(x18<(x15&0x14def9dea2f79cd6))))+x12;
  x20 = (((br_word_t)(x19<x12))+x14)+(x15&0x1000000000000000);
  x21 = x16;
  x22 = x18;
  x23 = x19;
  x24 = x20;
  /*skip*/
  _br_store(out0+0, x21);
  _br_store(out0+8, x22);
  _br_store(out0+16, x23);
  _br_store(out0+24, x24);
  /*skip*/
}

static void fl_opp(br_word_t out0, br_word_t in0) {
  br_word_t x0, x1, x2, x5, x3, x7, x9, x4, x13, x6, x8, x10, x11, x12, x14, x15, x16, x17, x18, x19, x20;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  /*skip*/
  x4 = (br_word_t)0-x0;
  x5 = (br_word_t)0-x1;
  x6 = x5-((br_word_t)((br_word_t)0<x4));
  x7 = (br_word_t)0-x2;
  x8 = x7-(((br_word_t)((br_word_t)0<x5))+((br_word_t)(x5<x6)));
  x9 = (br_word_t)0-x3;
  x10 = x9-(((br_word_t)((br_word_t)0<x7))+((br_word_t)(x7<x8)));
  x11 = (0u-(br_word_t)1)+((br_word_t)((((br_word_t)((br_word_t)0<x9))+((br_word_t)(x9<x10)))==(br_word_t)0));
  x12 = x4+(x11&0x5812631a5cf5d3ed);
  x13 = ((br_word_t)(x12<x4))+x6;
  x14 = x13+(x11&0x14def9dea2f79cd6);
  x15 = (((br_word_t)(x13<x6))+((br_word_t)(x14<(x11&0x14def9dea2f79cd6))))+x8;
  x16 = (((br_word_t)(x15<x8))+x10)+(x11&0x1000000000000000);
  x17 = x12;
  x18 = x14;
  x19 = x15;
  x20 = x16;
  /*skip*/
  _br_store(out0+0, x17);
  _br_store(out0+8, x18);
  _br_store(out0+16, x19);
  _br_store(out0+24, x20);
  /*skip*/
}

static void fl_to_mont(br_word_t out0, br_word_t in0) {
  br_word_t x1, x2, x3, x0, x7, x14, x16, x12, x10, x18, x11, x8, x25, x21, x13, x28, x15, x26, x30, x17, x27, x24, x32, x19, x22, x40, x42, x39, x37, x44, x38, x35, x4, x29, x48, x31, x41, x50, x33, x43, x52, x34, x20, x9, x23, x45, x59, x55, x47, x62, x49, x60, x64, x51, x61, x58, x66, x53, x56, x74, x76, x73, x71, x78, x72, x69, x5, x63, x82, x65, x75, x84, x67, x77, x86, x68, x54, x46, x36, x57, x79, x93, x89, x81, x96, x83, x94, x98, x85, x95, x92, x100, x87, x90, x107, x109, x106, x104, x97, x114, x99, x108, x116, x101, x110, x123, x113, x126, x115, x124, x128, x117, x125, x122, x130, x121, x118, x102, x88, x80, x70, x91, x119, x111, x105, x112, x103, x6, x120, x134, x137, x127, x140, x133, x141, x129, x143, x135, x144, x131, x146, x136, x147, x139, x132, x149, x138, x150, x142, x145, x148, x151, x152, x153, x154, x155;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  /*skip*/
  x4 = x1;
  x5 = x2;
  x6 = x3;
  x7 = x0;
  x8 = x7*0x399411b7c309a3d;
  x9 = _br_mulhuu(x7, (br_word_t)0x399411b7c309a3d);
  x10 = x7*0xceec73d217f5be65;
  x11 = _br_mulhuu(x7, (br_word_t)0xceec73d217f5be65);
  x12 = _br_mulhuu(x7, (br_word_t)0xd00e1ba768859347);
  x13 = x7*0xa40611e3449c0f01;
  x14 = _br_mulhuu(x7, (br_word_t)0xa40611e3449c0f01);
  x15 = x14+(x7*0xd00e1ba768859347);
  x16 = ((br_word_t)(x15<x14))+x12;
  x17 = x16+x10;
  x18 = (((br_word_t)(x16<x12))+((br_word_t)(x17<x10)))+x11;
  x19 = x18+x8;
  x20 = ((br_word_t)(x18<x11))+((br_word_t)(x19<x8));
  x21 = x13*0xd2b51da312547e1b;
  x22 = x21*0x1000000000000000;
  x23 = _br_mulhuu(x21, (br_word_t)0x1000000000000000);
  x24 = _br_mulhuu(x21, (br_word_t)0x14def9dea2f79cd6);
  x25 = _br_mulhuu(x21, (br_word_t)0x5812631a5cf5d3ed);
  x26 = x25+(x21*0x14def9dea2f79cd6);
  x27 = (br_word_t)(x26<x25);
  x28 = ((br_word_t)((x13+(x21*0x5812631a5cf5d3ed))<x13))+x15;
  x29 = x28+x26;
  x30 = (((br_word_t)(x28<x15))+((br_word_t)(x29<x26)))+x17;
  x31 = x30+(x27+x24);
  x32 = (((br_word_t)(x30<x17))+((br_word_t)(x31<(x27+x24))))+x19;
  x33 = x32+x22;
  x34 = ((br_word_t)(x32<x19))+((br_word_t)(x33<x22));
  x35 = x4*0x399411b7c309a3d;
  x36 = _br_mulhuu(x4, (br_word_t)0x399411b7c309a3d);
  x37 = x4*0xceec73d217f5be65;
  x38 = _br_mulhuu(x4, (br_word_t)0xceec73d217f5be65);
  x39 = _br_mulhuu(x4, (br_word_t)0xd00e1ba768859347);
  x40 = _br_mulhuu(x4, (br_word_t)0xa40611e3449c0f01);
  x41 = x40+(x4*0xd00e1ba768859347);
  x42 = ((br_word_t)(x41<x40))+x39;
  x43 = x42+x37;
  x44 = (((br_word_t)(x42<x39))+((br_word_t)(x43<x37)))+x38;
  x45 = x44+x35;
  x46 = ((br_word_t)(x44<x38))+((br_word_t)(x45<x35));
  x47 = x29+(x4*0xa40611e3449c0f01);
  x48 = ((br_word_t)(x47<x29))+x31;
  x49 = x48+x41;
  x50 = (((br_word_t)(x48<x31))+((br_word_t)(x49<x41)))+x33;
  x51 = x50+x43;
  x52 = (((br_word_t)(x50<x33))+((br_word_t)(x51<x43)))+((x34+(x20+x9))+x23);
  x53 = x52+x45;
  x54 = ((br_word_t)(x52<((x34+(x20+x9))+x23)))+((br_word_t)(x53<x45));
  x55 = x47*0xd2b51da312547e1b;
  x56 = x55*0x1000000000000000;
  x57 = _br_mulhuu(x55, (br_word_t)0x1000000000000000);
  x58 = _br_mulhuu(x55, (br_word_t)0x14def9dea2f79cd6);
  x59 = _br_mulhuu(x55, (br_word_t)0x5812631a5cf5d3ed);
  x60 = x59+(x55*0x14def9dea2f79cd6);
  x61 = (br_word_t)(x60<x59);
  x62 = ((br_word_t)((x47+(x55*0x5812631a5cf5d3ed))<x47))+x49;
  x63 = x62+x60;
  x64 = (((br_word_t)(x62<x49))+((br_word_t)(x63<x60)))+x51;
  x65 = x64+(x61+x58);
  x66 = (((br_word_t)(x64<x51))+((br_word_t)(x65<(x61+x58))))+x53;
  x67 = x66+x56;
  x68 = ((br_word_t)(x66<x53))+((br_word_t)(x67<x56));
  x69 = x5*0x399411b7c309a3d;
  x70 = _br_mulhuu(x5, (br_word_t)0x399411b7c309a3d);
  x71 = x5*0xceec73d217f5be65;
  x72 = _br_mulhuu(x5, (br_word_t)0xceec73d217f5be65);
  x73 = _br_mulhuu(x5, (br_word_t)0xd00e1ba768859347);
  x74 = _br_mulhuu(x5, (br_word_t)0xa40611e3449c0f01);
  x75 = x74+(x5*0xd00e1ba768859347);
  x76 = ((br_word_t)(x75<x74))+x73;
  x77 = x76+x71;
  x78 = (((br_word_t)(x76<x73))+((br_word_t)(x77<x71)))+x72;
  x79 = x78+x69;
  x80 = ((br_word_t)(x78<x72))+((br_word_t)(x79<x69));
  x81 = x63+(x5*0xa40611e3449c0f01);
  x82 = ((br_word_t)(x81<x63))+x65;
  x83 = x82+x75;
  x84 = (((br_word_t)(x82<x65))+((br_word_t)(x83<x75)))+x67;
  x85 = x84+x77;
  x86 = (((br_word_t)(x84<x67))+((br_word_t)(x85<x77)))+((x68+(x54+(x46+x36)))+x57);
  x87 = x86+x79;
  x88 = ((br_word_t)(x86<((x68+(x54+(x46+x36)))+x57)))+((br_word_t)(x87<x79));
  x89 = x81*0xd2b51da312547e1b;
  x90 = x89*0x1000000000000000;
  x91 = _br_mulhuu(x89, (br_word_t)0x1000000000000000);
  x92 = _br_mulhuu(x89, (br_word_t)0x14def9dea2f79cd6);
  x93 = _br_mulhuu(x89, (br_word_t)0x5812631a5cf5d3ed);
  x94 = x93+(x89*0x14def9dea2f79cd6);
  x95 = (br_word_t)(x94<x93);
  x96 = ((br_word_t)((x81+(x89*0x5812631a5cf5d3ed))<x81))+x83;
  x97 = x96+x94;
  x98 = (((br_word_t)(x96<x83))+((br_word_t)(x97<x94)))+x85;
  x99 = x98+(x95+x92);
  x100 = (((br_word_t)(x98<x85))+((br_word_t)(x99<(x95+x92))))+x87;
  x101 = x100+x90;
  x102 = ((br_word_t)(x100<x87))+((br_word_t)(x101<x90));
  x103 = x6*0x399411b7c309a3d;
  x104 = x6*0xceec73d217f5be65;
  x105 = _br_mulhuu(x6, (br_word_t)0xceec73d217f5be65);
  x106 = _br_mulhuu(x6, (br_word_t)0xd00e1ba768859347);
  x107 = _br_mulhuu(x6, (br_word_t)0xa40611e3449c0f01);
  x108 = x107+(x6*0xd00e1ba768859347);
  x109 = ((br_word_t)(x108<x107))+x106;
  x110 = x109+x104;
  x111 = (((br_word_t)(x109<x106))+((br_word_t)(x110<x104)))+x105;
  x112 = x111+x103;
  x113 = x97+(x6*0xa40611e3449c0f01);
  x114 = ((br_word_t)(x113<x97))+x99;
  x115 = x114+x108;
  x116 = (((br_word_t)(x114<x99))+((br_word_t)(x115<x108)))+x101;
  x117 = x116+x110;
  x118 = (((br_word_t)(x116<x101))+((br_word_t)(x117<x110)))+((x102+(x88+(x80+x70)))+x91);
  x119 = x118+x112;
  x120 = x113*0xd2b51da312547e1b;
  x121 = x120*0x1000000000000000;
  x122 = _br_mulhuu(x120, (br_word_t)0x14def9dea2f79cd6);
  x123 = _br_mulhuu(x120, (br_word_t)0x5812631a5cf5d3ed);
  x124 = x123+(x120*0x14def9dea2f79cd6);
  x125 = (br_word_t)(x124<x123);
  x126 = ((br_word_t)((x113+(x120*0x5812631a5cf5d3ed))<x113))+x115;
  x127 = x126+x124;
  x128 = (((br_word_t)(x126<x115))+((br_word_t)(x127<x124)))+x117;
  x129 = x128+(x125+x122);
  x130 = (((br_word_t)(x128<x117))+((br_word_t)(x129<(x125+x122))))+x119;
  x131 = x130+x121;
  x132 = ((((br_word_t)(x130<x119))+((br_word_t)(x131<x121)))+((((br_word_t)(x118<((x102+(x88+(x80+x70)))+x91)))+((br_word_t)(x119<x112)))+((((br_word_t)(x111<x105))+((br_word_t)(x112<x103)))+(_br_mulhuu(x6, (br_word_t)0x399411b7c309a3d)))))+(_br_mulhuu(x120, (br_word_t)0x1000000000000000));
  x133 = x127-0x5812631a5cf5d3ed;
  x134 = x129-0x14def9dea2f79cd6;
  x135 = x134-((br_word_t)(x127<x133));
  x136 = x131-(((br_word_t)(x129<x134))+((br_word_t)(x134<x135)));
  x137 = x132-0x1000000000000000;
  x138 = x137-((br_word_t)(x131<x136));
  x139 = (br_word_t)((br_word_t)0<((br_word_t)0-(((br_word_t)(x132<x137))+((br_word_t)(x137<x138)))));
  x140 = (0u-(br_word_t)1)+((br_word_t)(x139==(br_word_t)0));
  x141 = x140^0xffffffffffffffff;
  x142 = (x127&x140)|(x133&x141);
  x143 = (0u-(br_word_t)1)+((br_word_t)(x139==(br_word_t)0));
  x144 = x143^0xffffffffffffffff;
  x145 = (x129&x143)|(x135&x144);
  x146 = (0u-(br_word_t)1)+((br_word_t)(x139==(br_word_t)0));
  x147 = x146^0xffffffffffffffff;
  x148 = (x131&x146)|(x136&x147);
  x149 = (0u-(br_word_t)1)+((br_word_t)(x139==(br_word_t)0));
  x150 = x149^0xffffffffffffffff;
  x151 = (x132&x149)|(x138&x150);
  x152 = x142;
  x153 = x145;
  x154 = x148;
  x155 = x151;
  /*skip*/
  _br_store(out0+0, x152);
  _br_store(out0+8, x153);
  _br_store(out0+16, x154);
  _br_store(out0+24, x155);
  /*skip*/
}

static void fl_from_bytes(br_word_t out0, br_word_t in0) {
  br_word_t x31, x30, x29, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19, x18, x17, x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0, x62, x63, x61, x64, x60, x65, x59, x66, x58, x67, x57, x68, x56, x69, x54, x55, x53, x71, x52, x72, x51, x73, x50, x74, x49, x75, x48, x76, x46, x47, x45, x78, x44, x79, x43, x80, x42, x81, x41, x82, x40, x83, x38, x39, x37, x85, x36, x86, x35, x87, x34, x88, x33, x89, x32, x90, x70, x77, x84, x91, x92, x93, x94, x95;
  x0 = _br_load1(in0+0);
  x1 = _br_load1(in0+1);
  x2 = _br_load1(in0+2);
  x3 = _br_load1(in0+3);
  x4 = _br_load1(in0+4);
  x5 = _br_load1(in0+5);
  x6 = _br_load1(in0+6);
  x7 = _br_load1(in0+7);
  x8 = _br_load1(in0+8);
  x9 = _br_load1(in0+9);
  x10 = _br_load1(in0+10);
  x11 = _br_load1(in0+11);
  x12 = _br_load1(in0+12);
  x13 = _br_load1(in0+13);
  x14 = _br_load1(in0+14);
  x15 = _br_load1(in0+15);
  x16 = _br_load1(in0+16);
  x17 = _br_load1(in0+17);
  x18 = _br_load1(in0+18);
  x19 = _br_load1(in0+19);
  x20 = _br_load1(in0+20);
  x21 = _br_load1(in0+21);
  x22 = _br_load1(in0+22);
  x23 = _br_load1(in0+23);
  x24 = _br_load1(in0+24);
  x25 = _br_load1(in0+25);
  x26 = _br_load1(in0+26);
  x27 = _br_load1(in0+27);
  x28 = _br_load1(in0+28);
  x29 = _br_load1(in0+29);
  x30 = _br_load1(in0+30);
  x31 = _br_load1(in0+31);
  /*skip*/
  /*skip*/
  x32 = x31<<((br_word_t)56&(sizeof(br_word_t)*8-1));
  x33 = x30<<((br_word_t)48&(sizeof(br_word_t)*8-1));
  x34 = x29<<((br_word_t)40&(sizeof(br_word_t)*8-1));
  x35 = x28<<((br_word_t)32&(sizeof(br_word_t)*8-1));
  x36 = x27<<24;
  x37 = x26<<16;
  x38 = x25<<8;
  x39 = x24;
  x40 = x23<<((br_word_t)56&(sizeof(br_word_t)*8-1));
  x41 = x22<<((br_word_t)48&(sizeof(br_word_t)*8-1));
  x42 = x21<<((br_word_t)40&(sizeof(br_word_t)*8-1));
  x43 = x20<<((br_word_t)32&(sizeof(br_word_t)*8-1));
  x44 = x19<<24;
  x45 = x18<<16;
  x46 = x17<<8;
  x47 = x16;
  x48 = x15<<((br_word_t)56&(sizeof(br_word_t)*8-1));
  x49 = x14<<((br_word_t)48&(sizeof(br_word_t)*8-1));
  x50 = x13<<((br_word_t)40&(sizeof(br_word_t)*8-1));
  x51 = x12<<((br_word_t)32&(sizeof(br_word_t)*8-1));
  x52 = x11<<24;
  x53 = x10<<16;
  x54 = x9<<8;
  x55 = x8;
  x56 = x7<<((br_word_t)56&(sizeof(br_word_t)*8-1));
  x57 = x6<<((br_word_t)48&(sizeof(br_word_t)*8-1));
  x58 = x5<<((br_word_t)40&(sizeof(br_word_t)*8-1));
  x59 = x4<<((br_word_t)32&(sizeof(br_word_t)*8-1));
  x60 = x3<<24;
  x61 = x2<<16;
  x62 = x1<<8;
  x63 = x0;
  x64 = x62+x63;
  x65 = x61+x64;
  x66 = x60+x65;
  x67 = x59+x66;
  x68 = x58+x67;
  x69 = x57+x68;
  x70 = x56+x69;
  x71 = x54+x55;
  x72 = x53+x71;
  x73 = x52+x72;
  x74 = x51+x73;
  x75 = x50+x74;
  x76 = x49+x75;
  x77 = x48+x76;
  x78 = x46+x47;
  x79 = x45+x78;
  x80 = x44+x79;
  x81 = x43+x80;
  x82 = x42+x81;
  x83 = x41+x82;
  x84 = x40+x83;
  x85 = x38+x39;
  x86 = x37+x85;
  x87 = x36+x86;
  x88 = x35+x87;
  x89 = x34+x88;
  x90 = x33+x89;
  x91 = x32+x90;
  x92 = x70;
  x93 = x77;
  x94 = x84;
  x95 = x91;
  /*skip*/
  _br_store(out0+0, x92);
  _br_store(out0+8, x93);
  _br_store(out0+16, x94);
  _br_store(out0+24, x95);
  /*skip*/
}

static void fl_to_bytes(br_word_t out0, br_word_t in0) {
  br_word_t x3, x2, x1, x0, x7, x9, x11, x13, x15, x17, x19, x6, x23, x25, x27, x29, x31, x33, x5, x37, x39, x41, x43, x45, x47, x4, x51, x53, x55, x57, x59, x61, x8, x10, x12, x14, x16, x18, x20, x21, x22, x24, x26, x28, x30, x32, x34, x35, x36, x38, x40, x42, x44, x46, x48, x49, x50, x52, x54, x56, x58, x60, x62, x63, x64, x65, x66, x67, x68, x69, x70, x71, x72, x73, x74, x75, x76, x77, x78, x79, x80, x81, x82, x83, x84, x85, x86, x87, x88, x89, x90, x91, x92, x93, x94, x95;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  /*skip*/
  x4 = x3;
  x5 = x2;
  x6 = x1;
  x7 = x0;
  x8 = x7&0xff;
  x9 = x7>>8;
  x10 = x9&0xff;
  x11 = x9>>8;
  x12 = x11&0xff;
  x13 = x11>>8;
  x14 = x13&0xff;
  x15 = x13>>8;
  x16 = x15&0xff;
  x17 = x15>>8;
  x18 = x17&0xff;
  x19 = x17>>8;
  x20 = x19&0xff;
  x21 = x19>>8;
  x22 = x6&0xff;
  x23 = x6>>8;
  x24 = x23&0xff;
  x25 = x23>>8;
  x26 = x25&0xff;
  x27 = x25>>8;
  x28 = x27&0xff;
  x29 = x27>>8;
  x30 = x29&0xff;
  x31 = x29>>8;
  x32 = x31&0xff;
  x33 = x31>>8;
  x34 = x33&0xff;
  x35 = x33>>8;
  x36 = x5&0xff;
  x37 = x5>>8;
  x38 = x37&0xff;
  x39 = x37>>8;
  x40 = x39&0xff;
  x41 = x39>>8;
  x42 = x41&0xff;
  x43 = x41>>8;
  x44 = x43&0xff;
  x45 = x43>>8;
  x46 = x45&0xff;
  x47 = x45>>8;
  x48 = x47&0xff;
  x49 = x47>>8;
  x50 = x4&0xff;
  x51 = x4>>8;
  x52 = x51&0xff;
  x53 = x51>>8;
  x54 = x53&0xff;
  x55 = x53>>8;
  x56 = x55&0xff;
  x57 = x55>>8;
  x58 = x57&0xff;
  x59 = x57>>8;
  x60 = x59&0xff;
  x61 = x59>>8;
  x62 = x61&0xff;
  x63 = x61>>8;
  x64 = x8;
  x65 = x10;
  x66 = x12;
  x67 = x14;
  x68 = x16;
  x69 = x18;
  x70 = x20;
  x71 = x21;
  x72 = x22;
  x73 = x24;
  x74 = x26;
  x75 = x28;
  x76 = x30;
  x77 = x32;
  x78 = x34;
  x79 = x35;
  x80 = x36;
  x81 = x38;
  x82 = x40;
  x83 = x42;
  x84 = x44;
  x85 = x46;
  x86 = x48;
  x87 = x49;
  x88 = x50;
  x89 = x52;
  x90 = x54;
  x91 = x56;
  x92 = x58;
  x93 = x60;
  x94 = x62;
  x95 = x63;
  /*skip*/
  _br_store1(out0+0, x64);
  _br_store1(out0+1, x65);
  _br_store1(out0+2, x66);
  _br_store1(out0+3, x67);
  _br_store1(out0+4, x68);
  _br_store1(out0+5, x69);
  _br_store1(out0+6, x70);
  _br_store1(out0+7, x71);
  _br_store1(out0+8, x72);
  _br_store1(out0+9, x73);
  _br_store1(out0+10, x74);
  _br_store1(out0+11, x75);
  _br_store1(out0+12, x76);
  _br_store1(out0+13, x77);
  _br_store1(out0+14, x78);
  _br_store1(out0+15, x79);
  _br_store1(out0+16, x80);
  _br_store1(out0+17, x81);
  _br_store1(out0+18, x82);
  _br_store1(out0+19, x83);
  _br_store1(out0+20, x84);
  _br_store1(out0+21, x85);
  _br_store1(out0+22, x86);
  _br_store1(out0+23, x87);
  _br_store1(out0+24, x88);
  _br_store1(out0+25, x89);
  _br_store1(out0+26, x90);
  _br_store1(out0+27, x91);
  _br_store1(out0+28, x92);
  _br_store1(out0+29, x93);
  _br_store1(out0+30, x94);
  _br_store1(out0+31, x95);
  /*skip*/
}
