static void femul(uint64_t out[5], const uint64_t in1[5], const uint64_t in2[5]) {
  { const uint64_t x10 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x18 = in2[4];
  { const uint64_t x19 = in2[3];
  { const uint64_t x17 = in2[2];
  { const uint64_t x15 = in2[1];
  { const uint64_t x13 = in2[0];
  { uint64_t x22;  uint64_t x21 = _mulx_u64(x5, x13, &x22);
  { uint64_t x25;  uint64_t x24 = _mulx_u64(x5, x15, &x25);
  { uint64_t x28;  uint64_t x27 = _mulx_u64(x5, x17, &x28);
  { uint64_t x31;  uint64_t x30 = _mulx_u64(x5, x19, &x31);
  { uint64_t x34;  uint64_t x33 = _mulx_u64(x5, x18, &x34);
  { uint64_t x36; uint8_t x37 = _addcarryx_u64(0x0, x22, x24, &x36);
  { uint64_t x39; uint8_t x40 = _addcarryx_u64(x37, x25, x27, &x39);
  { uint64_t x42; uint8_t x43 = _addcarryx_u64(x40, x28, x30, &x42);
  { uint64_t x45; uint8_t x46 = _addcarryx_u64(x43, x31, x33, &x45);
  { uint64_t x48; uint8_t _ = _addcarryx_u64(0x0, x46, x34, &x48);
  { uint64_t _;  uint64_t x51 = _mulx_u64(x21, 0x8e38e38e38e38e39L, &_);
  { uint64_t x55;  uint64_t x54 = _mulx_u64(x51, 0xfffffffffffffff7L, &x55);
  { uint64_t x58;  uint64_t x57 = _mulx_u64(x51, 0xffffffffffffffffL, &x58);
  { uint64_t x61;  uint64_t x60 = _mulx_u64(x51, 0xffffffffffffffffL, &x61);
  { uint64_t x64;  uint64_t x63 = _mulx_u64(x51, 0xffffffffffffffffL, &x64);
  { uint64_t x67;  uint64_t x66 = _mulx_u64(x51, 0x1fffffff, &x67);
  { uint64_t x69; uint8_t x70 = _addcarryx_u64(0x0, x55, x57, &x69);
  { uint64_t x72; uint8_t x73 = _addcarryx_u64(x70, x58, x60, &x72);
  { uint64_t x75; uint8_t x76 = _addcarryx_u64(x73, x61, x63, &x75);
  { uint64_t x78; uint8_t x79 = _addcarryx_u64(x76, x64, x66, &x78);
  { uint64_t x81; uint8_t _ = _addcarryx_u64(0x0, x79, x67, &x81);
  { uint64_t _; uint8_t x85 = _addcarryx_u64(0x0, x21, x54, &_);
  { uint64_t x87; uint8_t x88 = _addcarryx_u64(x85, x36, x69, &x87);
  { uint64_t x90; uint8_t x91 = _addcarryx_u64(x88, x39, x72, &x90);
  { uint64_t x93; uint8_t x94 = _addcarryx_u64(x91, x42, x75, &x93);
  { uint64_t x96; uint8_t x97 = _addcarryx_u64(x94, x45, x78, &x96);
  { uint64_t x99; uint8_t x100 = _addcarryx_u64(x97, x48, x81, &x99);
  { uint64_t x103;  uint64_t x102 = _mulx_u64(x7, x13, &x103);
  { uint64_t x106;  uint64_t x105 = _mulx_u64(x7, x15, &x106);
  { uint64_t x109;  uint64_t x108 = _mulx_u64(x7, x17, &x109);
  { uint64_t x112;  uint64_t x111 = _mulx_u64(x7, x19, &x112);
  { uint64_t x115;  uint64_t x114 = _mulx_u64(x7, x18, &x115);
  { uint64_t x117; uint8_t x118 = _addcarryx_u64(0x0, x103, x105, &x117);
  { uint64_t x120; uint8_t x121 = _addcarryx_u64(x118, x106, x108, &x120);
  { uint64_t x123; uint8_t x124 = _addcarryx_u64(x121, x109, x111, &x123);
  { uint64_t x126; uint8_t x127 = _addcarryx_u64(x124, x112, x114, &x126);
  { uint64_t x129; uint8_t _ = _addcarryx_u64(0x0, x127, x115, &x129);
  { uint64_t x132; uint8_t x133 = _addcarryx_u64(0x0, x87, x102, &x132);
  { uint64_t x135; uint8_t x136 = _addcarryx_u64(x133, x90, x117, &x135);
  { uint64_t x138; uint8_t x139 = _addcarryx_u64(x136, x93, x120, &x138);
  { uint64_t x141; uint8_t x142 = _addcarryx_u64(x139, x96, x123, &x141);
  { uint64_t x144; uint8_t x145 = _addcarryx_u64(x142, x99, x126, &x144);
  { uint64_t x147; uint8_t x148 = _addcarryx_u64(x145, x100, x129, &x147);
  { uint64_t _;  uint64_t x150 = _mulx_u64(x132, 0x8e38e38e38e38e39L, &_);
  { uint64_t x154;  uint64_t x153 = _mulx_u64(x150, 0xfffffffffffffff7L, &x154);
  { uint64_t x157;  uint64_t x156 = _mulx_u64(x150, 0xffffffffffffffffL, &x157);
  { uint64_t x160;  uint64_t x159 = _mulx_u64(x150, 0xffffffffffffffffL, &x160);
  { uint64_t x163;  uint64_t x162 = _mulx_u64(x150, 0xffffffffffffffffL, &x163);
  { uint64_t x166;  uint64_t x165 = _mulx_u64(x150, 0x1fffffff, &x166);
  { uint64_t x168; uint8_t x169 = _addcarryx_u64(0x0, x154, x156, &x168);
  { uint64_t x171; uint8_t x172 = _addcarryx_u64(x169, x157, x159, &x171);
  { uint64_t x174; uint8_t x175 = _addcarryx_u64(x172, x160, x162, &x174);
  { uint64_t x177; uint8_t x178 = _addcarryx_u64(x175, x163, x165, &x177);
  { uint64_t x180; uint8_t _ = _addcarryx_u64(0x0, x178, x166, &x180);
  { uint64_t _; uint8_t x184 = _addcarryx_u64(0x0, x132, x153, &_);
  { uint64_t x186; uint8_t x187 = _addcarryx_u64(x184, x135, x168, &x186);
  { uint64_t x189; uint8_t x190 = _addcarryx_u64(x187, x138, x171, &x189);
  { uint64_t x192; uint8_t x193 = _addcarryx_u64(x190, x141, x174, &x192);
  { uint64_t x195; uint8_t x196 = _addcarryx_u64(x193, x144, x177, &x195);
  { uint64_t x198; uint8_t x199 = _addcarryx_u64(x196, x147, x180, &x198);
  { uint8_t x200 = (x199 + x148);
  { uint64_t x203;  uint64_t x202 = _mulx_u64(x9, x13, &x203);
  { uint64_t x206;  uint64_t x205 = _mulx_u64(x9, x15, &x206);
  { uint64_t x209;  uint64_t x208 = _mulx_u64(x9, x17, &x209);
  { uint64_t x212;  uint64_t x211 = _mulx_u64(x9, x19, &x212);
  { uint64_t x215;  uint64_t x214 = _mulx_u64(x9, x18, &x215);
  { uint64_t x217; uint8_t x218 = _addcarryx_u64(0x0, x203, x205, &x217);
  { uint64_t x220; uint8_t x221 = _addcarryx_u64(x218, x206, x208, &x220);
  { uint64_t x223; uint8_t x224 = _addcarryx_u64(x221, x209, x211, &x223);
  { uint64_t x226; uint8_t x227 = _addcarryx_u64(x224, x212, x214, &x226);
  { uint64_t x229; uint8_t _ = _addcarryx_u64(0x0, x227, x215, &x229);
  { uint64_t x232; uint8_t x233 = _addcarryx_u64(0x0, x186, x202, &x232);
  { uint64_t x235; uint8_t x236 = _addcarryx_u64(x233, x189, x217, &x235);
  { uint64_t x238; uint8_t x239 = _addcarryx_u64(x236, x192, x220, &x238);
  { uint64_t x241; uint8_t x242 = _addcarryx_u64(x239, x195, x223, &x241);
  { uint64_t x244; uint8_t x245 = _addcarryx_u64(x242, x198, x226, &x244);
  { uint64_t x247; uint8_t x248 = _addcarryx_u64(x245, x200, x229, &x247);
  { uint64_t _;  uint64_t x250 = _mulx_u64(x232, 0x8e38e38e38e38e39L, &_);
  { uint64_t x254;  uint64_t x253 = _mulx_u64(x250, 0xfffffffffffffff7L, &x254);
  { uint64_t x257;  uint64_t x256 = _mulx_u64(x250, 0xffffffffffffffffL, &x257);
  { uint64_t x260;  uint64_t x259 = _mulx_u64(x250, 0xffffffffffffffffL, &x260);
  { uint64_t x263;  uint64_t x262 = _mulx_u64(x250, 0xffffffffffffffffL, &x263);
  { uint64_t x266;  uint64_t x265 = _mulx_u64(x250, 0x1fffffff, &x266);
  { uint64_t x268; uint8_t x269 = _addcarryx_u64(0x0, x254, x256, &x268);
  { uint64_t x271; uint8_t x272 = _addcarryx_u64(x269, x257, x259, &x271);
  { uint64_t x274; uint8_t x275 = _addcarryx_u64(x272, x260, x262, &x274);
  { uint64_t x277; uint8_t x278 = _addcarryx_u64(x275, x263, x265, &x277);
  { uint64_t x280; uint8_t _ = _addcarryx_u64(0x0, x278, x266, &x280);
  { uint64_t _; uint8_t x284 = _addcarryx_u64(0x0, x232, x253, &_);
  { uint64_t x286; uint8_t x287 = _addcarryx_u64(x284, x235, x268, &x286);
  { uint64_t x289; uint8_t x290 = _addcarryx_u64(x287, x238, x271, &x289);
  { uint64_t x292; uint8_t x293 = _addcarryx_u64(x290, x241, x274, &x292);
  { uint64_t x295; uint8_t x296 = _addcarryx_u64(x293, x244, x277, &x295);
  { uint64_t x298; uint8_t x299 = _addcarryx_u64(x296, x247, x280, &x298);
  { uint8_t x300 = (x299 + x248);
  { uint64_t x303;  uint64_t x302 = _mulx_u64(x11, x13, &x303);
  { uint64_t x306;  uint64_t x305 = _mulx_u64(x11, x15, &x306);
  { uint64_t x309;  uint64_t x308 = _mulx_u64(x11, x17, &x309);
  { uint64_t x312;  uint64_t x311 = _mulx_u64(x11, x19, &x312);
  { uint64_t x315;  uint64_t x314 = _mulx_u64(x11, x18, &x315);
  { uint64_t x317; uint8_t x318 = _addcarryx_u64(0x0, x303, x305, &x317);
  { uint64_t x320; uint8_t x321 = _addcarryx_u64(x318, x306, x308, &x320);
  { uint64_t x323; uint8_t x324 = _addcarryx_u64(x321, x309, x311, &x323);
  { uint64_t x326; uint8_t x327 = _addcarryx_u64(x324, x312, x314, &x326);
  { uint64_t x329; uint8_t _ = _addcarryx_u64(0x0, x327, x315, &x329);
  { uint64_t x332; uint8_t x333 = _addcarryx_u64(0x0, x286, x302, &x332);
  { uint64_t x335; uint8_t x336 = _addcarryx_u64(x333, x289, x317, &x335);
  { uint64_t x338; uint8_t x339 = _addcarryx_u64(x336, x292, x320, &x338);
  { uint64_t x341; uint8_t x342 = _addcarryx_u64(x339, x295, x323, &x341);
  { uint64_t x344; uint8_t x345 = _addcarryx_u64(x342, x298, x326, &x344);
  { uint64_t x347; uint8_t x348 = _addcarryx_u64(x345, x300, x329, &x347);
  { uint64_t _;  uint64_t x350 = _mulx_u64(x332, 0x8e38e38e38e38e39L, &_);
  { uint64_t x354;  uint64_t x353 = _mulx_u64(x350, 0xfffffffffffffff7L, &x354);
  { uint64_t x357;  uint64_t x356 = _mulx_u64(x350, 0xffffffffffffffffL, &x357);
  { uint64_t x360;  uint64_t x359 = _mulx_u64(x350, 0xffffffffffffffffL, &x360);
  { uint64_t x363;  uint64_t x362 = _mulx_u64(x350, 0xffffffffffffffffL, &x363);
  { uint64_t x366;  uint64_t x365 = _mulx_u64(x350, 0x1fffffff, &x366);
  { uint64_t x368; uint8_t x369 = _addcarryx_u64(0x0, x354, x356, &x368);
  { uint64_t x371; uint8_t x372 = _addcarryx_u64(x369, x357, x359, &x371);
  { uint64_t x374; uint8_t x375 = _addcarryx_u64(x372, x360, x362, &x374);
  { uint64_t x377; uint8_t x378 = _addcarryx_u64(x375, x363, x365, &x377);
  { uint64_t x380; uint8_t _ = _addcarryx_u64(0x0, x378, x366, &x380);
  { uint64_t _; uint8_t x384 = _addcarryx_u64(0x0, x332, x353, &_);
  { uint64_t x386; uint8_t x387 = _addcarryx_u64(x384, x335, x368, &x386);
  { uint64_t x389; uint8_t x390 = _addcarryx_u64(x387, x338, x371, &x389);
  { uint64_t x392; uint8_t x393 = _addcarryx_u64(x390, x341, x374, &x392);
  { uint64_t x395; uint8_t x396 = _addcarryx_u64(x393, x344, x377, &x395);
  { uint64_t x398; uint8_t x399 = _addcarryx_u64(x396, x347, x380, &x398);
  { uint8_t x400 = (x399 + x348);
  { uint64_t x403;  uint64_t x402 = _mulx_u64(x10, x13, &x403);
  { uint64_t x406;  uint64_t x405 = _mulx_u64(x10, x15, &x406);
  { uint64_t x409;  uint64_t x408 = _mulx_u64(x10, x17, &x409);
  { uint64_t x412;  uint64_t x411 = _mulx_u64(x10, x19, &x412);
  { uint64_t x415;  uint64_t x414 = _mulx_u64(x10, x18, &x415);
  { uint64_t x417; uint8_t x418 = _addcarryx_u64(0x0, x403, x405, &x417);
  { uint64_t x420; uint8_t x421 = _addcarryx_u64(x418, x406, x408, &x420);
  { uint64_t x423; uint8_t x424 = _addcarryx_u64(x421, x409, x411, &x423);
  { uint64_t x426; uint8_t x427 = _addcarryx_u64(x424, x412, x414, &x426);
  { uint64_t x429; uint8_t _ = _addcarryx_u64(0x0, x427, x415, &x429);
  { uint64_t x432; uint8_t x433 = _addcarryx_u64(0x0, x386, x402, &x432);
  { uint64_t x435; uint8_t x436 = _addcarryx_u64(x433, x389, x417, &x435);
  { uint64_t x438; uint8_t x439 = _addcarryx_u64(x436, x392, x420, &x438);
  { uint64_t x441; uint8_t x442 = _addcarryx_u64(x439, x395, x423, &x441);
  { uint64_t x444; uint8_t x445 = _addcarryx_u64(x442, x398, x426, &x444);
  { uint64_t x447; uint8_t x448 = _addcarryx_u64(x445, x400, x429, &x447);
  { uint64_t _;  uint64_t x450 = _mulx_u64(x432, 0x8e38e38e38e38e39L, &_);
  { uint64_t x454;  uint64_t x453 = _mulx_u64(x450, 0xfffffffffffffff7L, &x454);
  { uint64_t x457;  uint64_t x456 = _mulx_u64(x450, 0xffffffffffffffffL, &x457);
  { uint64_t x460;  uint64_t x459 = _mulx_u64(x450, 0xffffffffffffffffL, &x460);
  { uint64_t x463;  uint64_t x462 = _mulx_u64(x450, 0xffffffffffffffffL, &x463);
  { uint64_t x466;  uint64_t x465 = _mulx_u64(x450, 0x1fffffff, &x466);
  { uint64_t x468; uint8_t x469 = _addcarryx_u64(0x0, x454, x456, &x468);
  { uint64_t x471; uint8_t x472 = _addcarryx_u64(x469, x457, x459, &x471);
  { uint64_t x474; uint8_t x475 = _addcarryx_u64(x472, x460, x462, &x474);
  { uint64_t x477; uint8_t x478 = _addcarryx_u64(x475, x463, x465, &x477);
  { uint64_t x480; uint8_t _ = _addcarryx_u64(0x0, x478, x466, &x480);
  { uint64_t _; uint8_t x484 = _addcarryx_u64(0x0, x432, x453, &_);
  { uint64_t x486; uint8_t x487 = _addcarryx_u64(x484, x435, x468, &x486);
  { uint64_t x489; uint8_t x490 = _addcarryx_u64(x487, x438, x471, &x489);
  { uint64_t x492; uint8_t x493 = _addcarryx_u64(x490, x441, x474, &x492);
  { uint64_t x495; uint8_t x496 = _addcarryx_u64(x493, x444, x477, &x495);
  { uint64_t x498; uint8_t x499 = _addcarryx_u64(x496, x447, x480, &x498);
  { uint8_t x500 = (x499 + x448);
  { uint64_t x502; uint8_t x503 = _subborrow_u64(0x0, x486, 0xfffffffffffffff7L, &x502);
  { uint64_t x505; uint8_t x506 = _subborrow_u64(x503, x489, 0xffffffffffffffffL, &x505);
  { uint64_t x508; uint8_t x509 = _subborrow_u64(x506, x492, 0xffffffffffffffffL, &x508);
  { uint64_t x511; uint8_t x512 = _subborrow_u64(x509, x495, 0xffffffffffffffffL, &x511);
  { uint64_t x514; uint8_t x515 = _subborrow_u64(x512, x498, 0x1fffffff, &x514);
  { uint64_t _; uint8_t x518 = _subborrow_u64(x515, x500, 0x0, &_);
  { uint64_t x519 = cmovznz64(x518, x514, x498);
  { uint64_t x520 = cmovznz64(x518, x511, x495);
  { uint64_t x521 = cmovznz64(x518, x508, x492);
  { uint64_t x522 = cmovznz64(x518, x505, x489);
  { uint64_t x523 = cmovznz64(x518, x502, x486);
  out[0] = x523;
  out[1] = x522;
  out[2] = x521;
  out[3] = x520;
  out[4] = x519;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
