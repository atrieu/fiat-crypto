static void femul(uint32_t out[5], const uint32_t in1[5], const uint32_t in2[5]) {
  { const uint32_t x10 = in1[4];
  { const uint32_t x11 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x18 = in2[4];
  { const uint32_t x19 = in2[3];
  { const uint32_t x17 = in2[2];
  { const uint32_t x15 = in2[1];
  { const uint32_t x13 = in2[0];
  { uint32_t x22;  uint32_t x21 = _mulx_u32(x5, x13, &x22);
  { uint32_t x25;  uint32_t x24 = _mulx_u32(x5, x15, &x25);
  { uint32_t x28;  uint32_t x27 = _mulx_u32(x5, x17, &x28);
  { uint32_t x31;  uint32_t x30 = _mulx_u32(x5, x19, &x31);
  { uint32_t x34;  uint32_t x33 = _mulx_u32(x5, x18, &x34);
  { uint32_t x36; uint8_t x37 = _addcarryx_u32(0x0, x22, x24, &x36);
  { uint32_t x39; uint8_t x40 = _addcarryx_u32(x37, x25, x27, &x39);
  { uint32_t x42; uint8_t x43 = _addcarryx_u32(x40, x28, x30, &x42);
  { uint32_t x45; uint8_t x46 = _addcarryx_u32(x43, x31, x33, &x45);
  { uint32_t x48; uint8_t _ = _addcarryx_u32(0x0, x46, x34, &x48);
  { uint32_t _;  uint32_t x51 = _mulx_u32(x21, 0xaaaaaaab, &_);
  { uint32_t x55;  uint32_t x54 = _mulx_u32(x51, 0xfffffffd, &x55);
  { uint32_t x58;  uint32_t x57 = _mulx_u32(x51, 0xffffffff, &x58);
  { uint32_t x61;  uint32_t x60 = _mulx_u32(x51, 0xffffffff, &x61);
  { uint32_t x64;  uint32_t x63 = _mulx_u32(x51, 0xffffffff, &x64);
  { uint32_t x67;  uint32_t x66 = _mulx_u32(x51, 0x3fffff, &x67);
  { uint32_t x69; uint8_t x70 = _addcarryx_u32(0x0, x55, x57, &x69);
  { uint32_t x72; uint8_t x73 = _addcarryx_u32(x70, x58, x60, &x72);
  { uint32_t x75; uint8_t x76 = _addcarryx_u32(x73, x61, x63, &x75);
  { uint32_t x78; uint8_t x79 = _addcarryx_u32(x76, x64, x66, &x78);
  { uint32_t x81; uint8_t _ = _addcarryx_u32(0x0, x79, x67, &x81);
  { uint32_t _; uint8_t x85 = _addcarryx_u32(0x0, x21, x54, &_);
  { uint32_t x87; uint8_t x88 = _addcarryx_u32(x85, x36, x69, &x87);
  { uint32_t x90; uint8_t x91 = _addcarryx_u32(x88, x39, x72, &x90);
  { uint32_t x93; uint8_t x94 = _addcarryx_u32(x91, x42, x75, &x93);
  { uint32_t x96; uint8_t x97 = _addcarryx_u32(x94, x45, x78, &x96);
  { uint32_t x99; uint8_t x100 = _addcarryx_u32(x97, x48, x81, &x99);
  { uint32_t x103;  uint32_t x102 = _mulx_u32(x7, x13, &x103);
  { uint32_t x106;  uint32_t x105 = _mulx_u32(x7, x15, &x106);
  { uint32_t x109;  uint32_t x108 = _mulx_u32(x7, x17, &x109);
  { uint32_t x112;  uint32_t x111 = _mulx_u32(x7, x19, &x112);
  { uint32_t x115;  uint32_t x114 = _mulx_u32(x7, x18, &x115);
  { uint32_t x117; uint8_t x118 = _addcarryx_u32(0x0, x103, x105, &x117);
  { uint32_t x120; uint8_t x121 = _addcarryx_u32(x118, x106, x108, &x120);
  { uint32_t x123; uint8_t x124 = _addcarryx_u32(x121, x109, x111, &x123);
  { uint32_t x126; uint8_t x127 = _addcarryx_u32(x124, x112, x114, &x126);
  { uint32_t x129; uint8_t _ = _addcarryx_u32(0x0, x127, x115, &x129);
  { uint32_t x132; uint8_t x133 = _addcarryx_u32(0x0, x87, x102, &x132);
  { uint32_t x135; uint8_t x136 = _addcarryx_u32(x133, x90, x117, &x135);
  { uint32_t x138; uint8_t x139 = _addcarryx_u32(x136, x93, x120, &x138);
  { uint32_t x141; uint8_t x142 = _addcarryx_u32(x139, x96, x123, &x141);
  { uint32_t x144; uint8_t x145 = _addcarryx_u32(x142, x99, x126, &x144);
  { uint32_t x147; uint8_t x148 = _addcarryx_u32(x145, x100, x129, &x147);
  { uint32_t _;  uint32_t x150 = _mulx_u32(x132, 0xaaaaaaab, &_);
  { uint32_t x154;  uint32_t x153 = _mulx_u32(x150, 0xfffffffd, &x154);
  { uint32_t x157;  uint32_t x156 = _mulx_u32(x150, 0xffffffff, &x157);
  { uint32_t x160;  uint32_t x159 = _mulx_u32(x150, 0xffffffff, &x160);
  { uint32_t x163;  uint32_t x162 = _mulx_u32(x150, 0xffffffff, &x163);
  { uint32_t x166;  uint32_t x165 = _mulx_u32(x150, 0x3fffff, &x166);
  { uint32_t x168; uint8_t x169 = _addcarryx_u32(0x0, x154, x156, &x168);
  { uint32_t x171; uint8_t x172 = _addcarryx_u32(x169, x157, x159, &x171);
  { uint32_t x174; uint8_t x175 = _addcarryx_u32(x172, x160, x162, &x174);
  { uint32_t x177; uint8_t x178 = _addcarryx_u32(x175, x163, x165, &x177);
  { uint32_t x180; uint8_t _ = _addcarryx_u32(0x0, x178, x166, &x180);
  { uint32_t _; uint8_t x184 = _addcarryx_u32(0x0, x132, x153, &_);
  { uint32_t x186; uint8_t x187 = _addcarryx_u32(x184, x135, x168, &x186);
  { uint32_t x189; uint8_t x190 = _addcarryx_u32(x187, x138, x171, &x189);
  { uint32_t x192; uint8_t x193 = _addcarryx_u32(x190, x141, x174, &x192);
  { uint32_t x195; uint8_t x196 = _addcarryx_u32(x193, x144, x177, &x195);
  { uint32_t x198; uint8_t x199 = _addcarryx_u32(x196, x147, x180, &x198);
  { uint8_t x200 = (x199 + x148);
  { uint32_t x203;  uint32_t x202 = _mulx_u32(x9, x13, &x203);
  { uint32_t x206;  uint32_t x205 = _mulx_u32(x9, x15, &x206);
  { uint32_t x209;  uint32_t x208 = _mulx_u32(x9, x17, &x209);
  { uint32_t x212;  uint32_t x211 = _mulx_u32(x9, x19, &x212);
  { uint32_t x215;  uint32_t x214 = _mulx_u32(x9, x18, &x215);
  { uint32_t x217; uint8_t x218 = _addcarryx_u32(0x0, x203, x205, &x217);
  { uint32_t x220; uint8_t x221 = _addcarryx_u32(x218, x206, x208, &x220);
  { uint32_t x223; uint8_t x224 = _addcarryx_u32(x221, x209, x211, &x223);
  { uint32_t x226; uint8_t x227 = _addcarryx_u32(x224, x212, x214, &x226);
  { uint32_t x229; uint8_t _ = _addcarryx_u32(0x0, x227, x215, &x229);
  { uint32_t x232; uint8_t x233 = _addcarryx_u32(0x0, x186, x202, &x232);
  { uint32_t x235; uint8_t x236 = _addcarryx_u32(x233, x189, x217, &x235);
  { uint32_t x238; uint8_t x239 = _addcarryx_u32(x236, x192, x220, &x238);
  { uint32_t x241; uint8_t x242 = _addcarryx_u32(x239, x195, x223, &x241);
  { uint32_t x244; uint8_t x245 = _addcarryx_u32(x242, x198, x226, &x244);
  { uint32_t x247; uint8_t x248 = _addcarryx_u32(x245, x200, x229, &x247);
  { uint32_t _;  uint32_t x250 = _mulx_u32(x232, 0xaaaaaaab, &_);
  { uint32_t x254;  uint32_t x253 = _mulx_u32(x250, 0xfffffffd, &x254);
  { uint32_t x257;  uint32_t x256 = _mulx_u32(x250, 0xffffffff, &x257);
  { uint32_t x260;  uint32_t x259 = _mulx_u32(x250, 0xffffffff, &x260);
  { uint32_t x263;  uint32_t x262 = _mulx_u32(x250, 0xffffffff, &x263);
  { uint32_t x266;  uint32_t x265 = _mulx_u32(x250, 0x3fffff, &x266);
  { uint32_t x268; uint8_t x269 = _addcarryx_u32(0x0, x254, x256, &x268);
  { uint32_t x271; uint8_t x272 = _addcarryx_u32(x269, x257, x259, &x271);
  { uint32_t x274; uint8_t x275 = _addcarryx_u32(x272, x260, x262, &x274);
  { uint32_t x277; uint8_t x278 = _addcarryx_u32(x275, x263, x265, &x277);
  { uint32_t x280; uint8_t _ = _addcarryx_u32(0x0, x278, x266, &x280);
  { uint32_t _; uint8_t x284 = _addcarryx_u32(0x0, x232, x253, &_);
  { uint32_t x286; uint8_t x287 = _addcarryx_u32(x284, x235, x268, &x286);
  { uint32_t x289; uint8_t x290 = _addcarryx_u32(x287, x238, x271, &x289);
  { uint32_t x292; uint8_t x293 = _addcarryx_u32(x290, x241, x274, &x292);
  { uint32_t x295; uint8_t x296 = _addcarryx_u32(x293, x244, x277, &x295);
  { uint32_t x298; uint8_t x299 = _addcarryx_u32(x296, x247, x280, &x298);
  { uint8_t x300 = (x299 + x248);
  { uint32_t x303;  uint32_t x302 = _mulx_u32(x11, x13, &x303);
  { uint32_t x306;  uint32_t x305 = _mulx_u32(x11, x15, &x306);
  { uint32_t x309;  uint32_t x308 = _mulx_u32(x11, x17, &x309);
  { uint32_t x312;  uint32_t x311 = _mulx_u32(x11, x19, &x312);
  { uint32_t x315;  uint32_t x314 = _mulx_u32(x11, x18, &x315);
  { uint32_t x317; uint8_t x318 = _addcarryx_u32(0x0, x303, x305, &x317);
  { uint32_t x320; uint8_t x321 = _addcarryx_u32(x318, x306, x308, &x320);
  { uint32_t x323; uint8_t x324 = _addcarryx_u32(x321, x309, x311, &x323);
  { uint32_t x326; uint8_t x327 = _addcarryx_u32(x324, x312, x314, &x326);
  { uint32_t x329; uint8_t _ = _addcarryx_u32(0x0, x327, x315, &x329);
  { uint32_t x332; uint8_t x333 = _addcarryx_u32(0x0, x286, x302, &x332);
  { uint32_t x335; uint8_t x336 = _addcarryx_u32(x333, x289, x317, &x335);
  { uint32_t x338; uint8_t x339 = _addcarryx_u32(x336, x292, x320, &x338);
  { uint32_t x341; uint8_t x342 = _addcarryx_u32(x339, x295, x323, &x341);
  { uint32_t x344; uint8_t x345 = _addcarryx_u32(x342, x298, x326, &x344);
  { uint32_t x347; uint8_t x348 = _addcarryx_u32(x345, x300, x329, &x347);
  { uint32_t _;  uint32_t x350 = _mulx_u32(x332, 0xaaaaaaab, &_);
  { uint32_t x354;  uint32_t x353 = _mulx_u32(x350, 0xfffffffd, &x354);
  { uint32_t x357;  uint32_t x356 = _mulx_u32(x350, 0xffffffff, &x357);
  { uint32_t x360;  uint32_t x359 = _mulx_u32(x350, 0xffffffff, &x360);
  { uint32_t x363;  uint32_t x362 = _mulx_u32(x350, 0xffffffff, &x363);
  { uint32_t x366;  uint32_t x365 = _mulx_u32(x350, 0x3fffff, &x366);
  { uint32_t x368; uint8_t x369 = _addcarryx_u32(0x0, x354, x356, &x368);
  { uint32_t x371; uint8_t x372 = _addcarryx_u32(x369, x357, x359, &x371);
  { uint32_t x374; uint8_t x375 = _addcarryx_u32(x372, x360, x362, &x374);
  { uint32_t x377; uint8_t x378 = _addcarryx_u32(x375, x363, x365, &x377);
  { uint32_t x380; uint8_t _ = _addcarryx_u32(0x0, x378, x366, &x380);
  { uint32_t _; uint8_t x384 = _addcarryx_u32(0x0, x332, x353, &_);
  { uint32_t x386; uint8_t x387 = _addcarryx_u32(x384, x335, x368, &x386);
  { uint32_t x389; uint8_t x390 = _addcarryx_u32(x387, x338, x371, &x389);
  { uint32_t x392; uint8_t x393 = _addcarryx_u32(x390, x341, x374, &x392);
  { uint32_t x395; uint8_t x396 = _addcarryx_u32(x393, x344, x377, &x395);
  { uint32_t x398; uint8_t x399 = _addcarryx_u32(x396, x347, x380, &x398);
  { uint8_t x400 = (x399 + x348);
  { uint32_t x403;  uint32_t x402 = _mulx_u32(x10, x13, &x403);
  { uint32_t x406;  uint32_t x405 = _mulx_u32(x10, x15, &x406);
  { uint32_t x409;  uint32_t x408 = _mulx_u32(x10, x17, &x409);
  { uint32_t x412;  uint32_t x411 = _mulx_u32(x10, x19, &x412);
  { uint32_t x415;  uint32_t x414 = _mulx_u32(x10, x18, &x415);
  { uint32_t x417; uint8_t x418 = _addcarryx_u32(0x0, x403, x405, &x417);
  { uint32_t x420; uint8_t x421 = _addcarryx_u32(x418, x406, x408, &x420);
  { uint32_t x423; uint8_t x424 = _addcarryx_u32(x421, x409, x411, &x423);
  { uint32_t x426; uint8_t x427 = _addcarryx_u32(x424, x412, x414, &x426);
  { uint32_t x429; uint8_t _ = _addcarryx_u32(0x0, x427, x415, &x429);
  { uint32_t x432; uint8_t x433 = _addcarryx_u32(0x0, x386, x402, &x432);
  { uint32_t x435; uint8_t x436 = _addcarryx_u32(x433, x389, x417, &x435);
  { uint32_t x438; uint8_t x439 = _addcarryx_u32(x436, x392, x420, &x438);
  { uint32_t x441; uint8_t x442 = _addcarryx_u32(x439, x395, x423, &x441);
  { uint32_t x444; uint8_t x445 = _addcarryx_u32(x442, x398, x426, &x444);
  { uint32_t x447; uint8_t x448 = _addcarryx_u32(x445, x400, x429, &x447);
  { uint32_t _;  uint32_t x450 = _mulx_u32(x432, 0xaaaaaaab, &_);
  { uint32_t x454;  uint32_t x453 = _mulx_u32(x450, 0xfffffffd, &x454);
  { uint32_t x457;  uint32_t x456 = _mulx_u32(x450, 0xffffffff, &x457);
  { uint32_t x460;  uint32_t x459 = _mulx_u32(x450, 0xffffffff, &x460);
  { uint32_t x463;  uint32_t x462 = _mulx_u32(x450, 0xffffffff, &x463);
  { uint32_t x466;  uint32_t x465 = _mulx_u32(x450, 0x3fffff, &x466);
  { uint32_t x468; uint8_t x469 = _addcarryx_u32(0x0, x454, x456, &x468);
  { uint32_t x471; uint8_t x472 = _addcarryx_u32(x469, x457, x459, &x471);
  { uint32_t x474; uint8_t x475 = _addcarryx_u32(x472, x460, x462, &x474);
  { uint32_t x477; uint8_t x478 = _addcarryx_u32(x475, x463, x465, &x477);
  { uint32_t x480; uint8_t _ = _addcarryx_u32(0x0, x478, x466, &x480);
  { uint32_t _; uint8_t x484 = _addcarryx_u32(0x0, x432, x453, &_);
  { uint32_t x486; uint8_t x487 = _addcarryx_u32(x484, x435, x468, &x486);
  { uint32_t x489; uint8_t x490 = _addcarryx_u32(x487, x438, x471, &x489);
  { uint32_t x492; uint8_t x493 = _addcarryx_u32(x490, x441, x474, &x492);
  { uint32_t x495; uint8_t x496 = _addcarryx_u32(x493, x444, x477, &x495);
  { uint32_t x498; uint8_t x499 = _addcarryx_u32(x496, x447, x480, &x498);
  { uint8_t x500 = (x499 + x448);
  { uint32_t x502; uint8_t x503 = _subborrow_u32(0x0, x486, 0xfffffffd, &x502);
  { uint32_t x505; uint8_t x506 = _subborrow_u32(x503, x489, 0xffffffff, &x505);
  { uint32_t x508; uint8_t x509 = _subborrow_u32(x506, x492, 0xffffffff, &x508);
  { uint32_t x511; uint8_t x512 = _subborrow_u32(x509, x495, 0xffffffff, &x511);
  { uint32_t x514; uint8_t x515 = _subborrow_u32(x512, x498, 0x3fffff, &x514);
  { uint32_t _; uint8_t x518 = _subborrow_u32(x515, x500, 0x0, &_);
  { uint32_t x519 = cmovznz32(x518, x514, x498);
  { uint32_t x520 = cmovznz32(x518, x511, x495);
  { uint32_t x521 = cmovznz32(x518, x508, x492);
  { uint32_t x522 = cmovznz32(x518, x505, x489);
  { uint32_t x523 = cmovznz32(x518, x502, x486);
  out[0] = x523;
  out[1] = x522;
  out[2] = x521;
  out[3] = x520;
  out[4] = x519;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
