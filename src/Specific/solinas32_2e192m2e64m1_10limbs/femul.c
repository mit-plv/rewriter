static void femul(uint32_t out[10], const uint32_t in1[10], const uint32_t in2[10]) {
  { const uint32_t x20 = in1[9];
  { const uint32_t x21 = in1[8];
  { const uint32_t x19 = in1[7];
  { const uint32_t x17 = in1[6];
  { const uint32_t x15 = in1[5];
  { const uint32_t x13 = in1[4];
  { const uint32_t x11 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x38 = in2[9];
  { const uint32_t x39 = in2[8];
  { const uint32_t x37 = in2[7];
  { const uint32_t x35 = in2[6];
  { const uint32_t x33 = in2[5];
  { const uint32_t x31 = in2[4];
  { const uint32_t x29 = in2[3];
  { const uint32_t x27 = in2[2];
  { const uint32_t x25 = in2[1];
  { const uint32_t x23 = in2[0];
  { ℤ x40 = ((((uint64_t)x5 * x38) + ((0x2 * ((uint64_t)x7 * x39)) + ((0x2 * ((uint64_t)x9 * x37)) + ((0x2 * ((uint64_t)x11 * x35)) + (((uint64_t)x13 * x33) + (((uint64_t)x15 * x31) + ((0x2 * ((uint64_t)x17 * x29)) + ((0x2 * ((uint64_t)x19 * x27)) + ((0x2 * ((uint64_t)x21 * x25)) + ((uint64_t)x20 * x23)))))))))) +ℤ ((0x80 * (((uint64_t)x19 * x38) + (((uint64_t)x21 * x39) + ((uint64_t)x20 * x37)))) +ℤ ((0x4000000 *ℤ (((uint64_t)x21 * x38) + ((uint64_t)x20 * x39))) +ℤ (0x200000000000 *ℤ ((uint64_t)x20 * x38)))));
  { uint64_t x41 = ((((uint64_t)x5 * x39) + ((0x2 * ((uint64_t)x7 * x37)) + ((0x2 * ((uint64_t)x9 * x35)) + (((uint64_t)x11 * x33) + (((uint64_t)x13 * x31) + (((uint64_t)x15 * x29) + ((0x2 * ((uint64_t)x17 * x27)) + ((0x2 * ((uint64_t)x19 * x25)) + ((uint64_t)x21 * x23))))))))) + (((uint64_t)x20 * x38) + (0x40 * ((0x2 * ((uint64_t)x17 * x38)) + ((0x2 * ((uint64_t)x19 * x39)) + ((0x2 * ((uint64_t)x21 * x37)) + (0x2 * ((uint64_t)x20 * x35))))))));
  { uint64_t x42 = ((((uint64_t)x5 * x37) + ((0x2 * ((uint64_t)x7 * x35)) + (((uint64_t)x9 * x33) + (((uint64_t)x11 * x31) + (((uint64_t)x13 * x29) + (((uint64_t)x15 * x27) + ((0x2 * ((uint64_t)x17 * x25)) + ((uint64_t)x19 * x23)))))))) + ((((uint64_t)x21 * x38) + ((uint64_t)x20 * x39)) + (0x40 * (((uint64_t)x15 * x38) + ((0x2 * ((uint64_t)x17 * x39)) + ((0x2 * ((uint64_t)x19 * x37)) + ((0x2 * ((uint64_t)x21 * x35)) + ((uint64_t)x20 * x33))))))));
  { uint64_t x43 = ((((uint64_t)x5 * x35) + (((uint64_t)x7 * x33) + (((uint64_t)x9 * x31) + (((uint64_t)x11 * x29) + (((uint64_t)x13 * x27) + (((uint64_t)x15 * x25) + ((uint64_t)x17 * x23))))))) + ((((uint64_t)x19 * x38) + (((uint64_t)x21 * x39) + ((uint64_t)x20 * x37))) + (0x40 * (((uint64_t)x13 * x38) + (((uint64_t)x15 * x39) + ((0x2 * ((uint64_t)x17 * x37)) + ((0x2 * ((uint64_t)x19 * x35)) + (((uint64_t)x21 * x33) + ((uint64_t)x20 * x31)))))))));
  { uint64_t x44 = ((((uint64_t)x5 * x33) + ((0x2 * ((uint64_t)x7 * x31)) + ((0x2 * ((uint64_t)x9 * x29)) + ((0x2 * ((uint64_t)x11 * x27)) + ((0x2 * ((uint64_t)x13 * x25)) + ((uint64_t)x15 * x23)))))) + (((0x2 * ((uint64_t)x17 * x38)) + ((0x2 * ((uint64_t)x19 * x39)) + ((0x2 * ((uint64_t)x21 * x37)) + (0x2 * ((uint64_t)x20 * x35))))) + (0x80 * (((uint64_t)x11 * x38) + (((uint64_t)x13 * x39) + (((uint64_t)x15 * x37) + ((0x2 * ((uint64_t)x17 * x35)) + (((uint64_t)x19 * x33) + (((uint64_t)x21 * x31) + ((uint64_t)x20 * x29))))))))));
  { uint64_t x45 = ((((uint64_t)x5 * x31) + ((0x2 * ((uint64_t)x7 * x29)) + ((0x2 * ((uint64_t)x9 * x27)) + ((0x2 * ((uint64_t)x11 * x25)) + ((uint64_t)x13 * x23))))) + ((((uint64_t)x15 * x38) + ((0x2 * ((uint64_t)x17 * x39)) + ((0x2 * ((uint64_t)x19 * x37)) + ((0x2 * ((uint64_t)x21 * x35)) + ((uint64_t)x20 * x33))))) + (0x80 * (((uint64_t)x9 * x38) + (((uint64_t)x11 * x39) + (((uint64_t)x13 * x37) + (((uint64_t)x15 * x35) + (((uint64_t)x17 * x33) + (((uint64_t)x19 * x31) + (((uint64_t)x21 * x29) + ((uint64_t)x20 * x27)))))))))));
  { uint64_t x46 = ((((uint64_t)x5 * x29) + ((0x2 * ((uint64_t)x7 * x27)) + ((0x2 * ((uint64_t)x9 * x25)) + ((uint64_t)x11 * x23)))) + ((((uint64_t)x13 * x38) + (((uint64_t)x15 * x39) + ((0x2 * ((uint64_t)x17 * x37)) + ((0x2 * ((uint64_t)x19 * x35)) + (((uint64_t)x21 * x33) + ((uint64_t)x20 * x31)))))) + (0x40 * ((0x2 * ((uint64_t)x7 * x38)) + ((0x2 * ((uint64_t)x9 * x39)) + ((0x2 * ((uint64_t)x11 * x37)) + ((0x2 * ((uint64_t)x13 * x35)) + (((uint64_t)x15 * x33) + ((0x2 * ((uint64_t)x17 * x31)) + ((0x2 * ((uint64_t)x19 * x29)) + ((0x2 * ((uint64_t)x21 * x27)) + (0x2 * ((uint64_t)x20 * x25)))))))))))));
  { uint64_t x47 = ((((uint64_t)x5 * x27) + ((0x2 * ((uint64_t)x7 * x25)) + ((uint64_t)x9 * x23))) + (((uint64_t)x11 * x38) + (((uint64_t)x13 * x39) + (((uint64_t)x15 * x37) + ((0x2 * ((uint64_t)x17 * x35)) + (((uint64_t)x19 * x33) + (((uint64_t)x21 * x31) + ((uint64_t)x20 * x29))))))));
  { uint64_t x48 = ((((uint64_t)x5 * x25) + ((uint64_t)x7 * x23)) + (((uint64_t)x9 * x38) + (((uint64_t)x11 * x39) + (((uint64_t)x13 * x37) + (((uint64_t)x15 * x35) + (((uint64_t)x17 * x33) + (((uint64_t)x19 * x31) + (((uint64_t)x21 * x29) + ((uint64_t)x20 * x27)))))))));
  { uint64_t x49 = (((uint64_t)x5 * x23) + ((0x2 * ((uint64_t)x7 * x38)) + ((0x2 * ((uint64_t)x9 * x39)) + ((0x2 * ((uint64_t)x11 * x37)) + ((0x2 * ((uint64_t)x13 * x35)) + (((uint64_t)x15 * x33) + ((0x2 * ((uint64_t)x17 * x31)) + ((0x2 * ((uint64_t)x19 * x29)) + ((0x2 * ((uint64_t)x21 * x27)) + (0x2 * ((uint64_t)x20 * x25)))))))))));
  { uint32_t x50 = (uint32_t) (x47 >> 0x13);
  { uint32_t x51 = ((uint32_t)x47 & 0x7ffff);
  { ℤ x52 = (x40 >>ℤ 0x13);
  { uint32_t x53 = (x40 & 0x7ffff);
  { ℤ x54 = ((0x80000 *ℤ x52) +ℤ x53);
  { ℤ x55 = (x54 >>ℤ 0x13);
  { uint32_t x56 = (x54 & 0x7ffff);
  { ℤ x57 = ((x50 + x46) +ℤ (0x40 *ℤ x55));
  { uint64_t x58 = (x57 >> 0x13);
  { uint32_t x59 = (x57 & 0x7ffff);
  { ℤ x60 = (x49 +ℤ x55);
  { uint64_t x61 = (x60 >> 0x14);
  { uint32_t x62 = (x60 & 0xfffff);
  { uint64_t x63 = (x58 + x45);
  { uint64_t x64 = (x63 >> 0x13);
  { uint32_t x65 = ((uint32_t)x63 & 0x7ffff);
  { uint64_t x66 = (x61 + x48);
  { uint32_t x67 = (uint32_t) (x66 >> 0x13);
  { uint32_t x68 = ((uint32_t)x66 & 0x7ffff);
  { uint64_t x69 = (x64 + x44);
  { uint32_t x70 = (uint32_t) (x69 >> 0x14);
  { uint32_t x71 = ((uint32_t)x69 & 0xfffff);
  { uint32_t x72 = (x67 + x51);
  { uint32_t x73 = (x72 >> 0x13);
  { uint32_t x74 = (x72 & 0x7ffff);
  { uint64_t x75 = (x70 + x43);
  { uint32_t x76 = (uint32_t) (x75 >> 0x13);
  { uint32_t x77 = ((uint32_t)x75 & 0x7ffff);
  { uint64_t x78 = (x76 + x42);
  { uint32_t x79 = (uint32_t) (x78 >> 0x13);
  { uint32_t x80 = ((uint32_t)x78 & 0x7ffff);
  { uint64_t x81 = (x79 + x41);
  { uint32_t x82 = (uint32_t) (x81 >> 0x13);
  { uint32_t x83 = ((uint32_t)x81 & 0x7ffff);
  { uint32_t x84 = (x82 + x56);
  { uint32_t x85 = (x84 >> 0x13);
  { uint32_t x86 = (x84 & 0x7ffff);
  { uint32_t x87 = ((0x80000 * x85) + x86);
  { uint32_t x88 = (x87 >> 0x13);
  { uint32_t x89 = (x87 & 0x7ffff);
  { uint32_t x90 = ((x73 + x59) + (0x40 * x88));
  { uint32_t x91 = (x90 >> 0x13);
  { uint32_t x92 = (x90 & 0x7ffff);
  { uint32_t x93 = (x62 + x88);
  { uint32_t x94 = (x93 >> 0x14);
  { uint32_t x95 = (x93 & 0xfffff);
  out[0] = x95;
  out[1] = (x94 + x68);
  out[2] = x74;
  out[3] = x92;
  out[4] = (x91 + x65);
  out[5] = x71;
  out[6] = x77;
  out[7] = x80;
  out[8] = x83;
  out[9] = x89;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}