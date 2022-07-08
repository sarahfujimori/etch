// Generated by the Tensor Algebra Compiler (tensor-compiler.org)

num ttv_compute() {
  num out_val = 0.0;

  for (int32_t iC = C1_pos[0]; iC < C1_pos[1]; iC++) {
    for (int32_t jC = C2_pos[iC]; jC < C2_pos[(iC + 1)]; jC++) {
      int32_t kC = C3_pos[jC];
      int32_t pC3_end = C3_pos[(jC + 1)];
      int32_t kV = V1_pos[0];
      int32_t pV1_end = V1_pos[1];

      while (kC < pC3_end && kV < pV1_end) {
        int32_t kC0 = C3_crd[kC];
        int32_t kV0 = V1_crd[kV];
        int32_t k = TACO_MIN(kC0,kV0);
        if (kC0 == k && kV0 == k) {
          out_val += C_vals[kC] * V_vals[kV];
        }
        kC += (int32_t)(kC0 == k);
        kV += (int32_t)(kV0 == k);
      }
    }
  }

  out_vals[0] = out_val;
  return out_val;
}
