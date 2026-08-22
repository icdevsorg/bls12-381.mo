import Bench "mo:bench";
import Nat64 "mo:base/Nat64";
import CoreNat "mo:core/Nat";

module {

  // ═══════════════════════════════════════════════════
  //  BLS12-381 constants
  // ═══════════════════════════════════════════════════

  let P : Nat = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787;
  let POW64 : Nat = 0x10000000000000000; // 2^64

  // (P+1)/4 — the exponent used in fp_sqrt (381 bits)
  let FP_SQRT_EXP : Nat = 1000602388805416848354447456433976039139220704984751971333014534031007912622709466110671907282253916009473568139947;

  // P-2 — the exponent used in fp_inv via Fermat (381 bits)
  let FP_INV_EXP : Nat = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785;

  // ═══════════════════════════════════════════════════
  //  Fp arithmetic (same as lib.mo)
  // ═══════════════════════════════════════════════════

  func fp_mul(a : Nat, b : Nat) : Nat { (a * b) % P };

  func fp_add(a : Nat, b : Nat) : Nat {
    let s = a + b;
    if (s >= P) { s - P } else { s };
  };

  func fp_sub(a : Nat, b : Nat) : Nat {
    if (a >= b) { a - b } else { P + a - b };
  };

  // ═══════════════════════════════════════════════════
  //  Strategy 1: Current fp_pow — uses e / 2 (bignum division)
  // ═══════════════════════════════════════════════════

  func fp_pow_nat(base_ : Nat, exp_ : Nat) : Nat {
    var result : Nat = 1;
    var b = base_ % P;
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) {
        result := fp_mul(result, b);
      };
      b := fp_mul(b, b);
      e := e / 2;
    };
    result;
  };

  // ═══════════════════════════════════════════════════
  //  Strategy 2: fp_pow with Nat64 6-limb bit scanning
  //  (BLS12-381 needs 6 limbs for 384-bit field)
  // ═══════════════════════════════════════════════════

  func fp_pow_limb6(base_ : Nat, exp_ : Nat) : Nat {
    var result : Nat = 1;
    var b = base_ % P;
    // Convert exponent to 6 × Nat64 limbs
    var s0 = Nat64.fromNat(exp_ % POW64);
    var s1 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 64) % POW64);
    var s2 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 128) % POW64);
    var s3 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 192) % POW64);
    var s4 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 256) % POW64);
    var s5 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 320) % POW64);
    while (s0 != 0 or s1 != 0 or s2 != 0 or s3 != 0 or s4 != 0 or s5 != 0) {
      if ((s0 & 1) == 1) {
        result := fp_mul(result, b);
      };
      b := fp_mul(b, b);
      // Right shift 384-bit value by 1
      s0 := (s0 >> 1) | ((s1 & 1) << 63);
      s1 := (s1 >> 1) | ((s2 & 1) << 63);
      s2 := (s2 >> 1) | ((s3 & 1) << 63);
      s3 := (s3 >> 1) | ((s4 & 1) << 63);
      s4 := (s4 >> 1) | ((s5 & 1) << 63);
      s5 := s5 >> 1;
    };
    result;
  };

  // ═══════════════════════════════════════════════════
  //  Bit-scanning only (no multiplications) to isolate
  //  the overhead of bignum e/2 vs Nat64 limb shifts
  // ═══════════════════════════════════════════════════

  func bitcount_nat(exp_ : Nat) : Nat {
    var count : Nat = 0;
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) { count += 1 };
      e := e / 2;
    };
    count;
  };

  func bitcount_limb6(exp_ : Nat) : Nat {
    var count : Nat = 0;
    var s0 = Nat64.fromNat(exp_ % POW64);
    var s1 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 64) % POW64);
    var s2 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 128) % POW64);
    var s3 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 192) % POW64);
    var s4 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 256) % POW64);
    var s5 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 320) % POW64);
    while (s0 != 0 or s1 != 0 or s2 != 0 or s3 != 0 or s4 != 0 or s5 != 0) {
      if ((s0 & 1) == 1) { count += 1 };
      s0 := (s0 >> 1) | ((s1 & 1) << 63);
      s1 := (s1 >> 1) | ((s2 & 1) << 63);
      s2 := (s2 >> 1) | ((s3 & 1) << 63);
      s3 := (s3 >> 1) | ((s4 & 1) << 63);
      s4 := (s4 >> 1) | ((s5 & 1) << 63);
      s5 := s5 >> 1;
    };
    count;
  };

  // ═══════════════════════════════════════════════════
  //  Fp2 pow with Nat64 6-limb bit scanning
  // ═══════════════════════════════════════════════════

  type Fp2 = (Nat, Nat);

  func fp2_mul(a : Fp2, b : Fp2) : Fp2 {
    let t0 = fp_mul(a.0, b.0);
    let t1 = fp_mul(a.1, b.1);
    (fp_sub(t0, t1), fp_sub(fp_mul(fp_add(a.0, a.1), fp_add(b.0, b.1)), fp_add(t0, t1)));
  };

  func fp2_sq(a : Fp2) : Fp2 {
    let t = fp_mul(a.0, a.1);
    (fp_mul(fp_add(a.0, a.1), fp_sub(a.0, a.1)), fp_add(t, t));
  };

  func fp2_pow_nat(base_ : Fp2, exp_ : Nat) : Fp2 {
    var result : Fp2 = (1, 0);
    var b = base_;
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) { result := fp2_mul(result, b) };
      b := fp2_sq(b);
      e := e / 2;
    };
    result;
  };

  func fp2_pow_limb6(base_ : Fp2, exp_ : Nat) : Fp2 {
    var result : Fp2 = (1, 0);
    var b = base_;
    var s0 = Nat64.fromNat(exp_ % POW64);
    var s1 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 64) % POW64);
    var s2 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 128) % POW64);
    var s3 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 192) % POW64);
    var s4 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 256) % POW64);
    var s5 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 320) % POW64);
    while (s0 != 0 or s1 != 0 or s2 != 0 or s3 != 0 or s4 != 0 or s5 != 0) {
      if ((s0 & 1) == 1) { result := fp2_mul(result, b) };
      b := fp2_sq(b);
      s0 := (s0 >> 1) | ((s1 & 1) << 63);
      s1 := (s1 >> 1) | ((s2 & 1) << 63);
      s2 := (s2 >> 1) | ((s3 & 1) << 63);
      s3 := (s3 >> 1) | ((s4 & 1) << 63);
      s4 := (s4 >> 1) | ((s5 & 1) << 63);
      s5 := s5 >> 1;
    };
    result;
  };

  // ═══════════════════════════════════════════════════
  //  Benchmark
  // ═══════════════════════════════════════════════════

  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("BLS12-381 Nat64 Limb Bit-Scanning for fp_pow");
    bench.description("Compare e/2 bignum division vs Nat64 6-limb shifts for exponent scanning in pow functions");
    bench.cols(["1_op"]);
    bench.rows([
      // Isolated bit scanning cost (381-bit exponent)
      "bitcount_nat_381bit",
      "bitcount_limb6_381bit",

      // Full fp_pow with fp_sqrt exponent (381 bits)
      "fp_pow_nat_sqrt_exp",
      "fp_pow_limb6_sqrt_exp",

      // Full fp_pow with small exponent (17 bits)
      "fp_pow_nat_small",
      "fp_pow_limb6_small",

      // Fp2 pow with sqrt-related exponent
      "fp2_pow_nat_381bit",
      "fp2_pow_limb6_381bit",
    ]);

    let test_val : Nat = 1234567890123456789012345678901234567890123456789012345678901234567890;
    let fp2_val : Fp2 = (test_val, 9876543210987654321098765432109876543210987654321098765432109876543210);

    bench.runner(func(row, _col) {
      switch(row) {
        // === Isolated bit scanning ===
        case("bitcount_nat_381bit") {
          ignore bitcount_nat(FP_SQRT_EXP);
        };
        case("bitcount_limb6_381bit") {
          ignore bitcount_limb6(FP_SQRT_EXP);
        };

        // === Full fp_pow with sqrt exponent ===
        case("fp_pow_nat_sqrt_exp") {
          ignore fp_pow_nat(test_val, FP_SQRT_EXP);
        };
        case("fp_pow_limb6_sqrt_exp") {
          ignore fp_pow_limb6(test_val, FP_SQRT_EXP);
        };

        // === Small exponent (65537 = 2^16+1) ===
        case("fp_pow_nat_small") {
          ignore fp_pow_nat(test_val, 65537);
        };
        case("fp_pow_limb6_small") {
          ignore fp_pow_limb6(test_val, 65537);
        };

        // === Fp2 pow ===
        case("fp2_pow_nat_381bit") {
          ignore fp2_pow_nat(fp2_val, FP_SQRT_EXP);
        };
        case("fp2_pow_limb6_381bit") {
          ignore fp2_pow_limb6(fp2_val, FP_SQRT_EXP);
        };

        case(_) {};
      };
    });

    bench;
  };
};
