import Bench "mo:bench";
import FP "../src/fp";
import BLS "../src/lib";

module {

  // ═══════════════════════════════════════════════════
  //  Constants
  // ═══════════════════════════════════════════════════

  let P : Nat = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787;

  // Two typical BLS12-381 field elements (both < P, already reduced)
  let A_NAT : Nat = 1234567890123456789012345678901234567890123456789012345678901234567890;
  let B_NAT : Nat = 3876543210987654321098765432109876543210987654321098765432109876543210;

  // ═══════════════════════════════════════════════════
  //  Nat bignum approach (current lib.mo)
  // ═══════════════════════════════════════════════════

  func nat_fp_mul(a : Nat, b : Nat) : Nat {
    (a * b) % P;
  };

  func nat_fp_add(a : Nat, b : Nat) : Nat {
    let s = a + b;
    if (s >= P) { s - P } else { s };
  };

  func nat_fp_sub(a : Nat, b : Nat) : Nat {
    if (a >= b) { a - b } else { P + a - b };
  };

  func nat_fp_neg(a : Nat) : Nat {
    if (a == 0) { 0 } else { P - a };
  };

  func nat_fp_pow(base_ : Nat, exp_ : Nat) : Nat {
    var result : Nat = 1;
    var b = base_ % P;
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) {
        result := nat_fp_mul(result, b);
      };
      b := nat_fp_mul(b, b);
      e := e / 2;
    };
    result;
  };

  func nat_fp_inv(a : Nat) : Nat {
    if (a == 0) return 0;
    // Extended GCD with sign-tracked Nat
    var lm : Nat = 1;
    var lm_neg : Bool = false;
    var hm : Nat = 0;
    var hm_neg : Bool = false;
    var low = a % P;
    var high = P;
    while (low > 1) {
      let ratio = high / low;
      let prod = lm * ratio;
      let (nm, nm_neg) = if (hm_neg == lm_neg) {
        if (hm >= prod) { (hm - prod, hm_neg) }
        else { (prod - hm, not hm_neg) };
      } else {
        (hm + prod, hm_neg);
      };
      let nw = high - low * ratio;
      hm := lm;
      hm_neg := lm_neg;
      lm := nm;
      lm_neg := nm_neg;
      high := low;
      low := nw;
    };
    if (lm_neg) { P - (lm % P) } else { lm % P };
  };

  // ═══════════════════════════════════════════════════
  //  Fp2 with Nat bignum (current lib.mo approach)
  // ═══════════════════════════════════════════════════

  type Fp2Nat = (Nat, Nat);

  func nat_fp2_mul(a : Fp2Nat, b : Fp2Nat) : Fp2Nat {
    let t0 = nat_fp_mul(a.0, b.0);
    let t1 = nat_fp_mul(a.1, b.1);
    (nat_fp_sub(t0, t1),
     nat_fp_sub(
       nat_fp_mul(nat_fp_add(a.0, a.1), nat_fp_add(b.0, b.1)),
       nat_fp_add(t0, t1)));
  };

  // ═══════════════════════════════════════════════════
  //  Fp2 with Montgomery (what we'd switch to)
  // ═══════════════════════════════════════════════════

  type Fp2Mont = (FP.Fp, FP.Fp);

  func mont_fp2_mul(a : Fp2Mont, b : Fp2Mont) : Fp2Mont {
    let t0 = FP.fp_mul(a.0, b.0);
    let t1 = FP.fp_mul(a.1, b.1);
    (FP.fp_sub(t0, t1),
     FP.fp_sub(
       FP.fp_mul(FP.fp_add(a.0, a.1), FP.fp_add(b.0, b.1)),
       FP.fp_add(t0, t1)));
  };

  // ═══════════════════════════════════════════════════
  //  Benchmark
  // ═══════════════════════════════════════════════════

  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Montgomery (fp.mo) vs Nat Bignum (lib.mo)");
    bench.description("Compare Montgomery CIOS 6×Nat64 vs Nat bignum for BLS12-381 Fp");
    bench.cols(["1_op"]);
    bench.rows([
      "fp_mul_nat",
      "fp_mul_mont",

      "fp_add_nat",
      "fp_add_mont",

      "fp_sub_nat",
      "fp_sub_mont",

      "fp_neg_nat",
      "fp_neg_mont",

      "fp_inv_nat_gcd",
      "fp_inv_mont_fermat",

      "fp_pow_small_nat",
      "fp_pow_small_mont",

      "fp2_mul_nat",
      "fp2_mul_mont",

      "to_mont_cost",
      "from_mont_cost",

      // Higher-level: use lib.mo's actual exported functions
      "lib_fp_mul",
      "lib_fp_inv",
      "lib_fp2_mul",
    ]);

    // Pre-compute Montgomery representations
    let a_mont = FP.nat_to_mont(A_NAT);
    let b_mont = FP.nat_to_mont(B_NAT);

    // Fp2 test values
    let fp2a_nat : Fp2Nat = (A_NAT, B_NAT);
    let fp2b_nat : Fp2Nat = (B_NAT, A_NAT);
    let fp2a_mont : Fp2Mont = (FP.nat_to_mont(A_NAT), FP.nat_to_mont(B_NAT));
    let fp2b_mont : Fp2Mont = (FP.nat_to_mont(B_NAT), FP.nat_to_mont(A_NAT));

    bench.runner(func(row, _col) {
      switch(row) {
        // === fp_mul ===
        case("fp_mul_nat") {
          ignore nat_fp_mul(A_NAT, B_NAT);
        };
        case("fp_mul_mont") {
          ignore FP.fp_mul(a_mont, b_mont);
        };

        // === fp_add ===
        case("fp_add_nat") {
          ignore nat_fp_add(A_NAT, B_NAT);
        };
        case("fp_add_mont") {
          ignore FP.fp_add(a_mont, b_mont);
        };

        // === fp_sub ===
        case("fp_sub_nat") {
          ignore nat_fp_sub(A_NAT, B_NAT);
        };
        case("fp_sub_mont") {
          ignore FP.fp_sub(a_mont, b_mont);
        };

        // === fp_neg ===
        case("fp_neg_nat") {
          ignore nat_fp_neg(A_NAT);
        };
        case("fp_neg_mont") {
          ignore FP.fp_neg(a_mont);
        };

        // === fp_inv ===
        case("fp_inv_nat_gcd") {
          ignore nat_fp_inv(A_NAT);
        };
        case("fp_inv_mont_fermat") {
          ignore FP.fp_inv(a_mont);
        };

        // === fp_pow (small exponent) ===
        case("fp_pow_small_nat") {
          ignore nat_fp_pow(A_NAT, 65537);
        };
        case("fp_pow_small_mont") {
          ignore FP.fp_pow(a_mont, 65537);
        };

        // === fp2_mul ===
        case("fp2_mul_nat") {
          ignore nat_fp2_mul(fp2a_nat, fp2b_nat);
        };
        case("fp2_mul_mont") {
          ignore mont_fp2_mul(fp2a_mont, fp2b_mont);
        };

        // === conversion cost ===
        case("to_mont_cost") {
          ignore FP.nat_to_mont(A_NAT);
        };
        case("from_mont_cost") {
          ignore FP.from_mont(a_mont);
        };

        // === lib.mo actual exported functions (current baseline) ===
        case("lib_fp_mul") {
          ignore BLS.fp_mul(A_NAT, B_NAT);
        };
        case("lib_fp_inv") {
          ignore BLS.fp_inv(A_NAT);
        };
        case("lib_fp2_mul") {
          ignore BLS.fp2_mul((A_NAT, B_NAT), (B_NAT, A_NAT));
        };

        case(_) {};
      };
    });

    bench;
  };
};
