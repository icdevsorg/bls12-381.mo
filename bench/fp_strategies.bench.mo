import Bench "mo:bench";
import Int "mo:core/Int";
import Nat "mo:core/Nat";

module {

  // ═══════════════════════════════════════════════════
  //  Constants
  // ═══════════════════════════════════════════════════

  let P_INT : Int = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787;
  let P_NAT : Nat = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787;

  // Precomputed (P+1)/4 for sqrt
  let FP_P_PLUS_1_OVER_4 : Nat = 1000602388805416848354447456433976039139220704984751971333014534031007912622709466110671907282253916009473568139947;

  // Two test values (typical BLS12-381 field elements)
  let A_INT : Int = 1234567890123456789012345678901234567890123456789012345678901234567890;
  let B_INT : Int = 3876543210987654321098765432109876543210987654321098765432109876543210;
  let A_NAT : Nat = 1234567890123456789012345678901234567890123456789012345678901234567890;
  let B_NAT : Nat = 3876543210987654321098765432109876543210987654321098765432109876543210;

  // ═══════════════════════════════════════════════════
  //  Strategy 1: CURRENT — Int with fp_mod(a%P, sign check)
  // ═══════════════════════════════════════════════════

  func int_mod(a : Int) : Int {
    let r = a % P_INT;
    if (r < 0) { r + P_INT } else { r };
  };

  func int_add(a : Int, b : Int) : Int {
    int_mod(a + b);
  };

  func int_sub(a : Int, b : Int) : Int {
    int_mod(a - b);
  };

  func int_mul(a : Int, b : Int) : Int {
    int_mod(a * b);
  };

  func int_neg(a : Int) : Int {
    if (int_mod(a) == 0) { 0 } else { P_INT - int_mod(a) };
  };

  // Extended GCD inverse
  func int_inv(a : Int) : Int {
    if (a == 0) return 0;
    var lm : Int = 1;
    var hm : Int = 0;
    var low = int_mod(a);
    var high = P_INT;
    while (low > 1) {
      let ratio = high / low;
      let nm = hm - lm * ratio;
      let nw = high - low * ratio;
      hm := lm;
      lm := nm;
      high := low;
      low := nw;
    };
    int_mod(lm);
  };

  func int_pow(base_ : Int, exp_ : Nat) : Int {
    var result : Int = 1;
    var b = int_mod(base_);
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) {
        result := int_mul(result, b);
      };
      b := int_mul(b, b);
      e := e / 2;
    };
    result;
  };

  // ═══════════════════════════════════════════════════
  //  Strategy 2: NAT — pure Nat, guarded subtraction
  // ═══════════════════════════════════════════════════

  func nat_mod(a : Nat) : Nat {
    a % P_NAT;
  };

  func nat_add(a : Nat, b : Nat) : Nat {
    (a + b) % P_NAT;
  };

  func nat_sub(a : Nat, b : Nat) : Nat {
    // Both a, b should be in [0, P). So a + P - b is always >= 0
    if (a >= b) { (a - b) % P_NAT } else { (P_NAT - b + a) % P_NAT };
  };

  func nat_mul(a : Nat, b : Nat) : Nat {
    (a * b) % P_NAT;
  };

  func nat_neg(a : Nat) : Nat {
    let am = a % P_NAT;
    if (am == 0) { 0 } else { P_NAT - am };
  };

  // Fermat's little theorem inverse: a^(P-2) mod P
  func nat_inv(a : Nat) : Nat {
    if (a == 0) return 0;
    nat_pow(a, P_NAT - 2);
  };

  func nat_pow(base_ : Nat, exp_ : Nat) : Nat {
    var result : Nat = 1;
    var b = base_ % P_NAT;
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) {
        result := nat_mul(result, b);
      };
      b := nat_mul(b, b);
      e := e / 2;
    };
    result;
  };

  // ═══════════════════════════════════════════════════
  //  Strategy 3: NAT + conditional subtract (no mod for add/sub)
  // ═══════════════════════════════════════════════════

  // For reduced inputs in [0, P), add/sub can avoid expensive % P
  func natcs_add(a : Nat, b : Nat) : Nat {
    let s = a + b;
    if (s >= P_NAT) { s - P_NAT } else { s };
  };

  func natcs_sub(a : Nat, b : Nat) : Nat {
    if (a >= b) { a - b } else { P_NAT + a - b };
  };

  // mul still needs % P since product can be >> P
  func natcs_mul(a : Nat, b : Nat) : Nat {
    (a * b) % P_NAT;
  };

  func natcs_neg(a : Nat) : Nat {
    if (a == 0) { 0 } else { P_NAT - a };
  };

  func natcs_inv(a : Nat) : Nat {
    if (a == 0) return 0;
    natcs_pow(a, P_NAT - 2);
  };

  func natcs_pow(base_ : Nat, exp_ : Nat) : Nat {
    var result : Nat = 1;
    var b = base_ % P_NAT;
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) {
        result := natcs_mul(result, b);
      };
      b := natcs_mul(b, b);
      e := e / 2;
    };
    result;
  };

  // ═══════════════════════════════════════════════════
  //  Strategy 4: INT but Fermat inverse (instead of GCD)
  // ═══════════════════════════════════════════════════

  func int_fermat_inv(a : Int) : Int {
    if (a == 0) return 0;
    int_pow(a, P_NAT - 2);
  };

  // ═══════════════════════════════════════════════════
  //  Strategy 5: Fp2 comparisons — Karatsuba vs schoolbook
  //
  //  schoolbook: fp2_mul = 4 fp_mul + 2 fp_add/sub
  //  current:    fp2_mul = 3 fp_mul + 5 fp_add/sub (Karatsuba-like)
  // ═══════════════════════════════════════════════════

  // Current fp2_mul using Karatsuba-like (3 multiplies)
  func int_fp2_mul_karatsuba(a0 : Int, a1 : Int, b0 : Int, b1 : Int) : (Int, Int) {
    let t0 = int_mul(a0, b0);
    let t1 = int_mul(a1, b1);
    (int_sub(t0, t1), int_sub(int_mul(int_add(a0, a1), int_add(b0, b1)), int_add(t0, t1)));
  };

  // Schoolbook fp2_mul (4 multiplies)
  func int_fp2_mul_schoolbook(a0 : Int, a1 : Int, b0 : Int, b1 : Int) : (Int, Int) {
    (int_sub(int_mul(a0, b0), int_mul(a1, b1)),
     int_add(int_mul(a0, b1), int_mul(a1, b0)));
  };

  // Same but with Nat
  func nat_fp2_mul_karatsuba(a0 : Nat, a1 : Nat, b0 : Nat, b1 : Nat) : (Nat, Nat) {
    let t0 = nat_mul(a0, b0);
    let t1 = nat_mul(a1, b1);
    (nat_sub(t0, t1), nat_sub(nat_mul(nat_add(a0, a1), nat_add(b0, b1)), nat_add(t0, t1)));
  };

  func natcs_fp2_mul_karatsuba(a0 : Nat, a1 : Nat, b0 : Nat, b1 : Nat) : (Nat, Nat) {
    let t0 = natcs_mul(a0, b0);
    let t1 = natcs_mul(a1, b1);
    (natcs_sub(t0, t1), natcs_sub(natcs_mul(natcs_add(a0, a1), natcs_add(b0, b1)), natcs_add(t0, t1)));
  };

  // ═══════════════════════════════════════════════════
  //  Strategy 6: Nat GCD inverse (track signs manually)
  // ═══════════════════════════════════════════════════

  // Extended GCD using Nat with explicit sign tracking
  func nat_gcd_inv(a : Nat) : Nat {
    if (a == 0) return 0;
    var lm : Nat = 1;
    var lm_neg : Bool = false;
    var hm : Nat = 0;
    var hm_neg : Bool = false;
    var low = a % P_NAT;
    var high = P_NAT;
    while (low > 1) {
      let ratio = high / low;
      let prod = lm * ratio;
      // nm = hm - lm * ratio (signed)
      let (nm, nm_neg) = if (hm_neg == lm_neg) {
        // same sign: result = |hm| - prod, sign depends on comparison
        if (hm >= prod) { (hm - prod, hm_neg) }
        else { (prod - hm, not hm_neg) };
      } else {
        // different signs: result = |hm| + prod, sign = hm's sign
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
    if (lm_neg) { P_NAT - (lm % P_NAT) } else { lm % P_NAT };
  };

  // ═══════════════════════════════════════════════════
  //  Benchmark
  // ═══════════════════════════════════════════════════

  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Fp Strategy Comparison");
    bench.description("Compare Int vs Nat vs conditional-subtract implementations for BLS12-381 field arithmetic");
    bench.cols(["1_op"]);
    bench.rows([
      // Addition
      "add_int",
      "add_nat",
      "add_natcs",
      // Subtraction
      "sub_int",
      "sub_nat",
      "sub_natcs",
      // Multiplication
      "mul_int",
      "mul_nat",
      // Negation
      "neg_int",
      "neg_nat",
      "neg_natcs",
      // Inversion
      "inv_int_gcd",
      "inv_int_fermat",
      "inv_nat_fermat",
      "inv_nat_gcd",
      // fp2_mul strategies
      "fp2_mul_int_karatsuba",
      "fp2_mul_int_schoolbook",
      "fp2_mul_nat_karatsuba",
      "fp2_mul_natcs_karatsuba",
    ]);

    bench.runner(func(row, _col) {
      switch(row) {
        // === Addition ===
        case("add_int") {
          ignore int_add(A_INT, B_INT);
        };
        case("add_nat") {
          ignore nat_add(A_NAT, B_NAT);
        };
        case("add_natcs") {
          ignore natcs_add(A_NAT, B_NAT);
        };

        // === Subtraction ===
        case("sub_int") {
          ignore int_sub(A_INT, B_INT);
        };
        case("sub_nat") {
          ignore nat_sub(A_NAT, B_NAT);
        };
        case("sub_natcs") {
          ignore natcs_sub(A_NAT, B_NAT);
        };

        // === Multiplication ===
        case("mul_int") {
          ignore int_mul(A_INT, B_INT);
        };
        case("mul_nat") {
          ignore nat_mul(A_NAT, B_NAT);
        };

        // === Negation ===
        case("neg_int") {
          ignore int_neg(A_INT);
        };
        case("neg_nat") {
          ignore nat_neg(A_NAT);
        };
        case("neg_natcs") {
          ignore natcs_neg(A_NAT);
        };

        // === Inversion ===
        case("inv_int_gcd") {
          ignore int_inv(A_INT);
        };
        case("inv_int_fermat") {
          ignore int_fermat_inv(A_INT);
        };
        case("inv_nat_fermat") {
          ignore nat_inv(A_NAT);
        };
        case("inv_nat_gcd") {
          ignore nat_gcd_inv(A_NAT);
        };

        // === Fp2 mul strategies ===
        case("fp2_mul_int_karatsuba") {
          ignore int_fp2_mul_karatsuba(A_INT, B_INT, B_INT, A_INT);
        };
        case("fp2_mul_int_schoolbook") {
          ignore int_fp2_mul_schoolbook(A_INT, B_INT, B_INT, A_INT);
        };
        case("fp2_mul_nat_karatsuba") {
          ignore nat_fp2_mul_karatsuba(A_NAT, B_NAT, B_NAT, A_NAT);
        };
        case("fp2_mul_natcs_karatsuba") {
          ignore natcs_fp2_mul_karatsuba(A_NAT, B_NAT, B_NAT, A_NAT);
        };

        case(_) {};
      };
    });

    bench;
  };
};
