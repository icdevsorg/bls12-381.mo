// Montgomery-form Fp arithmetic for BLS12-381.
// Constants and algorithm structure were checked against @noble/curves 1.9.7.
// See THIRD_PARTY_LICENSES.md for its MIT attribution.
// Field elements stored as 6 × Nat64 limbs in Montgomery representation.
// value_mont = value * R mod P, where R = 2^384.
//
// Montgomery multiplication: mont_mul(aR, bR) = a*b*R mod P
// This avoids expensive division by P — uses REDC instead.

import Nat64 "mo:base/Nat64";
import Nat "mo:base/Nat";
import Prim "mo:⛔";
import Int "mo:base/Int";

module {

  // ══════════════════════════════════════════════════════════════
  //  Types
  // ══════════════════════════════════════════════════════════════

  /// A field element in Montgomery form, stored as 6 little-endian Nat64 limbs.
  /// value = (l0 + l1*2^64 + l2*2^128 + l3*2^192 + l4*2^256 + l5*2^320) represents
  /// the field element value * R^{-1} mod P.
  public type Fp = (Nat64, Nat64, Nat64, Nat64, Nat64, Nat64);

  // ══════════════════════════════════════════════════════════════
  //  Constants
  // ══════════════════════════════════════════════════════════════

  // The BLS12-381 field prime P
  // P = 0x1a0111ea397fe69a_4b1ba7b6434bacd7_64774b84f38512bf_6730d2a0f6b0f624_1eabfffeb153ffff_b9feffffffffaaab
  let P0 : Nat64 = 0xb9feffffffffaaab;
  let P1 : Nat64 = 0x1eabfffeb153ffff;
  let P2 : Nat64 = 0x6730d2a0f6b0f624;
  let P3 : Nat64 = 0x64774b84f38512bf;
  let P4 : Nat64 = 0x4b1ba7b6434bacd7;
  let P5 : Nat64 = 0x1a0111ea397fe69a;

  // N' = -P^{-1} mod 2^64 (for REDC)
  let N_PRIME : Nat64 = 0x89f3fffcfffcfffd;

  /// Montgomery representation of 0
  public let ZERO : Fp = (0, 0, 0, 0, 0, 0);

  /// Montgomery representation of 1 (= R mod P)
  public let ONE : Fp = (
    0x760900000002fffd,
    0xebf4000bc40c0002,
    0x5f48985753c758ba,
    0x77ce585370525745,
    0x5c071a97a256ec6d,
    0x15f65ec3fa80e493
  );

  /// R^2 mod P (used for converting to Montgomery form)
  let R2 : Fp = (
    0xf4df1f341c341746,
    0x0a76e6a609d104f1,
    0x8de5476c4c95b6d5,
    0x67eb88a9939d83c0,
    0x9a793e85b519952d,
    0x11988fe592cae3aa
  );

  /// The prime P as Int (for conversions and fallback)
  public let P_INT : Int = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787;

  // ══════════════════════════════════════════════════════════════
  //  Low-level helpers
  // ══════════════════════════════════════════════════════════════

  let W : Nat = 0x10000000000000000; // 2^64

  /// Wide multiply: a * b -> (lo, hi) where result = lo + hi * 2^64
  func mul_wide(a : Nat64, b : Nat64) : (Nat64, Nat64) {
    let an = Prim.nat64ToNat(a);
    let bn = Prim.nat64ToNat(b);
    let prod = an * bn;
    (Prim.natToNat64(prod % W), Prim.natToNat64(prod / W));
  };

  /// Add with carry: a + b + carry_in -> (sum, carry_out)
  func adc(a : Nat64, b : Nat64, carry : Nat64) : (Nat64, Nat64) {
    let sum = Prim.nat64ToNat(a) + Prim.nat64ToNat(b) + Prim.nat64ToNat(carry);
    (Prim.natToNat64(sum % W), Prim.natToNat64(sum / W));
  };

  /// Subtract with borrow: a - b - borrow_in -> (diff, borrow_out)
  func sbb(a : Nat64, b : Nat64, borrow : Nat64) : (Nat64, Nat64) {
    let an = Prim.nat64ToNat(a);
    let bn = Prim.nat64ToNat(b) + Prim.nat64ToNat(borrow);
    if (an >= bn) {
      (Prim.natToNat64(an - bn), 0);
    } else {
      (Prim.natToNat64(an + W - bn), 1);
    };
  };

  /// Multiply-accumulate: acc + a * b -> (lo, carry)
  func mac(acc : Nat64, a : Nat64, b : Nat64, carry : Nat64) : (Nat64, Nat64) {
    let result = Prim.nat64ToNat(acc) + Prim.nat64ToNat(a) * Prim.nat64ToNat(b) + Prim.nat64ToNat(carry);
    (Prim.natToNat64(result % W), Prim.natToNat64(result / W));
  };

  // ══════════════════════════════════════════════════════════════
  //  Comparison
  // ══════════════════════════════════════════════════════════════

  public func fp_eq(a : Fp, b : Fp) : Bool {
    a.0 == b.0 and a.1 == b.1 and a.2 == b.2 and
    a.3 == b.3 and a.4 == b.4 and a.5 == b.5;
  };

  public func fp_is_zero(a : Fp) : Bool {
    a.0 == 0 and a.1 == 0 and a.2 == 0 and
    a.3 == 0 and a.4 == 0 and a.5 == 0;
  };

  /// Returns true if a >= P (used internally for conditional subtraction)
  func gte_p(a0 : Nat64, a1 : Nat64, a2 : Nat64, a3 : Nat64, a4 : Nat64, a5 : Nat64) : Bool {
    if (a5 > P5) return true;
    if (a5 < P5) return false;
    if (a4 > P4) return true;
    if (a4 < P4) return false;
    if (a3 > P3) return true;
    if (a3 < P3) return false;
    if (a2 > P2) return true;
    if (a2 < P2) return false;
    if (a1 > P1) return true;
    if (a1 < P1) return false;
    a0 >= P0;
  };

  // ══════════════════════════════════════════════════════════════
  //  Addition and subtraction
  // ══════════════════════════════════════════════════════════════

  /// Modular addition: (a + b) mod P
  public func fp_add(a : Fp, b : Fp) : Fp {
    // Add limbs
    let (r0, c0) = adc(a.0, b.0, 0);
    let (r1, c1) = adc(a.1, b.1, c0);
    let (r2, c2) = adc(a.2, b.2, c1);
    let (r3, c3) = adc(a.3, b.3, c2);
    let (r4, c4) = adc(a.4, b.4, c3);
    let (r5, _)  = adc(a.5, b.5, c4);

    // Conditionally subtract P if result >= P
    if (gte_p(r0, r1, r2, r3, r4, r5)) {
      let (s0, b0) = sbb(r0, P0, 0);
      let (s1, b1) = sbb(r1, P1, b0);
      let (s2, b2) = sbb(r2, P2, b1);
      let (s3, b3) = sbb(r3, P3, b2);
      let (s4, b4) = sbb(r4, P4, b3);
      let (s5, _)  = sbb(r5, P5, b4);
      (s0, s1, s2, s3, s4, s5);
    } else {
      (r0, r1, r2, r3, r4, r5);
    };
  };

  /// Modular subtraction: (a - b) mod P
  public func fp_sub(a : Fp, b : Fp) : Fp {
    let (d0, w0) = sbb(a.0, b.0, 0);
    let (d1, w1) = sbb(a.1, b.1, w0);
    let (d2, w2) = sbb(a.2, b.2, w1);
    let (d3, w3) = sbb(a.3, b.3, w2);
    let (d4, w4) = sbb(a.4, b.4, w3);
    let (d5, w5) = sbb(a.5, b.5, w4);

    // If borrow, add P back
    if (w5 != 0) {
      let (r0, c0) = adc(d0, P0, 0);
      let (r1, c1) = adc(d1, P1, c0);
      let (r2, c2) = adc(d2, P2, c1);
      let (r3, c3) = adc(d3, P3, c2);
      let (r4, c4) = adc(d4, P4, c3);
      let (r5, _)  = adc(d5, P5, c4);
      (r0, r1, r2, r3, r4, r5);
    } else {
      (d0, d1, d2, d3, d4, d5);
    };
  };

  /// Modular negation: (-a) mod P
  public func fp_neg(a : Fp) : Fp {
    if (fp_is_zero(a)) return ZERO;
    fp_sub(ZERO, a);
  };

  /// Double: a + a (slightly more efficient than fp_add(a, a))
  public func fp_double(a : Fp) : Fp {
    fp_add(a, a);
  };

  // ══════════════════════════════════════════════════════════════
  //  Montgomery multiplication (REDC)
  // ══════════════════════════════════════════════════════════════

  /// Montgomery multiplication: computes a * b * R^{-1} mod P
  /// If a and b are in Montgomery form (aR, bR), result is (a*b)R mod P.
  public func fp_mul(a : Fp, b : Fp) : Fp {
    // We use the CIOS (Coarsely Integrated Operand Scanning) method.
    // For each limb i of a, we:
    //   1. Multiply a[i] * b and accumulate into t[0..6]
    //   2. Compute m = t[0] * N' mod 2^64
    //   3. Add m * P to t (this makes t[0] = 0)
    //   4. Shift t right by one limb

    var t0 : Nat64 = 0;
    var t1 : Nat64 = 0;
    var t2 : Nat64 = 0;
    var t3 : Nat64 = 0;
    var t4 : Nat64 = 0;
    var t5 : Nat64 = 0;
    var t6 : Nat64 = 0;

    // Round 0: a.0 * b
    var carry : Nat64 = 0;
    let (r0_0, c0_0) = mac(t0, a.0, b.0, 0);
    let (r0_1, c0_1) = mac(t1, a.0, b.1, c0_0);
    let (r0_2, c0_2) = mac(t2, a.0, b.2, c0_1);
    let (r0_3, c0_3) = mac(t3, a.0, b.3, c0_2);
    let (r0_4, c0_4) = mac(t4, a.0, b.4, c0_3);
    let (r0_5, c0_5) = mac(t5, a.0, b.5, c0_4);
    t6 := c0_5;

    // Reduction: m = r0_0 * N' mod 2^64
    var m : Nat64 = r0_0 *% N_PRIME;
    let (_, mc0_0) = mac(r0_0, m, P0, 0);
    let (mr0_1, mc0_1) = mac(r0_1, m, P1, mc0_0);
    let (mr0_2, mc0_2) = mac(r0_2, m, P2, mc0_1);
    let (mr0_3, mc0_3) = mac(r0_3, m, P3, mc0_2);
    let (mr0_4, mc0_4) = mac(r0_4, m, P4, mc0_3);
    let (mr0_5, mc0_5) = mac(r0_5, m, P5, mc0_4);
    let (mr0_6, _) = adc(t6, 0, mc0_5);
    t0 := mr0_1; t1 := mr0_2; t2 := mr0_3; t3 := mr0_4; t4 := mr0_5; t5 := mr0_6;

    // Round 1: a.1 * b
    let (r1_0, c1_0) = mac(t0, a.1, b.0, 0);
    let (r1_1, c1_1) = mac(t1, a.1, b.1, c1_0);
    let (r1_2, c1_2) = mac(t2, a.1, b.2, c1_1);
    let (r1_3, c1_3) = mac(t3, a.1, b.3, c1_2);
    let (r1_4, c1_4) = mac(t4, a.1, b.4, c1_3);
    let (r1_5, c1_5) = mac(t5, a.1, b.5, c1_4);
    t6 := c1_5;

    m := r1_0 *% N_PRIME;
    let (_, mc1_0) = mac(r1_0, m, P0, 0);
    let (mr1_1, mc1_1) = mac(r1_1, m, P1, mc1_0);
    let (mr1_2, mc1_2) = mac(r1_2, m, P2, mc1_1);
    let (mr1_3, mc1_3) = mac(r1_3, m, P3, mc1_2);
    let (mr1_4, mc1_4) = mac(r1_4, m, P4, mc1_3);
    let (mr1_5, mc1_5) = mac(r1_5, m, P5, mc1_4);
    let (mr1_6, _) = adc(t6, 0, mc1_5);
    t0 := mr1_1; t1 := mr1_2; t2 := mr1_3; t3 := mr1_4; t4 := mr1_5; t5 := mr1_6;

    // Round 2: a.2 * b
    let (r2_0, c2_0) = mac(t0, a.2, b.0, 0);
    let (r2_1, c2_1) = mac(t1, a.2, b.1, c2_0);
    let (r2_2, c2_2) = mac(t2, a.2, b.2, c2_1);
    let (r2_3, c2_3) = mac(t3, a.2, b.3, c2_2);
    let (r2_4, c2_4) = mac(t4, a.2, b.4, c2_3);
    let (r2_5, c2_5) = mac(t5, a.2, b.5, c2_4);
    t6 := c2_5;

    m := r2_0 *% N_PRIME;
    let (_, mc2_0) = mac(r2_0, m, P0, 0);
    let (mr2_1, mc2_1) = mac(r2_1, m, P1, mc2_0);
    let (mr2_2, mc2_2) = mac(r2_2, m, P2, mc2_1);
    let (mr2_3, mc2_3) = mac(r2_3, m, P3, mc2_2);
    let (mr2_4, mc2_4) = mac(r2_4, m, P4, mc2_3);
    let (mr2_5, mc2_5) = mac(r2_5, m, P5, mc2_4);
    let (mr2_6, _) = adc(t6, 0, mc2_5);
    t0 := mr2_1; t1 := mr2_2; t2 := mr2_3; t3 := mr2_4; t4 := mr2_5; t5 := mr2_6;

    // Round 3: a.3 * b
    let (r3_0, c3_0) = mac(t0, a.3, b.0, 0);
    let (r3_1, c3_1) = mac(t1, a.3, b.1, c3_0);
    let (r3_2, c3_2) = mac(t2, a.3, b.2, c3_1);
    let (r3_3, c3_3) = mac(t3, a.3, b.3, c3_2);
    let (r3_4, c3_4) = mac(t4, a.3, b.4, c3_3);
    let (r3_5, c3_5) = mac(t5, a.3, b.5, c3_4);
    t6 := c3_5;

    m := r3_0 *% N_PRIME;
    let (_, mc3_0) = mac(r3_0, m, P0, 0);
    let (mr3_1, mc3_1) = mac(r3_1, m, P1, mc3_0);
    let (mr3_2, mc3_2) = mac(r3_2, m, P2, mc3_1);
    let (mr3_3, mc3_3) = mac(r3_3, m, P3, mc3_2);
    let (mr3_4, mc3_4) = mac(r3_4, m, P4, mc3_3);
    let (mr3_5, mc3_5) = mac(r3_5, m, P5, mc3_4);
    let (mr3_6, _) = adc(t6, 0, mc3_5);
    t0 := mr3_1; t1 := mr3_2; t2 := mr3_3; t3 := mr3_4; t4 := mr3_5; t5 := mr3_6;

    // Round 4: a.4 * b
    let (r4_0, c4_0) = mac(t0, a.4, b.0, 0);
    let (r4_1, c4_1) = mac(t1, a.4, b.1, c4_0);
    let (r4_2, c4_2) = mac(t2, a.4, b.2, c4_1);
    let (r4_3, c4_3) = mac(t3, a.4, b.3, c4_2);
    let (r4_4, c4_4) = mac(t4, a.4, b.4, c4_3);
    let (r4_5, c4_5) = mac(t5, a.4, b.5, c4_4);
    t6 := c4_5;

    m := r4_0 *% N_PRIME;
    let (_, mc4_0) = mac(r4_0, m, P0, 0);
    let (mr4_1, mc4_1) = mac(r4_1, m, P1, mc4_0);
    let (mr4_2, mc4_2) = mac(r4_2, m, P2, mc4_1);
    let (mr4_3, mc4_3) = mac(r4_3, m, P3, mc4_2);
    let (mr4_4, mc4_4) = mac(r4_4, m, P4, mc4_3);
    let (mr4_5, mc4_5) = mac(r4_5, m, P5, mc4_4);
    let (mr4_6, _) = adc(t6, 0, mc4_5);
    t0 := mr4_1; t1 := mr4_2; t2 := mr4_3; t3 := mr4_4; t4 := mr4_5; t5 := mr4_6;

    // Round 5: a.5 * b
    let (r5_0, c5_0) = mac(t0, a.5, b.0, 0);
    let (r5_1, c5_1) = mac(t1, a.5, b.1, c5_0);
    let (r5_2, c5_2) = mac(t2, a.5, b.2, c5_1);
    let (r5_3, c5_3) = mac(t3, a.5, b.3, c5_2);
    let (r5_4, c5_4) = mac(t4, a.5, b.4, c5_3);
    let (r5_5, c5_5) = mac(t5, a.5, b.5, c5_4);
    t6 := c5_5;

    m := r5_0 *% N_PRIME;
    let (_, mc5_0) = mac(r5_0, m, P0, 0);
    let (mr5_1, mc5_1) = mac(r5_1, m, P1, mc5_0);
    let (mr5_2, mc5_2) = mac(r5_2, m, P2, mc5_1);
    let (mr5_3, mc5_3) = mac(r5_3, m, P3, mc5_2);
    let (mr5_4, mc5_4) = mac(r5_4, m, P4, mc5_3);
    let (mr5_5, mc5_5) = mac(r5_5, m, P5, mc5_4);
    let (mr5_6, _) = adc(t6, 0, mc5_5);
    t0 := mr5_1; t1 := mr5_2; t2 := mr5_3; t3 := mr5_4; t4 := mr5_5; t5 := mr5_6;

    // Final conditional subtraction
    if (gte_p(t0, t1, t2, t3, t4, t5)) {
      let (s0, bw0) = sbb(t0, P0, 0);
      let (s1, bw1) = sbb(t1, P1, bw0);
      let (s2, bw2) = sbb(t2, P2, bw1);
      let (s3, bw3) = sbb(t3, P3, bw2);
      let (s4, bw4) = sbb(t4, P4, bw3);
      let (s5, _)   = sbb(t5, P5, bw4);
      (s0, s1, s2, s3, s4, s5);
    } else {
      (t0, t1, t2, t3, t4, t5);
    };
  };

  /// Montgomery squaring (uses same CIOS approach, but could be optimized later)
  public func fp_sq(a : Fp) : Fp {
    fp_mul(a, a);
  };

  // ══════════════════════════════════════════════════════════════
  //  Conversion to/from Montgomery form
  // ══════════════════════════════════════════════════════════════

  /// Convert a regular Int to Montgomery form.
  /// to_mont(a) = mont_mul(a_limbs, R^2) = a * R^2 * R^{-1} = a * R mod P
  public func to_mont(a : Int) : Fp {
    // First reduce a mod P
    let r = a % P_INT;
    let v : Nat = Int.abs(if (r < 0) { r + P_INT } else { r });

    // Convert to limbs
    let l0 = Prim.natToNat64(v % W);
    let v1 = v / W;
    let l1 = Prim.natToNat64(v1 % W);
    let v2 = v1 / W;
    let l2 = Prim.natToNat64(v2 % W);
    let v3 = v2 / W;
    let l3 = Prim.natToNat64(v3 % W);
    let v4 = v3 / W;
    let l4 = Prim.natToNat64(v4 % W);
    let v5 = v4 / W;
    let l5 = Prim.natToNat64(v5 % W);

    // Multiply by R^2 mod P using Montgomery multiplication
    // This gives a * R^2 * R^{-1} = a * R mod P
    fp_mul((l0, l1, l2, l3, l4, l5), R2);
  };

  /// Convert from Montgomery form back to Int.
  /// from_mont(aR) = mont_mul(aR, 1) = aR * 1 * R^{-1} = a mod P
  public func from_mont(a : Fp) : Int {
    // Montgomery multiply by 1 (in non-Montgomery form, i.e., (1,0,0,0,0,0))
    let r = fp_mul(a, (1, 0, 0, 0, 0, 0));
    // Convert limbs to Int
    Prim.nat64ToNat(r.0)
    + Prim.nat64ToNat(r.1) * W
    + Prim.nat64ToNat(r.2) * (W * W)
    + Prim.nat64ToNat(r.3) * (W * W * W)
    + Prim.nat64ToNat(r.4) * (W * W * W * W)
    + Prim.nat64ToNat(r.5) * (W * W * W * W * W);
  };

  /// Convert a Nat to Montgomery form
  public func nat_to_mont(n : Nat) : Fp {
    to_mont(n);
  };

  // ══════════════════════════════════════════════════════════════
  //  Exponentiation and inversion
  // ══════════════════════════════════════════════════════════════

  /// fp_pow: a^exp mod P (a in Montgomery form, exp as Nat)
  /// Result in Montgomery form.
  public func fp_pow(base_ : Fp, exp_ : Nat) : Fp {
    var result = ONE;
    var b = base_;
    var e = exp_;
    while (e > 0) {
      if (e % 2 == 1) {
        result := fp_mul(result, b);
      };
      b := fp_sq(b);
      e := e / 2;
    };
    result;
  };

  /// Modular inverse via Fermat's little theorem: a^{P-2} mod P
  public func fp_inv(a : Fp) : Fp {
    if (fp_is_zero(a)) return ZERO;
    // P-2 = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaa9
    fp_pow(a, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785);
  };

  /// Division: a / b = a * b^{-1}
  public func fp_div(a : Fp, b : Fp) : Fp {
    fp_mul(a, fp_inv(b));
  };

  /// Square root: a^{(P+1)/4} mod P  (P ≡ 3 mod 4)
  public func fp_sqrt(a : Fp) : ?Fp {
    let r = fp_pow(a, 1000602388805416848354447456433976039139220704984751971333014534031007912622709466110671907282253916009473568139947);
    if (fp_eq(fp_mul(r, r), a)) { ?r } else { null };
  };

  // ══════════════════════════════════════════════════════════════
  //  Scalar multiplication (by small Int constant)
  // ══════════════════════════════════════════════════════════════

  /// Multiply field element by a small integer scalar
  /// The scalar is NOT in Montgomery form — it's a plain integer.
  /// Result: (aR * s) mod P, but we need (a*s)*R mod P.
  /// Since a is aR, we have aR * s = (a*s)*R, which is what we want
  /// as long as s is small enough that aR*s < 2^384 * s won't overflow.
  /// For safety, convert s to Montgomery and use fp_mul.
  public func fp_scalar(a : Fp, s : Int) : Fp {
    fp_mul(a, to_mont(s));
  };

  // ══════════════════════════════════════════════════════════════
  //  Comparison helpers: fp_mod equivalent (convert, compare in Int)
  // ══════════════════════════════════════════════════════════════

  /// Get the canonical integer value mod P (for I/O and comparison)
  public func fp_to_int(a : Fp) : Int {
    from_mont(a);
  };

  /// Check if a > (P-1)/2 (for sign/sgn0 operations)
  public func fp_is_odd(a : Fp) : Bool {
    let v = from_mont(a);
    v % 2 == 1;
  };

  /// Modular reduction from Int (same as to_mont but returns Int value)
  public func fp_mod(a : Int) : Int {
    let r = a % P_INT;
    if (r < 0) { r + P_INT } else { r };
  };

};
