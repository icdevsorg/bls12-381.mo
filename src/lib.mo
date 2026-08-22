// BLS12-381 elliptic curve operations for EIP-2537 precompiles.
// Reference: https://eips.ethereum.org/EIPS/eip-2537
// Constants and algorithm structure were checked against @noble/curves 1.9.7.
// See THIRD_PARTY_LICENSES.md for its MIT attribution.

import Int "mo:base/Int";
import Iter "mo:base/Iter";
import Array "mo:base/Array";
import Buffer "mo:base/Buffer";
import Nat8 "mo:base/Nat8";
import Nat "mo:base/Nat";
import Nat64 "mo:base/Nat64";
import CoreNat "mo:core/Nat";

module {

  // 2^64 for Nat64 limb conversions
  let POW64 : Nat = 0x10000000000000000;

  // ══════════════════════════════════════════════════════════════
  //  Field prime  p  (381 bits)
  // ══════════════════════════════════════════════════════════════
  public let P : Nat = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787;

  // Curve order  r
  public let R_ : Nat = 52435875175126190479447740508185965837690552500527637822603658699938581184513;

  // Cofactors
  let G1_COFACTOR : Nat = 76329603384216526031706109802092473003;
  let G2_COFACTOR : Nat = 305502333931268344200999753193121504214466019254188142667664032982267604182971884026507427359259977847832272839041616661285803823378372096355777062779109;

  // BLS12-381 parameter x (|u| = 0xd201000000010000)
  let BLS_X : Nat = 15132376222941642752;

  // Precomputed constants
  let TWO_INV : Nat = 2001204777610833696708894912867952078278441409969503942666029068062015825245418932221343814564507832018947136279894; // (P+1)/2
  let FP_P_PLUS_1_OVER_4 : Nat = 1000602388805416848354447456433976039139220704984751971333014534031007912622709466110671907282253916009473568139947; // (P+1)/4
  let FP_P_MINUS_3_OVER_4 : Nat = 1000602388805416848354447456433976039139220704984751971333014534031007912622709466110671907282253916009473568139946; // (P-3)/4
  let FP_P_MINUS_1_OVER_2 : Nat = 2001204777610833696708894912867952078278441409969503942666029068062015825245418932221343814564507832018947136279893; // (P-1)/2

  // Precomputed NAF of BLS_X for miller loop (MSB first, 64 digits, implicit leading 1 omitted)
  let BLS_X_NAF : [Int] = [0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

  // Full NAF of BLS_X for exponentiation (MSB first, 65 digits, includes leading 1)
  let BLS_X_NAF_FULL : [Int] = [1, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

  // ══════════════════════════════════════════════════════════════
  //  Fp arithmetic  (modular arithmetic over prime P)
  // ══════════════════════════════════════════════════════════════

  public func fp_mod(a : Nat) : Nat {
    a % P;
  };

  public func fp_add(a : Nat, b : Nat) : Nat {
    let s = a + b;
    if (s >= P) { s - P } else { s };
  };

  public func fp_sub(a : Nat, b : Nat) : Nat {
    if (a >= b) { a - b } else { P + a - b };
  };

  public func fp_mul(a : Nat, b : Nat) : Nat {
    (a * b) % P;
  };

  public func fp_neg(a : Nat) : Nat {
    if (a == 0) { 0 } else { P - a };
  };

  public func fp_inv(a : Nat) : Nat {
    if (a == 0) return 0;
    // Extended GCD with sign-tracked Nat
    var lm : Nat = 1;
    var lm_neg : Bool = false;
    var hm : Nat = 0;
    var hm_neg : Bool = false;
    var low = fp_mod(a);
    var high = P;
    while (low > 1) {
      let ratio = high / low;
      let prod = lm * ratio;
      // nm = hm - lm * ratio (signed)
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

  public func fp_div(a : Nat, b : Nat) : Nat {
    fp_mul(a, fp_inv(b));
  };

  public func fp_pow(base_ : Nat, exp_ : Nat) : Nat {
    var result : Nat = 1;
    var b = fp_mod(base_);
    // Use Nat64 6-limb bit scanning for 384-bit exponents (86x faster scanning)
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
      s0 := (s0 >> 1) | ((s1 & 1) << 63);
      s1 := (s1 >> 1) | ((s2 & 1) << 63);
      s2 := (s2 >> 1) | ((s3 & 1) << 63);
      s3 := (s3 >> 1) | ((s4 & 1) << 63);
      s4 := (s4 >> 1) | ((s5 & 1) << 63);
      s5 := s5 >> 1;
    };
    result;
  };

  // p ≡ 3 (mod 4), so sqrt(a) = a^((p+1)/4)
  public func fp_sqrt(a : Nat) : ?Nat {
    let r = fp_pow(a, FP_P_PLUS_1_OVER_4);
    if (fp_mul(r, r) == fp_mod(a)) { ?r } else { null };
  };

  // ══════════════════════════════════════════════════════════════
  //  Fp2 = Fp[u] / (u² + 1)     element = (c0, c1) = c0 + c1*u
  // ══════════════════════════════════════════════════════════════

  public type Fp2 = (Nat, Nat);

  public let FP2_ZERO : Fp2 = (0, 0);
  public let FP2_ONE  : Fp2 = (1, 0);

  public func fp2_add(a : Fp2, b : Fp2) : Fp2 {
    (fp_add(a.0, b.0), fp_add(a.1, b.1));
  };

  public func fp2_sub(a : Fp2, b : Fp2) : Fp2 {
    (fp_sub(a.0, b.0), fp_sub(a.1, b.1));
  };

  public func fp2_mul(a : Fp2, b : Fp2) : Fp2 {
    let t0 = fp_mul(a.0, b.0);
    let t1 = fp_mul(a.1, b.1);
    (fp_sub(t0, t1), fp_sub(fp_mul(fp_add(a.0, a.1), fp_add(b.0, b.1)), fp_add(t0, t1)));
  };

  public func fp2_sq(a : Fp2) : Fp2 {
    // Dedicated squaring: (a0+a1)(a0-a1), 2*a0*a1 — only 2 fp_muls
    let t = fp_mul(a.0, a.1);
    (fp_mul(fp_add(a.0, a.1), fp_sub(a.0, a.1)), fp_add(t, t));
  };

  public func fp2_neg(a : Fp2) : Fp2 {
    (fp_neg(a.0), fp_neg(a.1));
  };

  public func fp2_scalar(a : Fp2, s : Nat) : Fp2 {
    (fp_mul(a.0, s), fp_mul(a.1, s));
  };

  public func fp2_inv(a : Fp2) : Fp2 {
    let t = fp_inv(fp_add(fp_mul(a.0, a.0), fp_mul(a.1, a.1)));
    (fp_mul(a.0, t), fp_mul(fp_neg(a.1), t));
  };

  public func fp2_div(a : Fp2, b : Fp2) : Fp2 { fp2_mul(a, fp2_inv(b)) };

  public func fp2_pow(base_ : Fp2, exp_ : Nat) : Fp2 {
    var result = FP2_ONE;
    var b = base_;
    // Use Nat64 6-limb bit scanning for 384-bit exponents
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

  public func fp2_eq(a : Fp2, b : Fp2) : Bool {
    fp_mod(a.0) == fp_mod(b.0) and fp_mod(a.1) == fp_mod(b.1);
  };

  public func fp2_is_zero(a : Fp2) : Bool {
    fp_mod(a.0) == 0 and fp_mod(a.1) == 0;
  };

  public func fp2_conj(a : Fp2) : Fp2 { (a.0, fp_neg(a.1)) };

  // Multiply by non-residue (1+u): (a0+a1*u)*(1+u) = (a0-a1) + (a0+a1)*u
  public func fp2_mul_nr(a : Fp2) : Fp2 {
    (fp_sub(a.0, a.1), fp_add(a.0, a.1));
  };

  public func fp2_sqrt(a : Fp2) : ?Fp2 {
    if (fp2_is_zero(a)) return ?FP2_ZERO;
    let a1 = fp2_pow(a, FP_P_MINUS_3_OVER_4);
    let alpha = fp2_mul(fp2_sq(a1), a);
    let x0 = fp2_mul(a1, a);
    if (fp2_eq(alpha, (P - 1, 0))) {
      return ?(fp_neg(x0.1), x0.0);
    };
    let b = fp2_mul(fp2_pow(fp2_add(FP2_ONE, alpha), FP_P_MINUS_1_OVER_2), x0);
    if (fp2_eq(fp2_sq(b), a)) { ?b } else { null };
  };

  // ══════════════════════════════════════════════════════════════
  //  G1 points:  y² = x³ + 4  over  Fp
  //  Jacobian coordinates: (X, Y, Z) = affine (X/Z², Y/Z³)
  // ══════════════════════════════════════════════════════════════

  public type G1Point = { x : Nat; y : Nat; z : Nat };

  public let G1_INF : G1Point = { x = 0; y = 1; z = 0 };

  public func g1_is_inf(p : G1Point) : Bool { fp_mod(p.z) == 0 };

  public func g1_eq(a : G1Point, b : G1Point) : Bool {
    if (g1_is_inf(a) and g1_is_inf(b)) return true;
    if (g1_is_inf(a) or g1_is_inf(b)) return false;
    let z1sq = fp_mul(a.z, a.z);
    let z2sq = fp_mul(b.z, b.z);
    if (fp_mod(fp_mul(a.x, z2sq)) != fp_mod(fp_mul(b.x, z1sq))) return false;
    fp_mod(fp_mul(a.y, fp_mul(z2sq, b.z))) == fp_mod(fp_mul(b.y, fp_mul(z1sq, a.z)));
  };

  public func g1_double(p : G1Point) : G1Point {
    if (g1_is_inf(p)) return G1_INF;
    let a = fp_mul(p.x, p.x);
    let b = fp_mul(p.y, p.y);
    let c = fp_mul(b, b);
    let d = fp_mul(2, fp_sub(fp_mul(fp_add(p.x, b), fp_add(p.x, b)), fp_add(a, c)));
    let e = fp_mul(3, a);
    let f = fp_mul(e, e);
    let nx = fp_sub(f, fp_mul(2, d));
    let ny = fp_sub(fp_mul(e, fp_sub(d, nx)), fp_mul(8, c));
    let nz = fp_mul(2, fp_mul(p.y, p.z));
    { x = fp_mod(nx); y = fp_mod(ny); z = fp_mod(nz) };
  };

  public func g1_add(a : G1Point, b : G1Point) : G1Point {
    if (g1_is_inf(a)) return b;
    if (g1_is_inf(b)) return a;
    let z1sq = fp_mul(a.z, a.z);
    let z2sq = fp_mul(b.z, b.z);
    let u1 = fp_mul(a.x, z2sq);
    let u2 = fp_mul(b.x, z1sq);
    let s1 = fp_mul(a.y, fp_mul(b.z, z2sq));
    let s2 = fp_mul(b.y, fp_mul(a.z, z1sq));
    if (fp_mod(u1) == fp_mod(u2)) {
      if (fp_mod(s1) == fp_mod(s2)) { return g1_double(a) }
      else { return G1_INF };
    };
    let h = fp_sub(u2, u1);
    let i = fp_mul(4, fp_mul(h, h));
    let j = fp_mul(h, i);
    let r = fp_mul(2, fp_sub(s2, s1));
    let v = fp_mul(u1, i);
    let nx = fp_sub(fp_sub(fp_mul(r, r), j), fp_mul(2, v));
    let ny = fp_sub(fp_mul(r, fp_sub(v, nx)), fp_mul(2, fp_mul(s1, j)));
    let nz = fp_mul(fp_sub(fp_mul(fp_add(a.z, b.z), fp_add(a.z, b.z)), fp_add(z1sq, z2sq)), h);
    { x = fp_mod(nx); y = fp_mod(ny); z = fp_mod(nz) };
  };

  public func g1_neg(p : G1Point) : G1Point {
    if (g1_is_inf(p)) return G1_INF;
    { x = p.x; y = fp_neg(p.y); z = p.z };
  };

  public func g1_mul(p : G1Point, n : Nat) : G1Point {
    if (n == 0 or g1_is_inf(p)) return G1_INF;
    var result = G1_INF;
    var base = p;
    var scalar = n;
    while (scalar > 0) {
      if (scalar % 2 == 1) { result := g1_add(result, base) };
      base := g1_double(base);
      scalar := scalar / 2;
    };
    result;
  };

  public func g1_to_affine(p : G1Point) : (Nat, Nat) {
    if (g1_is_inf(p)) return (0, 0);
    let zinv = fp_inv(p.z);
    let zinv2 = fp_mul(zinv, zinv);
    let zinv3 = fp_mul(zinv2, zinv);
    (fp_mod(fp_mul(p.x, zinv2)), fp_mod(fp_mul(p.y, zinv3)));
  };

  public func g1_is_on_curve(x : Nat, y : Nat) : Bool {
    fp_mod(fp_mul(y, y)) == fp_mod(fp_add(fp_mul(fp_mul(x, x), x), 4));
  };

  public func g1_from_affine(x : Nat, y : Nat) : ?G1Point {
    if (x == 0 and y == 0) return ?G1_INF;
    if (not g1_is_on_curve(x, y)) return null;
    ?{ x = fp_mod(x); y = fp_mod(y); z = 1 };
  };

  public func g1_subgroup_check(p : G1Point) : Bool {
    // r = x⁴ - x² + 1 where x = BLS_X = |z|
    // Compute [r]P = [x⁴]P - [x²]P + P via chain of [x] multiplications
    // BLS_X has only 6 set bits in 64 bits, so [x]P is very efficient
    let q1 = g1_mul(p, BLS_X);      // [x]P
    let q2 = g1_mul(q1, BLS_X);     // [x²]P
    let q3 = g1_mul(q2, BLS_X);     // [x³]P
    let q4 = g1_mul(q3, BLS_X);     // [x⁴]P
    g1_is_inf(g1_add(g1_add(q4, g1_neg(q2)), p));
  };

  // ══════════════════════════════════════════════════════════════
  //  G2 points: y² = x³ + 4(1+i)  over  Fp2    (Jacobian)
  // ══════════════════════════════════════════════════════════════

  public type G2Point = { x : Fp2; y : Fp2; z : Fp2 };

  public let G2_INF : G2Point = { x = FP2_ZERO; y = FP2_ONE; z = FP2_ZERO };

  let B_TWIST : Fp2 = (4, 4); // 4*(1+i)

  public func g2_is_inf(p : G2Point) : Bool { fp2_is_zero(p.z) };

  public func g2_double(p : G2Point) : G2Point {
    if (g2_is_inf(p)) return G2_INF;
    let a = fp2_sq(p.x);
    let b = fp2_sq(p.y);
    let c = fp2_sq(b);
    let d = fp2_scalar(fp2_sub(fp2_sq(fp2_add(p.x, b)), fp2_add(a, c)), 2);
    let e = fp2_scalar(a, 3);
    let f = fp2_sq(e);
    let nx = fp2_sub(f, fp2_scalar(d, 2));
    let ny = fp2_sub(fp2_mul(e, fp2_sub(d, nx)), fp2_scalar(c, 8));
    let nz = fp2_scalar(fp2_mul(p.y, p.z), 2);
    { x = nx; y = ny; z = nz };
  };

  public func g2_add(a : G2Point, b : G2Point) : G2Point {
    if (g2_is_inf(a)) return b;
    if (g2_is_inf(b)) return a;
    let z1sq = fp2_sq(a.z);
    let z2sq = fp2_sq(b.z);
    let u1 = fp2_mul(a.x, z2sq);
    let u2 = fp2_mul(b.x, z1sq);
    let s1 = fp2_mul(a.y, fp2_mul(b.z, z2sq));
    let s2 = fp2_mul(b.y, fp2_mul(a.z, z1sq));
    if (fp2_eq(u1, u2)) {
      if (fp2_eq(s1, s2)) return g2_double(a);
      return G2_INF;
    };
    let h = fp2_sub(u2, u1);
    let i = fp2_sq(fp2_scalar(h, 2));
    let j = fp2_mul(h, i);
    let r = fp2_scalar(fp2_sub(s2, s1), 2);
    let v = fp2_mul(u1, i);
    let nx = fp2_sub(fp2_sub(fp2_sq(r), j), fp2_scalar(v, 2));
    let ny = fp2_sub(fp2_mul(r, fp2_sub(v, nx)), fp2_scalar(fp2_mul(s1, j), 2));
    let nz = fp2_mul(fp2_sub(fp2_sq(fp2_add(a.z, b.z)), fp2_add(z1sq, z2sq)), h);
    { x = nx; y = ny; z = nz };
  };

  public func g2_neg(p : G2Point) : G2Point {
    if (g2_is_inf(p)) return G2_INF;
    { x = p.x; y = fp2_neg(p.y); z = p.z };
  };

  public func g2_mul(p : G2Point, n : Nat) : G2Point {
    if (n == 0 or g2_is_inf(p)) return G2_INF;
    var result = G2_INF;
    var base = p;
    var scalar = n;
    while (scalar > 0) {
      if (scalar % 2 == 1) { result := g2_add(result, base) };
      base := g2_double(base);
      scalar := scalar / 2;
    };
    result;
  };

  public func g2_to_affine(p : G2Point) : (Fp2, Fp2) {
    if (g2_is_inf(p)) return (FP2_ZERO, FP2_ZERO);
    let zinv = fp2_inv(p.z);
    let zinv2 = fp2_sq(zinv);
    let zinv3 = fp2_mul(zinv2, zinv);
    (fp2_mul(p.x, zinv2), fp2_mul(p.y, zinv3));
  };

  public func g2_is_on_curve(x : Fp2, y : Fp2) : Bool {
    fp2_eq(fp2_sq(y), fp2_add(fp2_mul(fp2_sq(x), x), B_TWIST));
  };

  public func g2_from_affine(x : Fp2, y : Fp2) : ?G2Point {
    if (fp2_is_zero(x) and fp2_is_zero(y)) return ?G2_INF;
    if (not g2_is_on_curve(x, y)) return null;
    ?{ x = x; y = y; z = FP2_ONE };
  };

  // ψ (psi) endomorphism on G2: untwist-Frobenius-twist
  // ψ(P) = [λ]P where λ ≡ -z (mod r) on the r-torsion subgroup
  // In Jacobian: ψ(X, Y, Z) = (PSI_X · conj(X), PSI_Y · conj(Y), conj(Z))
  // where conj is Fp2 conjugation: (a, b) → (a, -b)

  let PSI_X : Fp2 = (0, 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437);
  let PSI_Y : Fp2 = (2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530, 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257);

  public func g2_psi(p : G2Point) : G2Point {
    if (g2_is_inf(p)) return G2_INF;
    { x = fp2_mul(PSI_X, fp2_conj(p.x));
      y = fp2_mul(PSI_Y, fp2_conj(p.y));
      z = fp2_conj(p.z) };
  };

  public func g2_subgroup_check(p : G2Point) : Bool {
    // Efficient check using ψ endomorphism:
    // ψ(P) = [z]P on the r-torsion, where z = -BLS_X (negative)
    // So ψ(P) = [-BLS_X]P, meaning ψ(P) + [BLS_X]P = O
    let zP = g2_mul(p, BLS_X);      // [BLS_X]P
    let psiP = g2_psi(p);           // ψ(P) = [-BLS_X]P on subgroup
    g2_is_inf(g2_add(psiP, zP));    // ψ(P) + [BLS_X]P = O ?
  };

  // ══════════════════════════════════════════════════════════════
  //  Fp6 = Fp2[v] / (v³ - (1+u))
  //  element = (c0, c1, c2)
  // ══════════════════════════════════════════════════════════════

  public type Fp6 = (Fp2, Fp2, Fp2);

  public let FP6_ZERO : Fp6 = (FP2_ZERO, FP2_ZERO, FP2_ZERO);
  public let FP6_ONE  : Fp6 = (FP2_ONE, FP2_ZERO, FP2_ZERO);

  public func fp6_add(a : Fp6, b : Fp6) : Fp6 {
    (fp2_add(a.0, b.0), fp2_add(a.1, b.1), fp2_add(a.2, b.2));
  };

  public func fp6_sub(a : Fp6, b : Fp6) : Fp6 {
    (fp2_sub(a.0, b.0), fp2_sub(a.1, b.1), fp2_sub(a.2, b.2));
  };

  public func fp6_neg(a : Fp6) : Fp6 {
    (fp2_neg(a.0), fp2_neg(a.1), fp2_neg(a.2));
  };

  // v³ = (1+u), so multiply Fp2 by non-residue for cubic extension
  func fp6_nr(a : Fp2) : Fp2 { fp2_mul_nr(a) };

  public func fp6_mul(a : Fp6, b : Fp6) : Fp6 {
    let t0 = fp2_mul(a.0, b.0);
    let t1 = fp2_mul(a.1, b.1);
    let t2 = fp2_mul(a.2, b.2);
    let c0 = fp2_add(t0, fp6_nr(fp2_sub(fp2_mul(fp2_add(a.1, a.2), fp2_add(b.1, b.2)), fp2_add(t1, t2))));
    let c1 = fp2_add(fp2_sub(fp2_mul(fp2_add(a.0, a.1), fp2_add(b.0, b.1)), fp2_add(t0, t1)), fp6_nr(t2));
    let c2 = fp2_add(fp2_sub(fp2_mul(fp2_add(a.0, a.2), fp2_add(b.0, b.2)), fp2_add(t0, t2)), t1);
    (c0, c1, c2);
  };

  // Dedicated Fp6 squaring (Chung-Hasan SQ2 formula)
  public func fp6_sq(a : Fp6) : Fp6 {
    let s0 = fp2_sq(a.0);
    let ab = fp2_mul(a.0, a.1);
    let s1 = fp2_add(ab, ab);
    let s2 = fp2_sq(fp2_sub(fp2_add(a.0, a.2), a.1));
    let bc = fp2_mul(a.1, a.2);
    let s3 = fp2_add(bc, bc);
    let s4 = fp2_sq(a.2);
    (fp2_add(s0, fp6_nr(s3)),
     fp2_add(s1, fp6_nr(s4)),
     fp2_add(fp2_add(fp2_sub(fp2_add(s1, s2), s0), s3), fp2_neg(s4)));
  };

  public func fp6_inv(a : Fp6) : Fp6 {
    let t0 = fp2_sub(fp2_sq(a.0), fp6_nr(fp2_mul(a.1, a.2)));
    let t1 = fp2_sub(fp6_nr(fp2_sq(a.2)), fp2_mul(a.0, a.1));
    let t2 = fp2_sub(fp2_sq(a.1), fp2_mul(a.0, a.2));
    let det = fp2_add(fp2_mul(a.0, t0), fp6_nr(fp2_add(fp2_mul(a.2, t1), fp2_mul(a.1, t2))));
    let di = fp2_inv(det);
    (fp2_mul(t0, di), fp2_mul(t1, di), fp2_mul(t2, di));
  };

  // ══════════════════════════════════════════════════════════════
  //  Fp12 = Fp6[w] / (w² - v)
  //  element = (c0, c1)
  // ══════════════════════════════════════════════════════════════

  public type Fp12 = (Fp6, Fp6);

  public let FP12_ONE  : Fp12 = (FP6_ONE, FP6_ZERO);

  // Fp6 * v  ->  (nr*c2, c0, c1)
  func fp6_mul_by_v(a : Fp6) : Fp6 {
    (fp6_nr(a.2), a.0, a.1);
  };

  public func fp12_add(a : Fp12, b : Fp12) : Fp12 {
    (fp6_add(a.0, b.0), fp6_add(a.1, b.1));
  };

  public func fp12_sub(a : Fp12, b : Fp12) : Fp12 {
    (fp6_sub(a.0, b.0), fp6_sub(a.1, b.1));
  };

  public func fp12_mul(a : Fp12, b : Fp12) : Fp12 {
    let t0 = fp6_mul(a.0, b.0);
    let t1 = fp6_mul(a.1, b.1);
    let c0 = fp6_add(t0, fp6_mul_by_v(t1));
    let c1 = fp6_sub(fp6_sub(fp6_mul(fp6_add(a.0, a.1), fp6_add(b.0, b.1)), t0), t1);
    (c0, c1);
  };

  // Dedicated Fp12 squaring
  public func fp12_sq(a : Fp12) : Fp12 {
    let t0 = fp6_sq(a.0);
    let t1 = fp6_sq(a.1);
    let c0 = fp6_add(t0, fp6_mul_by_v(t1));
    let c1 = fp6_sub(fp6_sub(fp6_sq(fp6_add(a.0, a.1)), t0), t1);
    (c0, c1);
  };

  // Cyclotomic squaring (for elements in the p^6-cyclotomic subgroup)
  // Uses Granger-Scott 2010 algorithm
  // Fp4Square(x, y) = (x² + β·y², (x+y)² - x² - y²)  where β = mulByNonresidue
  // Pairs: (A0, B1), (B0, A2), (A1, B2)
  public func fp12_cyclotomic_sq(a : Fp12) : Fp12 {
    let (a0, a1, a2) = a.0;
    let (b0, b1, b2) = a.1;

    // Pair 1: Fp4Square(A0, B1)
    let a0_sq = fp2_sq(a0);
    let b1_sq = fp2_sq(b1);
    let t3 = fp2_add(fp6_nr(b1_sq), a0_sq);     // β·B1² + A0²
    let t4 = fp2_sub(fp2_sub(fp2_sq(fp2_add(a0, b1)), a0_sq), b1_sq); // 2·A0·B1

    // Pair 2: Fp4Square(B0, A2)
    let b0_sq = fp2_sq(b0);
    let a2_sq = fp2_sq(a2);
    let t5 = fp2_add(fp6_nr(a2_sq), b0_sq);     // β·A2² + B0²
    let t6 = fp2_sub(fp2_sub(fp2_sq(fp2_add(b0, a2)), b0_sq), a2_sq); // 2·B0·A2

    // Pair 3: Fp4Square(A1, B2)
    let a1_sq = fp2_sq(a1);
    let b2_sq = fp2_sq(b2);
    let t7 = fp2_add(fp6_nr(b2_sq), a1_sq);     // β·B2² + A1²
    let t8 = fp2_sub(fp2_sub(fp2_sq(fp2_add(a1, b2)), a1_sq), b2_sq); // 2·A1·B2

    let t9 = fp6_nr(t8);                         // β · (2·A1·B2)

    // Each output uses its OWN old value, with even/odd parts distributed:
    // Even parts → A components (subtract 2× old), Odd parts → B components (add 2× old)
    let newA0 = fp2_add(fp2_scalar(fp2_sub(t3, a0), 2), t3);  // 3t3 - 2A0
    let newA1 = fp2_add(fp2_scalar(fp2_sub(t5, a1), 2), t5);  // 3t5 - 2A1
    let newA2 = fp2_add(fp2_scalar(fp2_sub(t7, a2), 2), t7);  // 3t7 - 2A2
    let newB0 = fp2_add(fp2_scalar(fp2_add(t9, b0), 2), t9);  // 3t9 + 2B0
    let newB1 = fp2_add(fp2_scalar(fp2_add(t4, b1), 2), t4);  // 3t4 + 2B1
    let newB2 = fp2_add(fp2_scalar(fp2_add(t6, b2), 2), t6);  // 3t6 + 2B2

    ((newA0, newA1, newA2), (newB0, newB1, newB2));
  };

  // Cyclotomic exponentiation by BLS_X using precomputed NAF
  // Uses cyclotomic squaring (much cheaper) and conjugate for inverse
  func fp12_cyclotomic_exp_bls_x(f : Fp12) : Fp12 {
    var result = FP12_ONE;
    let finv = fp12_conj(f);  // In cyclotomic subgroup, inverse = conjugate
    var started = false;

    for (digit in BLS_X_NAF_FULL.vals()) {
      if (started) {
        result := fp12_cyclotomic_sq(result);
      };
      if (digit == 1) {
        result := if (started) { fp12_mul(result, f) } else { f };
        started := true;
      } else if (digit == -1) {
        result := if (started) { fp12_mul(result, finv) } else { finv };
        started := true;
      };
    };
    result;
  };

  public func fp12_inv(a : Fp12) : Fp12 {
    let t = fp6_inv(fp6_sub(fp6_sq(a.0), fp6_mul_by_v(fp6_sq(a.1))));
    (fp6_mul(a.0, t), fp6_neg(fp6_mul(a.1, t)));
  };

  public func fp12_pow(base_ : Fp12, exp_ : Nat) : Fp12 {
    var result = FP12_ONE;
    var b = base_;
    // Use Nat64 6-limb bit scanning for 384-bit exponents
    var s0 = Nat64.fromNat(exp_ % POW64);
    var s1 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 64) % POW64);
    var s2 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 128) % POW64);
    var s3 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 192) % POW64);
    var s4 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 256) % POW64);
    var s5 = Nat64.fromNat(CoreNat.bitshiftRight(exp_, 320) % POW64);
    while (s0 != 0 or s1 != 0 or s2 != 0 or s3 != 0 or s4 != 0 or s5 != 0) {
      if ((s0 & 1) == 1) { result := fp12_mul(result, b) };
      b := fp12_sq(b);
      s0 := (s0 >> 1) | ((s1 & 1) << 63);
      s1 := (s1 >> 1) | ((s2 & 1) << 63);
      s2 := (s2 >> 1) | ((s3 & 1) << 63);
      s3 := (s3 >> 1) | ((s4 & 1) << 63);
      s4 := (s4 >> 1) | ((s5 & 1) << 63);
      s5 := s5 >> 1;
    };
    result;
  };

  public func fp12_eq(a : Fp12, b : Fp12) : Bool {
    fp2_eq(a.0.0, b.0.0) and fp2_eq(a.0.1, b.0.1) and fp2_eq(a.0.2, b.0.2) and
    fp2_eq(a.1.0, b.1.0) and fp2_eq(a.1.1, b.1.1) and fp2_eq(a.1.2, b.1.2);
  };

  // Conjugate: (c0, c1) -> (c0, -c1)
  public func fp12_conj(a : Fp12) : Fp12 { (a.0, fp6_neg(a.1)) };

  // ══════════════════════════════════════════════════════════════
  //  Sparse Fp6 and Fp12 multiplications for pairing
  // ══════════════════════════════════════════════════════════════

  // Fp6 multiply by element with only c1 non-zero: (0, b1, 0)
  func fp6_mul1(a : Fp6, b1 : Fp2) : Fp6 {
    (fp6_nr(fp2_mul(a.2, b1)), fp2_mul(a.0, b1), fp2_mul(a.1, b1));
  };

  // Fp6 multiply by element with only c0, c1 non-zero: (b0, b1, 0)
  func fp6_mul01(a : Fp6, b0 : Fp2, b1 : Fp2) : Fp6 {
    let t0 = fp2_mul(a.0, b0);
    let t1 = fp2_mul(a.1, b1);
    (
      fp2_add(fp6_nr(fp2_sub(fp2_mul(fp2_add(a.1, a.2), b1), t1)), t0),
      fp2_sub(fp2_sub(fp2_mul(fp2_add(b0, b1), fp2_add(a.0, a.1)), t0), t1),
      fp2_add(fp2_sub(fp2_mul(fp2_add(a.0, a.2), b0), t0), t1)
    );
  };

  // Sparse Fp12 multiplication: positions 0, 1, 4
  // For M-type twist of BLS12-381
  func fp12_mul014(f : Fp12, o0 : Fp2, o1 : Fp2, o4 : Fp2) : Fp12 {
    let t0 = fp6_mul01(f.0, o0, o1);
    let t1 = fp6_mul1(f.1, o4);
    let c0 = fp6_add(fp6_mul_by_v(t1), t0);
    let c1 = fp6_sub(fp6_sub(fp6_mul01(fp6_add(f.1, f.0), o0, fp2_add(o1, o4)), t0), t1);
    (c0, c1);
  };

  // ══════════════════════════════════════════════════════════════
  //  Line evaluation functions for the Miller loop
  //  These compute BOTH the new point AND the line coefficients
  //  together (unified projective formulas)
  // ══════════════════════════════════════════════════════════════

  // Doubling step: double the point R and produce line coefficients
  // Returns (new Rx, new Ry, new Rz, (c0, c1, c2))
  func doubling_step(rx : Fp2, ry : Fp2, rz : Fp2) : (Fp2, Fp2, Fp2, Fp2, Fp2, Fp2) {
    let two_inv : Fp2 = (TWO_INV, 0);
    let t0 = fp2_sq(ry);                                     // Ry²
    let t1 = fp2_sq(rz);                                     // Rz²
    let t2 = fp2_mul(B_TWIST, fp2_scalar(t1, 3));            // 3 * b' * Rz²
    let t3 = fp2_scalar(t2, 3);                              // 9 * b' * Rz²
    let t4 = fp2_sub(fp2_sub(fp2_sq(fp2_add(ry, rz)), t1), t0); // 2*Ry*Rz

    // Line coefficients
    let c0 = fp2_sub(t2, t0);                                // 3*b'*Rz² - Ry²
    let c1 = fp2_scalar(fp2_sq(rx), 3);                      // 3*Rx²
    let c2 = fp2_neg(t4);                                     // -(2*Ry*Rz)

    // Point update
    let new_rx = fp2_mul(fp2_mul(fp2_mul(fp2_sub(t0, t3), rx), ry), two_inv);
    let new_ry = fp2_sub(fp2_sq(fp2_mul(fp2_add(t0, t3), two_inv)), fp2_scalar(fp2_sq(t2), 3));
    let new_rz = fp2_mul(t0, t4);

    (new_rx, new_ry, new_rz, c0, c1, c2);
  };

  // Addition step: add affine point Q to projective point R
  // Returns (new Rx, new Ry, new Rz, (c0, c1, c2))
  func addition_step(rx : Fp2, ry : Fp2, rz : Fp2, qx : Fp2, qy : Fp2) : (Fp2, Fp2, Fp2, Fp2, Fp2, Fp2) {
    let t0 = fp2_sub(ry, fp2_mul(qy, rz));                    // Ry - Qy*Rz
    let t1 = fp2_sub(rx, fp2_mul(qx, rz));                    // Rx - Qx*Rz

    // Line coefficients
    let c0 = fp2_sub(fp2_mul(t0, qx), fp2_mul(t1, qy));      // T0*Qx - T1*Qy
    let c1 = fp2_neg(t0);                                      // -T0
    let c2 = t1;                                                // T1

    // Point update
    let t2 = fp2_sq(t1);                                       // T1²
    let t3 = fp2_mul(t2, t1);                                  // T1³
    let t4 = fp2_mul(t2, rx);                                  // T1²*Rx
    let t5 = fp2_add(fp2_sub(t3, fp2_scalar(t4, 2)), fp2_mul(fp2_sq(t0), rz));
    let new_rx = fp2_mul(t1, t5);
    let new_ry = fp2_sub(fp2_mul(fp2_sub(t4, t5), t0), fp2_mul(t3, ry));
    let new_rz = fp2_mul(rz, t3);

    (new_rx, new_ry, new_rz, c0, c1, c2);
  };

  // Apply line function: sparse multiply f by (c0, c1*Px, c2*Py)
  func apply_line(f : Fp12, c0 : Fp2, c1 : Fp2, c2 : Fp2, px : Nat, py : Nat) : Fp12 {
    fp12_mul014(f, c0, fp2_scalar(c1, px), fp2_scalar(c2, py));
  };

  // ══════════════════════════════════════════════════════════════
  //  NAF (Non-Adjacent Form) decomposition
  // ══════════════════════════════════════════════════════════════

  func _naf_decomposition(a : Nat) : [Int] {
    let buf = Buffer.Buffer<Int>(64);
    var n = a;
    // n > 1 because of marker bit (leading 1 is implicit)
    while (n > 1) {
      if (n % 2 == 0) {
        buf.add(0);
      } else if (n % 4 == 3) {
        buf.add(-1);
        n += 1;
      } else {
        buf.add(1);
      };
      n := n / 2;
    };
    // buf is LSB first, reverse to MSB first
    let arr = Buffer.toArray(buf);
    Array.tabulate<Int>(arr.size(), func(i_ : Nat) : Int { arr[arr.size() - 1 - i_] });
  };

  // ══════════════════════════════════════════════════════════════
  //  Miller loop
  // ══════════════════════════════════════════════════════════════

  public func miller_loop(p : G1Point, q : G2Point) : Fp12 {
    if (g1_is_inf(p) or g2_is_inf(q)) return FP12_ONE;
    let p_aff = g1_to_affine(p);
    let q_aff = g2_to_affine(q);
    let qx = q_aff.0;
    let qy = q_aff.1;
    let neg_qy = fp2_neg(qy);
    var rx = qx;
    var ry = qy;
    var rz = FP2_ONE;
    var f = FP12_ONE;
    let naf = BLS_X_NAF;

    for (idx in Iter.range(0, naf.size() - 1)) {
      f := fp12_sq(f);
      let (nrx, nry, nrz, c0d, c1d, c2d) = doubling_step(rx, ry, rz);
      rx := nrx; ry := nry; rz := nrz;
      f := apply_line(f, c0d, c1d, c2d, p_aff.0, p_aff.1);
      let bit = naf[idx];
      if (bit != 0) {
        let use_qy = if (bit == -1) neg_qy else qy;
        let (arx, ary, arz, c0a, c1a, c2a) = addition_step(rx, ry, rz, qx, use_qy);
        rx := arx; ry := ary; rz := arz;
        f := apply_line(f, c0a, c1a, c2a, p_aff.0, p_aff.1);
      };
    };

    // BLS12-381 x is negative, so conjugate
    f := fp12_conj(f);
    f;
  };

  /// Combined multi-Miller loop: processes all pairs in a single pass over
  /// the BLS_X NAF bits.  Shares the fp12_sq across all pairs, saving ~64
  /// fp12_sq operations compared to calling miller_loop separately per pair.
  /// Pairs where either component is at infinity are silently skipped.
  public func multi_miller_loop(pairs : [(G1Point, G2Point)]) : Fp12 {
    // Pre-process pairs: convert to affine and filter out infinities
    let buf = Buffer.Buffer<(Nat, Nat, Fp2, Fp2, Fp2, Fp2, Fp2, Fp2)>(pairs.size());
    for ((p, q) in pairs.vals()) {
      if (not g1_is_inf(p) and not g2_is_inf(q)) {
        let p_aff = g1_to_affine(p);
        let q_aff = g2_to_affine(q);
        buf.add((p_aff.0, p_aff.1, q_aff.0, q_aff.1, fp2_neg(q_aff.1), q_aff.0, q_aff.1, FP2_ONE));
      };
    };
    let n = buf.size();
    if (n == 0) return FP12_ONE;

    // Mutable arrays for R-point tracking per pair
    let pxArr = Array.tabulate<Nat>(n, func(i : Nat) : Nat { buf.get(i).0 });
    let pyArr = Array.tabulate<Nat>(n, func(i : Nat) : Nat { buf.get(i).1 });
    let qxArr = Array.tabulate<Fp2>(n, func(i : Nat) : Fp2 { buf.get(i).2 });
    let qyArr = Array.tabulate<Fp2>(n, func(i : Nat) : Fp2 { buf.get(i).3 });
    let negQyArr = Array.tabulate<Fp2>(n, func(i : Nat) : Fp2 { buf.get(i).4 });
    let rxArr = Array.tabulateVar<Fp2>(n, func(i : Nat) : Fp2 { buf.get(i).5 });
    let ryArr = Array.tabulateVar<Fp2>(n, func(i : Nat) : Fp2 { buf.get(i).6 });
    let rzArr = Array.tabulateVar<Fp2>(n, func(i : Nat) : Fp2 { buf.get(i).7 });

    var f = FP12_ONE;
    let naf = BLS_X_NAF;

    for (idx in Iter.range(0, naf.size() - 1)) {
      f := fp12_sq(f);  // shared across all pairs

      // Doubling step for each pair
      var i = 0;
      while (i < n) {
        let (nrx, nry, nrz, c0d, c1d, c2d) = doubling_step(rxArr[i], ryArr[i], rzArr[i]);
        rxArr[i] := nrx; ryArr[i] := nry; rzArr[i] := nrz;
        f := apply_line(f, c0d, c1d, c2d, pxArr[i], pyArr[i]);
        i += 1;
      };

      let bit = naf[idx];
      if (bit != 0) {
        // Addition step for each pair
        var j = 0;
        while (j < n) {
          let use_qy = if (bit == -1) negQyArr[j] else qyArr[j];
          let (arx, ary, arz, c0a, c1a, c2a) = addition_step(rxArr[j], ryArr[j], rzArr[j], qxArr[j], use_qy);
          rxArr[j] := arx; ryArr[j] := ary; rzArr[j] := arz;
          f := apply_line(f, c0a, c1a, c2a, pxArr[j], pyArr[j]);
          j += 1;
        };
      };
    };

    // BLS12-381 x is negative, so conjugate
    fp12_conj(f);
  };

  // ══════════════════════════════════════════════════════════════
  //  Frobenius maps using precomputed coefficients
  // ══════════════════════════════════════════════════════════════

  // Frobenius for Fp2: conjugate (a0 + a1*u) -> (a0 - a1*u)
  func fp2_frob(a : Fp2) : Fp2 { fp2_conj(a) };

  // Frobenius coefficients for Fp6 (extracted from noble-curves)
  // FROB6_C1[power] applied to c1 component, FROB6_C2[power] applied to c2 component

  // power=1
  let FROB6_C1_1 : Fp2 = (
    0,
    4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436
  );
  let FROB6_C2_1 : Fp2 = (
    4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437,
    0
  );
  // power=2
  let FROB6_C1_2 : Fp2 = (
    793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350,
    0
  );
  let FROB6_C2_2 : Fp2 = (
    4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436,
    0
  );
  // power=3
  let FROB6_C1_3 : Fp2 = (
    0,
    1
  );
  let FROB6_C2_3 : Fp2 = (
    4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786,
    0
  );

  func fp6_frob(a : Fp6, power : Nat) : Fp6 {
    let (gamma1, gamma2) = switch(power % 6) {
      case(1) (FROB6_C1_1, FROB6_C2_1);
      case(2) (FROB6_C1_2, FROB6_C2_2);
      case(3) (FROB6_C1_3, FROB6_C2_3);
      case(_) ((1,0) : Fp2, (1,0) : Fp2);  // identity for power=0
    };
    if (power % 2 == 1) {
      (fp2_frob(a.0), fp2_mul(gamma1, fp2_frob(a.1)), fp2_mul(gamma2, fp2_frob(a.2)));
    } else {
      (a.0, fp2_mul(gamma1, a.1), fp2_mul(gamma2, a.2));
    };
  };

  // Fp12 Frobenius coefficients (extracted from noble-curves)
  // power=1: (1+u)^((p-1)/6)
  let FROB12_C_1 : Fp2 = (
    3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760,
    151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027
  );
  // power=2: (1+u)^((p^2-1)/6)
  let FROB12_C_2 : Fp2 = (
    793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351,
    0
  );
  // power=3: (1+u)^((p^3-1)/6)
  let FROB12_C_3 : Fp2 = (
    2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530,
    1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257
  );

  func fp12_frob(a : Fp12, power : Nat) : Fp12 {
    let c0 = fp6_frob(a.0, power);
    let c1_frob = fp6_frob(a.1, power);
    let coeff = switch(power % 12) {
      case(1) FROB12_C_1;
      case(2) FROB12_C_2;
      case(3) FROB12_C_3;
      case(_) (1,0) : Fp2;
    };
    // Multiply each Fp2 component of c1 by the coefficient
    let c1 : Fp6 = (fp2_mul(c1_frob.0, coeff), fp2_mul(c1_frob.1, coeff), fp2_mul(c1_frob.2, coeff));
    (c0, c1);
  };

  // ══════════════════════════════════════════════════════════════
  //  Final exponentiation
  //  f^((p^12 - 1) / r)
  // ══════════════════════════════════════════════════════════════

  // Easy part: f^((p^6-1)(p^2+1))
  func final_exp_easy(f : Fp12) : Fp12 {
    // f^(p^6-1) = conj(f) / f
    let f1 = fp12_mul(fp12_conj(f), fp12_inv(f));
    // f1^(p^2+1)
    fp12_mul(fp12_frob(f1, 2), f1);
  };

  // Hard part using addition chain from noble-curves
  // Uses cyclotomic squaring/exponentiation since f is in cyclotomic subgroup
  func final_exp_hard(f : Fp12) : Fp12 {
    let t2 = fp12_conj(fp12_cyclotomic_exp_bls_x(f));

    let t3 = fp12_mul(fp12_conj(fp12_cyclotomic_sq(f)), t2);

    let t4 = fp12_conj(fp12_cyclotomic_exp_bls_x(t3));

    let t5 = fp12_conj(fp12_cyclotomic_exp_bls_x(t4));

    let t6 = fp12_mul(fp12_conj(fp12_cyclotomic_exp_bls_x(t5)), fp12_cyclotomic_sq(t2));

    let t7 = fp12_conj(fp12_cyclotomic_exp_bls_x(t6));

    // Combine with Frobenius maps
    let a = fp12_frob(fp12_mul(t2, t5), 2);         // (t2*t5)^(p²)
    let b = fp12_frob(fp12_mul(t4, f), 3);           // (t4*f)^(p³)
    let c = fp12_frob(fp12_mul(t6, fp12_conj(f)), 1); // (t6*conj(f))^p
    let d = fp12_mul(fp12_mul(t7, fp12_conj(t3)), f); // t7 * conj(t3) * f

    fp12_mul(fp12_mul(fp12_mul(a, b), c), d);
  };

  public func final_exponentiation(f : Fp12) : Fp12 {
    final_exp_hard(final_exp_easy(f));
  };

  // ══════════════════════════════════════════════════════════════
  //  Pairing
  // ══════════════════════════════════════════════════════════════

  public func pairing(p : G1Point, q : G2Point) : Fp12 {
    final_exponentiation(miller_loop(p, q));
  };

  public func multi_pairing(pairs : [(G1Point, G2Point)]) : Fp12 {
    final_exponentiation(multi_miller_loop(pairs));
  };

  public func pairing_check(pairs : [(G1Point, G2Point)]) : Bool {
    fp12_eq(multi_pairing(pairs), FP12_ONE);
  };

  // ══════════════════════════════════════════════════════════════
  //  MSM (multi-scalar multiplication) - Pippenger's bucket method
  //  Falls back to naive summation for small k
  // ══════════════════════════════════════════════════════════════

  public func g1_msm(points : [G1Point], scalars : [Nat]) : G1Point {
    let k = points.size();
    if (k == 0) return G1_INF;
    if (k == 1) return g1_mul(points[0], scalars[0]);

    // Naive fallback for small k (Pippenger overhead not worth it)
    if (k <= 8) {
      var result = G1_INF;
      for (i in Iter.range(0, k - 1)) {
        result := g1_add(result, g1_mul(points[i], scalars[i]));
      };
      return result;
    };

    // Pippenger's bucket method
    // Window size c ≈ floor(log2(k))
    var c : Nat = 0;
    var temp = k;
    while (temp > 0) { c += 1; temp := temp / 2; };
    c -= 1; // floor(log2(k))

    // Compute 2^c
    var windowSize : Nat = 1;
    for (_ in Iter.range(0, c - 1)) { windowSize *= 2; };
    let numBuckets : Nat = windowSize - 1;
    let numWindows : Nat = (256 + c - 1) / c;

    // Pre-decompose scalars into c-bit windows
    let scalarWindows = Array.tabulate<[var Nat]>(k, func(idx : Nat) : [var Nat] {
      let w = Array.init<Nat>(numWindows, 0);
      var s = scalars[idx];
      for (j in Iter.range(0, numWindows - 1)) {
        w[j] := s % windowSize;
        s := s / windowSize;
      };
      w;
    });

    // Allocate buckets (reused across windows)
    let buckets = Array.init<G1Point>(numBuckets, G1_INF);
    let windowResults = Array.init<G1Point>(numWindows, G1_INF);

    for (j in Iter.range(0, numWindows - 1)) {
      // Reset buckets
      for (b in Iter.range(0, numBuckets - 1)) {
        buckets[b] := G1_INF;
      };

      // Bucket accumulation: add P_i to bucket[window_value - 1]
      for (i in Iter.range(0, k - 1)) {
        let wv = scalarWindows[i][j];
        if (wv > 0) {
          buckets[wv - 1] := g1_add(buckets[wv - 1], points[i]);
        };
      };

      // Bucket reduction via running sum
      var running = G1_INF;
      var windowSum = G1_INF;
      var b = numBuckets;
      while (b > 0) {
        b -= 1;
        running := g1_add(running, buckets[b]);
        windowSum := g1_add(windowSum, running);
      };

      windowResults[j] := windowSum;
    };

    // Combine windows: total = Σ windowResults[j] × 2^(j*c)
    // Process MSW to LSW with c doublings between each
    var total = windowResults[numWindows - 1];
    var w = numWindows - 1;
    while (w > 0) {
      w -= 1;
      for (_ in Iter.range(0, c - 1)) {
        total := g1_double(total);
      };
      total := g1_add(total, windowResults[w]);
    };

    total;
  };

  public func g2_msm(points : [G2Point], scalars : [Nat]) : G2Point {
    let k = points.size();
    if (k == 0) return G2_INF;
    if (k == 1) return g2_mul(points[0], scalars[0]);

    if (k <= 8) {
      var result = G2_INF;
      for (i in Iter.range(0, k - 1)) {
        result := g2_add(result, g2_mul(points[i], scalars[i]));
      };
      return result;
    };

    var c : Nat = 0;
    var temp = k;
    while (temp > 0) { c += 1; temp := temp / 2; };
    c -= 1;

    var windowSize : Nat = 1;
    for (_ in Iter.range(0, c - 1)) { windowSize *= 2; };
    let numBuckets : Nat = windowSize - 1;
    let numWindows : Nat = (256 + c - 1) / c;

    let scalarWindows = Array.tabulate<[var Nat]>(k, func(idx : Nat) : [var Nat] {
      let w = Array.init<Nat>(numWindows, 0);
      var s = scalars[idx];
      for (j in Iter.range(0, numWindows - 1)) {
        w[j] := s % windowSize;
        s := s / windowSize;
      };
      w;
    });

    let buckets = Array.init<G2Point>(numBuckets, G2_INF);
    let windowResults = Array.init<G2Point>(numWindows, G2_INF);

    for (j in Iter.range(0, numWindows - 1)) {
      for (b in Iter.range(0, numBuckets - 1)) {
        buckets[b] := G2_INF;
      };

      for (i in Iter.range(0, k - 1)) {
        let wv = scalarWindows[i][j];
        if (wv > 0) {
          buckets[wv - 1] := g2_add(buckets[wv - 1], points[i]);
        };
      };

      var running = G2_INF;
      var windowSum = G2_INF;
      var b = numBuckets;
      while (b > 0) {
        b -= 1;
        running := g2_add(running, buckets[b]);
        windowSum := g2_add(windowSum, running);
      };

      windowResults[j] := windowSum;
    };

    var total = windowResults[numWindows - 1];
    var w = numWindows - 1;
    while (w > 0) {
      w -= 1;
      for (_ in Iter.range(0, c - 1)) {
        total := g2_double(total);
      };
      total := g2_add(total, windowResults[w]);
    };

    total;
  };

  // ══════════════════════════════════════════════════════════════
  //  Hash-to-curve: MAP_FP_TO_G1 and MAP_FP2_TO_G2
  //  Using Simplified SWU map + isogeny
  //  Reference: RFC 9380
  // ══════════════════════════════════════════════════════════════

  // Constants for 11-isogeny map E'(Fp) -> E(Fp)
  // E': y² = x³ + A'x + B'
  // From RFC 9380 Appendix E.2
  let ISO11_A : Nat = 12190336318893619529228877361869031420615612348429846051986726275283378313155663745811710833465465981901188123677;
  let ISO11_B : Nat = 2906670324641927570491258158026293881577086121416628140204402091718288198173574630967936031029026176254968826637280;

  // SWU map for isogeny source E'
  public func swu_fp(u : Nat) : (Nat, Nat) {
    let um = fp_mod(u);
    let z : Nat = 11;
    let tv1 = fp_mul(z, fp_mul(um, um));
    let tv2 = fp_add(tv1, fp_mul(tv1, tv1));
    let tv3 = fp_add(tv2, 1);
    var x_den = fp_mul(fp_neg(ISO11_A), tv2);
    if (fp_mod(x_den) == 0) { x_den := fp_mul(ISO11_A, z) };
    let x = fp_div(fp_mul(ISO11_B, tv3), x_den);
    let gx = fp_add(fp_add(fp_mul(fp_mul(x, x), x), fp_mul(ISO11_A, x)), ISO11_B);
    switch (fp_sqrt(gx)) {
      case (?y) {
        let yf = if ((fp_mod(y) % 2) == (fp_mod(um) % 2)) { y } else { fp_neg(y) };
        (fp_mod(x), fp_mod(yf));
      };
      case null {
        let x2 = fp_mul(fp_mul(z, fp_mul(um, um)), x);
        let gx2 = fp_add(fp_add(fp_mul(fp_mul(x2, x2), x2), fp_mul(ISO11_A, x2)), ISO11_B);
        switch (fp_sqrt(gx2)) {
          case (?y2) {
            let yf = if ((fp_mod(y2) % 2) == (fp_mod(um) % 2)) { y2 } else { fp_neg(y2) };
            (fp_mod(x2), fp_mod(yf));
          };
          case null { (0, 0) };
        };
      };
    };
  };

  // 11-isogeny map coefficients (x_num, x_den, y_num, y_den)
  // x_num has 12 coefficients k_(1,i) for i=0..11
  // From RFC 9380 Appendix E.2
  let ISO11_XNUM : [Nat] = [
    2712959285290305970661081772124144179193819192423276218370281158706191519995889425075952244140278856085036081760695,
    3564859427549639835253027846704205725951033235539816243131874237388832081954622352624080767121604606753339903542203,
    2051387046688339481714726479723076305756384619135044672831882917686431912682625619320120082313093891743187631791280,
    3612713941521031012780325893181011392520079402153354595775735142359240110423346445050803899623018402874731133626465,
    2247053637822768981792833880270996398470828564809439728372634811976089874056583714987807553397615562273407692740057,
    3415427104483187489859740871640064348492611444552862448295571438270821994900526625562705192993481400731539293415811,
    2067521456483432583860405634125513059912765526223015704616050604591207046392807563217109432457129564962571408764292,
    3650721292069012982822225637849018828271936405382082649291891245623305084633066170122780668657208923883092359301262,
    1239271775787030039269460763652455868148971086016832054354147730155061349388626624328773377658494412538595239256855,
    3479374185711034293956731583912244564891370843071137483962415222733470401948838363051960066766720884717833231600798,
    2492756312273161536685660027440158956721981129429869601638362407515627529461742974364729223659746272460004902959995,
    1058488477413994682556770863004536636444795456512795473806825292198091015005841418695586811009326456605062948114985
  ];

  // x_den has 11 coefficients k_(2,i) for i=0..10
  // From RFC 9380 Appendix E.2
  let ISO11_XDEN : [Nat] = [
    1353092447850172218905095041059784486169131709710991428415161466575141675351394082965234118340787683181925558786844,
    2822220997908397120956501031591772354860004534930174057793539372552395729721474912921980407622851861692773516917759,
    1717937747208385987946072944131378949849282930538642983149296304709633281382731764122371874602115081850953846504985,
    501624051089734157816582944025690868317536915684467868346388760435016044027032505306995281054569109955275640941784,
    3025903087998593826923738290305187197829899948335370692927241015584233559365859980023579293766193297662657497834014,
    2224140216975189437834161136818943039444741035168992629437640302964164227138031844090123490881551522278632040105125,
    1146414465848284837484508420047674663876992808692209238763293935905506532411661921697047880549716175045414621825594,
    3179090966864399634396993677377903383656908036827452986467581478509513058347781039562481806409014718357094150199902,
    1549317016540628014674302140786462938410429359529923207442151939696344988707002602944342203885692366490121021806145,
    1442797143427491432630626390066422021593505165588630398337491100088557278058060064930663878153124164818522816175370,
    1
  ];

  // y_num has 16 coefficients k_(3,i) for i=0..15
  // From RFC 9380 Appendix E.2
  let ISO11_YNUM : [Nat] = [
    1393399195776646641963150658816615410692049723305861307490980409834842911816308830479576739332720113414154429643571,
    2968610969752762946134106091152102846225411740689724909058016729455736597929366401532929068084731548131227395540630,
    122933100683284845219599644396874530871261396084070222155796123161881094323788483360414289333111221370374027338230,
    303251954782077855462083823228569901064301365507057490567314302006681283228886645653148231378803311079384246777035,
    1353972356724735644398279028378555627591260676383150667237975415318226973994509601413730187583692624416197017403099,
    3443977503653895028417260979421240655844034880950251104724609885224259484262346958661845148165419691583810082940400,
    718493410301850496156792713845282235942975872282052335612908458061560958159410402177452633054233549648465863759602,
    1466864076415884313141727877156167508644960317046160398342634861648153052436926062434809922037623519108138661903145,
    1536886493137106337339531461344158973554574987550750910027365237255347020572858445054025958480906372033954157667719,
    2171468288973248519912068884667133903101171670397991979582205855298465414047741472281361964966463442016062407908400,
    3915937073730221072189646057898966011292434045388986394373682715266664498392389619761133407846638689998746172899634,
    3802409194827407598156407709510350851173404795262202653149767739163117554648574333789388883640862266596657730112910,
    1707589313757812493102695021134258021969283151093981498394095062397393499601961942449581422761005023512037430861560,
    349697005987545415860583335313370109325490073856352967581197273584891698473628451945217286148025358795756956811571,
    885704436476567581377743161796735879083481447641210566405057346859953524538988296201011389016649354976986251207243,
    3370924952219000111210625390420697640496067348723987858345031683392215988129398381698161406651860675722373763741188
  ];

  // y_den has 16 coefficients k_(4,i) for i=0..15
  // From RFC 9380 Appendix E.2
  let ISO11_YDEN : [Nat] = [
    3396434800020507717552209507749485772788165484415495716688989613875369612529138640646200921379825018840894888371137,
    3907278185868397906991868466757978732688957419873771881240086730384895060595583602347317992689443299391009456758845,
    854914566454823955479427412036002165304466268547334760894270240966182605542146252771872707010378658178126128834546,
    3496628876382137961119423566187258795236027183112131017519536056628828830323846696121917502443333849318934945158166,
    1828256966233331991927609917644344011503610008134915752990581590799656305331275863706710232159635159092657073225757,
    1362317127649143894542621413133849052553333099883364300946623208643344298804722863920546222860227051989127113848748,
    3443845896188810583748698342858554856823966611538932245284665132724280883115455093457486044009395063504744802318172,
    3484671274283470572728732863557945897902920439975203610275006103818288159899345245633896492713412187296754791689945,
    3755735109429418587065437067067640634211015783636675372165599470771975919172394156249639331555277748466603540045130,
    3459661102222301807083870307127272890283709299202626530836335779816726101522661683404130556379097384249447658110805,
    742483168411032072323733249644347333168432665415341249073150659015707795549260947228694495111018381111866512337576,
    1662231279858095762833829698537304807741442669992646287950513237989158777254081548205552083108208170765474149568658,
    1668238650112823419388205992952852912407572045257706138925379268508860023191233729074751042562151098884528280913356,
    369162719928976119195087327055926326601627748362769544198813069133429557026740823593067700396825489145575282378487,
    2164195715141237148945939585099633032390257748382945597506236650132835917087090097395995817229686247227784224263055,
    1
  ];

  // Evaluate polynomial: sum(coeffs[i] * x^i) for i=0..len-1
  func eval_poly_fp(coeffs : [Nat], x : Nat) : Nat {
    var result : Nat = 0;
    var xpow : Nat = 1;
    for (i in Iter.range(0, coeffs.size() - 1)) {
      result := fp_add(result, fp_mul(coeffs[i], xpow));
      xpow := fp_mul(xpow, x);
    };
    result;
  };

  // Apply 11-isogeny: map point on E' to E using rational maps
  // x = x_num(xp) / x_den(xp)
  // y = yp * y_num(xp) / y_den(xp)
  public func iso11_map(xp : Nat, yp : Nat) : (Nat, Nat) {
    let xn = eval_poly_fp(ISO11_XNUM, xp);
    let xd = eval_poly_fp(ISO11_XDEN, xp);
    let yn = eval_poly_fp(ISO11_YNUM, xp);
    let yd = eval_poly_fp(ISO11_YDEN, xp);
    let ox = fp_div(xn, xd);
    let oy = fp_mul(yp, fp_div(yn, yd));
    (fp_mod(ox), fp_mod(oy));
  };

  // Clear cofactor for G1:
  // Uses the efficient method from https://eprint.iacr.org/2019/403
  // clearCofactor(P) = [BLS_X]P + P = (BLS_X + 1) * P
  public func clear_cofactor_g1(p : G1Point) : G1Point {
    g1_add(g1_mul(p, BLS_X), p);
  };

  // ψ² (psi squared) endomorphism on G2: apply psi twice
  public func g2_psi2(p : G2Point) : G2Point {
    g2_psi(g2_psi(p));
  };

  // Clear cofactor for G2 (from RFC 9380 / Budroni-Pintore)
  // https://eprint.iacr.org/2017/419.pdf
  public func clear_cofactor_g2(p : G2Point) : G2Point {
    let t1 = g2_neg(g2_mul(p, BLS_X));           // [-x]P
    let psiP = g2_psi(p);                        // ψ(P)
    var t3 = g2_psi2(g2_double(p));              // ψ²(2P)
    t3 := g2_add(t3, g2_neg(psiP));              // ψ²(2P) - ψ(P)
    var t2 = g2_add(t1, psiP);                   // [-x]P + ψ(P)
    t2 := g2_neg(g2_mul(t2, BLS_X));             // [x²]P - [x]ψ(P)
    t3 := g2_add(t3, t2);                         // ψ²(2P) - ψ(P) + [x²]P - [x]ψ(P)
    t3 := g2_add(t3, g2_neg(t1));                // + [x]P
    g2_add(t3, g2_neg(p));                       // - P
  };

  // Full MAP_FP_TO_G1: SWU + 11-isogeny + cofactor clearing per EIP-2537
  public func map_fp_to_g1(u : Nat) : G1Point {
    let (xp, yp) = swu_fp(u);
    let (xe, ye) = iso11_map(xp, yp);
    clear_cofactor_g1({ x = xe; y = ye; z = 1 });
  };

  // sgn0 for Fp2 (RFC 9380 section 4.1, sgn0_m_eq_2)
  // Returns true if the element is "odd"
  public func sgn0_fp2(x : Fp2) : Bool {
    let sign_0 = fp_mod(x.0) % 2;
    let zero_0 = fp_mod(x.0) == 0;
    let sign_1 = fp_mod(x.1) % 2;
    sign_0 == 1 or (zero_0 and sign_1 == 1);
  };

  // MAP_FP2_TO_G2: SWU for Fp2 + 3-isogeny + clear cofactor
  // E2': y² = x³ + A2'x + B2'  (isogeny source)
  let ISO3_A2 : Fp2 = (0, 240);
  let ISO3_B2 : Fp2 = (1012, 1012);
  let MAP_G2_Z : Fp2 = (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786); // -(2+i) = (P-2, P-1)

  public func swu_fp2(u : Fp2) : (Fp2, Fp2) {
    let tv1 = fp2_mul(MAP_G2_Z, fp2_sq(u));
    let tv2 = fp2_add(tv1, fp2_sq(tv1));
    let tv3 = fp2_add(tv2, FP2_ONE);
    var xd = fp2_mul(fp2_neg(ISO3_A2), tv2);
    if (fp2_is_zero(xd)) { xd := fp2_mul(ISO3_A2, MAP_G2_Z) };
    let x_ = fp2_div(fp2_mul(ISO3_B2, tv3), xd);
    let gx = fp2_add(fp2_add(fp2_mul(fp2_sq(x_), x_), fp2_mul(ISO3_A2, x_)), ISO3_B2);
    switch (fp2_sqrt(gx)) {
      case (?y_) {
        let yf = if (sgn0_fp2(y_) == sgn0_fp2(u)) { y_ } else { fp2_neg(y_) };
        (x_, yf);
      };
      case null {
        let x2 = fp2_mul(fp2_mul(MAP_G2_Z, fp2_sq(u)), x_);
        let gx2 = fp2_add(fp2_add(fp2_mul(fp2_sq(x2), x2), fp2_mul(ISO3_A2, x2)), ISO3_B2);
        switch (fp2_sqrt(gx2)) {
          case (?y2) {
            let yf = if (sgn0_fp2(y2) == sgn0_fp2(u)) { y2 } else { fp2_neg(y2) };
            (x2, yf);
          };
          case null { (FP2_ZERO, FP2_ZERO) };
        };
      };
    };
  };

  // 3-isogeny map coefficients for G2 (from E2' to E2)
  // From RFC 9380 Appendix E.3
  let ISO3_XNUM_G2 : [Fp2] = [
    (889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542,
     889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542),
    (0,
     2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522),
    (2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526,
     1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261),
    (3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033,
     0)
  ];

  let ISO3_XDEN_G2 : [Fp2] = [
    (0, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715),
    (12, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775),
    (1, 0)
  ];

  let ISO3_YNUM_G2 : [Fp2] = [
    (3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558,
     3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558),
    (0,
     889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518),
    (2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524,
     1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263),
    (2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776,
     0)
  ];

  let ISO3_YDEN_G2 : [Fp2] = [
    (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355,
     4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355),
    (0,
     4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571),
    (18,
     4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769),
    (1, 0)
  ];

  // Evaluate polynomial with Fp2 coefficients using Horner's method (reverse order)
  func eval_poly_fp2(coeffs : [Fp2], x_ : Fp2) : Fp2 {
    let len = coeffs.size();
    var result = coeffs[len - 1];
    // Walk from index len-2 down to 0
    var j : Nat = 1;
    while (j < len) {
      result := fp2_add(fp2_mul(result, x_), coeffs[len - 1 - j]);
      j += 1;
    };
    result;
  };

  // Apply 3-isogeny map for G2
  public func iso3_map_g2(xp : Fp2, yp : Fp2) : (Fp2, Fp2) {
    let xn = eval_poly_fp2(ISO3_XNUM_G2, xp);
    let xd = eval_poly_fp2(ISO3_XDEN_G2, xp);
    let yn = eval_poly_fp2(ISO3_YNUM_G2, xp);
    let yd = eval_poly_fp2(ISO3_YDEN_G2, xp);
    let ox = fp2_div(xn, xd);
    let oy = fp2_mul(yp, fp2_div(yn, yd));
    (ox, oy);
  };

  // Full MAP_FP2_TO_G2: SWU + 3-isogeny + cofactor clearing per EIP-2537
  public func map_fp2_to_g2(u : Fp2) : G2Point {
    let (xp, yp) = swu_fp2(u);
    let (xe, ye) = iso3_map_g2(xp, yp);
    clear_cofactor_g2({ x = xe; y = ye; z = FP2_ONE });
  };

  // ══════════════════════════════════════════════════════════════
  //  Encoding / decoding for EIP-2537 precompile I/O
  // ══════════════════════════════════════════════════════════════

  // Read a 64-byte big-endian Fp element (16 zero padding + 48 data)
  public func decode_fp(input : [Nat8], offset : Nat) : ?Nat {
    if (offset + 64 > input.size()) return null;
    for (i in Iter.range(0, 15)) {
      if (input[offset + i] != 0) return null;
    };
    var result : Nat = 0;
    for (i in Iter.range(16, 63)) {
      result := result * 256 + Nat8.toNat(input[offset + i]);
    };
    if (result >= P) return null;
    ?result;
  };

  // Read 128-byte big-endian Fp2 (two 64-byte Fp: c0 then c1)
  public func decode_fp2(input : [Nat8], offset : Nat) : ?Fp2 {
    let ?c0 = decode_fp(input, offset) else return null;
    let ?c1 = decode_fp(input, offset + 64) else return null;
    ?(c0, c1);
  };

  // Encode Fp to 64 bytes
  public func encode_fp(value : Nat) : [Nat8] {
    let v = fp_mod(value);
    let buf = Buffer.Buffer<Nat8>(64);
    for (_ in Iter.range(0, 15)) { buf.add(0) };
    let bytes = Array.init<Nat8>(48, 0);
    var n = v;
    var idx : Nat = 47;
    while (n > 0) {
      bytes[idx] := Nat8.fromNat(n % 256);
      n := n / 256;
      if (idx > 0) { idx -= 1 } else { n := 0 };
    };
    for (b in bytes.vals()) { buf.add(b) };
    Buffer.toArray(buf);
  };

  public func encode_fp2(value : Fp2) : [Nat8] {
    let c0 = encode_fp(value.0);
    let c1 = encode_fp(value.1);
    let buf = Buffer.Buffer<Nat8>(128);
    for (b in c0.vals()) { buf.add(b) };
    for (b in c1.vals()) { buf.add(b) };
    Buffer.toArray(buf);
  };

  // Decode G1 point - curve check only (for G1ADD/G2ADD which don't need subgroup check)
  public func decode_g1_curve_only(input : [Nat8], offset : Nat) : ?G1Point {
    let ?x = decode_fp(input, offset) else return null;
    let ?y = decode_fp(input, offset + 64) else return null;
    if (x == 0 and y == 0) return ?G1_INF;
    if (not g1_is_on_curve(x, y)) return null;
    ?{ x = fp_mod(x); y = fp_mod(y); z = 1 };
  };

  // Decode G1 point with full subgroup check (for G1MUL, G1MSM, PAIRING)
  public func decode_g1(input : [Nat8], offset : Nat) : ?G1Point {
    let ?x = decode_fp(input, offset) else return null;
    let ?y = decode_fp(input, offset + 64) else return null;
    if (x == 0 and y == 0) return ?G1_INF;
    if (not g1_is_on_curve(x, y)) return null;
    let pt : G1Point = { x = x; y = y; z = 1 };
    if (not g1_subgroup_check(pt)) return null;
    ?pt;
  };

  // Decode G2 point - curve check only (for G2ADD which doesn't need subgroup check)
  public func decode_g2_curve_only(input : [Nat8], offset : Nat) : ?G2Point {
    let ?x = decode_fp2(input, offset) else return null;
    let ?y = decode_fp2(input, offset + 128) else return null;
    if (fp2_is_zero(x) and fp2_is_zero(y)) return ?G2_INF;
    if (not g2_is_on_curve(x, y)) return null;
    ?{ x = x; y = y; z = FP2_ONE };
  };

  // Decode G2 point with full subgroup check (for G2MUL, G2MSM, PAIRING)
  public func decode_g2(input : [Nat8], offset : Nat) : ?G2Point {
    let ?x = decode_fp2(input, offset) else return null;
    let ?y = decode_fp2(input, offset + 128) else return null;
    if (fp2_is_zero(x) and fp2_is_zero(y)) return ?G2_INF;
    if (not g2_is_on_curve(x, y)) return null;
    let pt : G2Point = { x = x; y = y; z = FP2_ONE };
    if (not g2_subgroup_check(pt)) return null;
    ?pt;
  };

  public func decode_scalar(input : [Nat8], offset : Nat) : Nat {
    var result : Nat = 0;
    for (i in Iter.range(0, 31)) {
      if (offset + i < input.size()) {
        result := result * 256 + Nat8.toNat(input[offset + i]);
      };
    };
    result;
  };

  public func encode_g1(p : G1Point) : [Nat8] {
    if (g1_is_inf(p)) return Array.tabulate<Nat8>(128, func(_ : Nat) : Nat8 { 0 });
    let (ax, ay) = g1_to_affine(p);
    let buf = Buffer.Buffer<Nat8>(128);
    for (b in encode_fp(ax).vals()) { buf.add(b) };
    for (b in encode_fp(ay).vals()) { buf.add(b) };
    Buffer.toArray(buf);
  };

  public func encode_g2(p : G2Point) : [Nat8] {
    if (g2_is_inf(p)) return Array.tabulate<Nat8>(256, func(_ : Nat) : Nat8 { 0 });
    let (ax, ay) = g2_to_affine(p);
    let buf = Buffer.Buffer<Nat8>(256);
    for (b in encode_fp2(ax).vals()) { buf.add(b) };
    for (b in encode_fp2(ay).vals()) { buf.add(b) };
    Buffer.toArray(buf);
  };

  // ══════════════════════════════════════════════════════════════
  //  Generator points
  // ══════════════════════════════════════════════════════════════

  public let G1_GEN : G1Point = {
    x = 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507;
    y = 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569;
    z = 1;
  };

  public let G2_GEN : G2Point = {
    x = (352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160,
         3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758);
    y = (1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905,
         927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582);
    z = FP2_ONE;
  };

  // KZG trusted setup G2[1] (tau * G2) from the Ethereum KZG ceremony
  // Source: c-kzg-4844 trusted_setup.txt line 4100 (g2_monomial[1])
  // Compressed: b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2
  public let KZG_G2_SETUP_1 : G2Point = {
    x = (3749701713850085193403383609513386037494151572263731328608276629425322978272408394373143740944003571525027436289778,
         3347537128081568434923729147580015899756771550835613107520576615563260658656019591232316627827007503930666726825842);
    y = (194392958648403190675529552496435226424111592982833162118538452666741235889530674000225873281133418439621742897817,
         3447898402727835650716129438012169492682148398295533958400255525306573911008434577489634554212211450783070687991119);
    z = FP2_ONE;
  };

  // ══════════════════════════════════════════════════════════════
  //  Compressed G1 point decoding (48 bytes, Zcash format)
  //  Used by EIP-4844 KZG point evaluation precompile
  // ══════════════════════════════════════════════════════════════

  public func decompress_g1(data : [Nat8]) : ?G1Point {
    // Must be exactly 48 bytes
    if (data.size() != 48) return null;

    // Flags are in the top 3 bits of the first byte
    let flags = data[0] >> 5;
    let compressed_flag = (flags >> 2) & 1; // bit 7
    let infinity_flag = (flags >> 1) & 1;   // bit 6
    let sort_flag = flags & 1;              // bit 5

    // Must be compressed format
    if (compressed_flag != 1) return null;

    // Point at infinity
    if (infinity_flag == 1) {
      // sort_flag must be 0, remaining bytes must be 0
      if (sort_flag != 0) return null;
      var i = 1;
      while (i < 48) {
        if (data[i] != 0) return null;
        i += 1;
      };
      // Check first byte after clearing flags
      if (data[0] & 0x1F != 0) return null;
      return ?G1_INF;
    };

    // Extract x coordinate (big-endian, 48 bytes, clear flag bits in first byte)
    var x : Nat = Nat8.toNat(data[0] & 0x1F);
    var i = 1;
    while (i < 48) {
      x := x * 256 + Nat8.toNat(data[i]);
      i += 1;
    };

    // x must be < P
    if (x >= P) return null;

    // Compute y² = x³ + 4
    let x2 = fp_mul(x, x);
    let x3 = fp_mul(x2, x);
    let rhs = fp_add(x3, 4);

    // Compute sqrt
    let ?y_abs = fp_sqrt(rhs) else return null;

    // Apply sign: sort_flag=1 means y > (P-1)/2
    let half_p = (P - 1) / 2;
    let y = if (sort_flag == 1) {
      if (y_abs > half_p) { y_abs } else { P - y_abs };
    } else {
      if (y_abs > half_p) { P - y_abs } else { y_abs };
    };

    // On-curve check is implicit (we computed y from x³+4)
    ?{ x = fp_mod(x); y = fp_mod(y); z = 1 };
  };

  // ══════════════════════════════════════════════════════════════
  //  Gas costs (EIP-2537 Pectra update)
  // ══════════════════════════════════════════════════════════════

  public let GAS_G1ADD : Nat = 375;
  public let GAS_G1MUL : Nat = 12000;
  public let GAS_G2ADD : Nat = 600;
  public let GAS_G2MUL : Nat = 22500;
  public let GAS_PAIRING_BASE : Nat = 37700;
  public let GAS_PAIRING_PER_PAIR : Nat = 32600;
  public let GAS_MAP_FP_TO_G1 : Nat = 5500;
  public let GAS_MAP_FP2_TO_G2 : Nat = 23800;

  public func gas_g1_msm(k : Nat) : Nat {
    if (k == 0) return 0;
    (k * GAS_G1MUL * g1_msm_discount(k)) / 1000;
  };

  public func gas_g2_msm(k : Nat) : Nat {
    if (k == 0) return 0;
    (k * GAS_G2MUL * g2_msm_discount(k)) / 1000;
  };

  func g1_msm_discount(k : Nat) : Nat {
    let table : [Nat] = [
      1000, 949, 848, 797, 764, 750, 738, 728, 719, 712,
      705, 698, 692, 687, 682, 677, 673, 669, 665, 661,
      658, 654, 651, 648, 645, 642, 640, 637, 635, 632,
      630, 627, 625, 623, 621, 619, 617, 615, 613, 611,
      609, 608, 606, 604, 603, 601, 599, 598, 596, 595,
      593, 592, 591, 589, 588, 586, 585, 584, 582, 581,
      580, 579, 577, 576, 575, 574, 573, 572, 570, 569,
      568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
      558, 557, 556, 555, 554, 553, 552, 551, 550, 549,
      548, 547, 547, 546, 545, 544, 543, 542, 541, 540,
      540, 539, 538, 537, 536, 536, 535, 534, 533, 532,
      532, 531, 530, 529, 528, 528, 527, 526, 525, 525,
      524, 523, 522, 522, 521, 520, 520, 519
    ];
    if (k <= table.size()) { table[k - 1] } else { 519 };
  };

  func g2_msm_discount(k : Nat) : Nat {
    let table : [Nat] = [
      1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770,
      759, 749, 740, 732, 724, 717, 711, 704, 699, 693,
      688, 683, 679, 674, 670, 666, 663, 659, 655, 652,
      649, 646, 643, 640, 637, 634, 632, 629, 627, 624,
      622, 620, 618, 615, 613, 611, 609, 607, 606, 604,
      602, 600, 598, 597, 595, 593, 592, 590, 589, 587,
      586, 584, 583, 582, 580, 579, 578, 576, 575, 574,
      573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
      561, 560, 559, 558, 557, 556, 555, 554, 553, 552,
      552, 551, 550, 549, 548, 547, 546, 545, 545, 544,
      543, 542, 541, 541, 540, 539, 538, 537, 537, 536,
      535, 535, 534, 533, 532, 532, 531, 530, 530, 529,
      528, 528, 527, 526, 526, 525, 524, 524
    ];
    if (k <= table.size()) { table[k - 1] } else { 524 };
  };

};
