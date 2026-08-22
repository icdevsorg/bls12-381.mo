// BLS12-381 test canister: exposes individual BLS operations for testing
import BLS "../../src/lib";
import Array "mo:core/Array";
import Nat8 "mo:core/Nat8";
import PureList "mo:core/pure/List";
import VarArray "mo:core/VarArray";

persistent actor {

  // ══════════════════════════════════════════════════════════════
  //  Helpers: Nat8 array <-> Int conversions
  // ══════════════════════════════════════════════════════════════

  // Decode a big-endian unsigned integer from a Nat8 array
  func bytesToNat(bytes : [Nat8]) : Nat {
    var result : Nat = 0;
    for (b in bytes.vals()) {
      result := result * 256 + Nat8.toNat(b);
    };
    result;
  };

  // Encode a Nat as a fixed-length big-endian Nat8 array
  func natToBytes(n : Nat, len : Nat) : [Nat8] {
    let buf = VarArray.repeat<Nat8>(0, len);
    var val = n;
    var idx = len;
    while (val > 0 and idx > 0) {
      idx -= 1;
      buf[idx] := Nat8.fromNat(val % 256);
      val := val / 256;
    };
    VarArray.toArray(buf);
  };

  // Decode a big-endian Fp element (48 bytes)
  func bytesToFp(bytes : [Nat8]) : Nat {
    var result : Nat = 0;
    for (b in bytes.vals()) {
      result := result * 256 + Nat8.toNat(b);
    };
    result;
  };

  // Encode Fp element as 48-byte big-endian
  func fpToBytes(val : Nat) : [Nat8] {
    let v = BLS.fp_mod(val);
    natToBytes(v, 48);
  };

  // ══════════════════════════════════════════════════════════════
  //  Fp arithmetic tests
  // ══════════════════════════════════════════════════════════════

  // All Fp functions take/return 48-byte big-endian representations

  public query func fp_add(a : [Nat8], b : [Nat8]) : async [Nat8] {
    fpToBytes(BLS.fp_add(bytesToFp(a), bytesToFp(b)));
  };

  public query func fp_sub(a : [Nat8], b : [Nat8]) : async [Nat8] {
    fpToBytes(BLS.fp_sub(bytesToFp(a), bytesToFp(b)));
  };

  public query func fp_mul(a : [Nat8], b : [Nat8]) : async [Nat8] {
    fpToBytes(BLS.fp_mul(bytesToFp(a), bytesToFp(b)));
  };

  public query func fp_inv(a : [Nat8]) : async [Nat8] {
    fpToBytes(BLS.fp_inv(bytesToFp(a)));
  };

  public query func fp_neg(a : [Nat8]) : async [Nat8] {
    fpToBytes(BLS.fp_neg(bytesToFp(a)));
  };

  public query func fp_pow(base_ : [Nat8], exp_ : [Nat8]) : async [Nat8] {
    fpToBytes(BLS.fp_pow(bytesToFp(base_), bytesToNat(exp_)));
  };

  public query func fp_sqrt(a : [Nat8]) : async ?[Nat8] {
    switch (BLS.fp_sqrt(bytesToFp(a))) {
      case (?r) { ?fpToBytes(r) };
      case null { null };
    };
  };

  // ══════════════════════════════════════════════════════════════
  //  Fp2 arithmetic tests
  // ══════════════════════════════════════════════════════════════

  // Fp2 = (c0, c1) encoded as two 48-byte values concatenated (96 bytes)

  func decodeFp2(bytes : [Nat8]) : BLS.Fp2 {
    let c0 = bytesToFp(Array.tabulate<Nat8>(48, func(i : Nat) : Nat8 { bytes[i] }));
    let c1 = bytesToFp(Array.tabulate<Nat8>(48, func(i : Nat) : Nat8 { bytes[48 + i] }));
    (c0, c1);
  };

  func encodeFp2(fp2 : BLS.Fp2) : [Nat8] {
    let c0 = fpToBytes(fp2.0);
    let c1 = fpToBytes(fp2.1);
    Array.concat(c0, c1);
  };

  public query func fp2_add(a : [Nat8], b : [Nat8]) : async [Nat8] {
    encodeFp2(BLS.fp2_add(decodeFp2(a), decodeFp2(b)));
  };

  public query func fp2_sub(a : [Nat8], b : [Nat8]) : async [Nat8] {
    encodeFp2(BLS.fp2_sub(decodeFp2(a), decodeFp2(b)));
  };

  public query func fp2_mul(a : [Nat8], b : [Nat8]) : async [Nat8] {
    encodeFp2(BLS.fp2_mul(decodeFp2(a), decodeFp2(b)));
  };

  public query func fp2_sq(a : [Nat8]) : async [Nat8] {
    encodeFp2(BLS.fp2_sq(decodeFp2(a)));
  };

  public query func fp2_inv(a : [Nat8]) : async [Nat8] {
    encodeFp2(BLS.fp2_inv(decodeFp2(a)));
  };

  public query func fp2_neg(a : [Nat8]) : async [Nat8] {
    encodeFp2(BLS.fp2_neg(decodeFp2(a)));
  };

  // ══════════════════════════════════════════════════════════════
  //  G1 point operations
  // ══════════════════════════════════════════════════════════════

  // G1 points encoded as per EIP-2537: 128 bytes (64-byte x + 64-byte y)
  // Using the existing BLS.decode_g1_curve_only / BLS.encode_g1

  public query func g1_add(a : [Nat8], b : [Nat8]) : async [Nat8] {
    let ?pa = BLS.decode_g1_curve_only(a, 0) else return [];
    let ?pb = BLS.decode_g1_curve_only(b, 0) else return [];
    BLS.encode_g1(BLS.g1_add(pa, pb));
  };

  public query func g1_mul(point : [Nat8], scalar : [Nat8]) : async [Nat8] {
    let ?p = BLS.decode_g1_curve_only(point, 0) else return [];
    let s = bytesToNat(scalar);
    BLS.encode_g1(BLS.g1_mul(p, s));
  };

  public query func g1_neg(point : [Nat8]) : async [Nat8] {
    let ?p = BLS.decode_g1_curve_only(point, 0) else return [];
    BLS.encode_g1(BLS.g1_neg(p));
  };

  public query func g1_is_on_curve(point : [Nat8]) : async Bool {
    let ?_p = BLS.decode_g1_curve_only(point, 0) else return false;
    true;
  };

  public query func g1_subgroup_check(point : [Nat8]) : async Bool {
    let ?p = BLS.decode_g1_curve_only(point, 0) else return false;
    BLS.g1_subgroup_check(p);
  };

  // ══════════════════════════════════════════════════════════════
  //  G2 point operations
  // ══════════════════════════════════════════════════════════════

  // G2 points encoded as per EIP-2537: 256 bytes
  public query func g2_add(a : [Nat8], b : [Nat8]) : async [Nat8] {
    let ?pa = BLS.decode_g2_curve_only(a, 0) else return [];
    let ?pb = BLS.decode_g2_curve_only(b, 0) else return [];
    BLS.encode_g2(BLS.g2_add(pa, pb));
  };

  public query func g2_mul(point : [Nat8], scalar : [Nat8]) : async [Nat8] {
    let ?p = BLS.decode_g2_curve_only(point, 0) else return [];
    let s = bytesToNat(scalar);
    BLS.encode_g2(BLS.g2_mul(p, s));
  };

  public query func g2_is_on_curve(point : [Nat8]) : async Bool {
    let ?_p = BLS.decode_g2_curve_only(point, 0) else return false;
    true;
  };

  public query func g2_subgroup_check(point : [Nat8]) : async Bool {
    let ?p = BLS.decode_g2_curve_only(point, 0) else return false;
    BLS.g2_subgroup_check(p);
  };

  // ══════════════════════════════════════════════════════════════
  //  Hash-to-curve: MAP operations (the broken ones!)
  // ══════════════════════════════════════════════════════════════

  // MAP_FP_TO_G1: takes a 64-byte Fp element, returns a 128-byte G1 point
  public query func map_fp_to_g1(fp_input : [Nat8]) : async [Nat8] {
    let ?u = BLS.decode_fp(fp_input, 0) else return [];
    let result = BLS.map_fp_to_g1(u);
    BLS.encode_g1(result);
  };

  // MAP_FP2_TO_G2: takes a 128-byte Fp2 element, returns a 256-byte G2 point
  public query func map_fp2_to_g2(fp2_input : [Nat8]) : async [Nat8] {
    let ?u = BLS.decode_fp2(fp2_input, 0) else return [];
    let result = BLS.map_fp2_to_g2(u);
    BLS.encode_g2(result);
  };

  // ══════════════════════════════════════════════════════════════
  //  Internal diagnostic: expose SWU and isogeny separately
  // ══════════════════════════════════════════════════════════════

  // SWU map only (before isogeny) — returns point on E'
  public query func swu_fp(u : [Nat8]) : async [Nat8] {
    let fp = bytesToFp(u);
    let (x, y) = BLS.swu_fp(fp);
    // Return as two 48-byte values
    let bx = fpToBytes(x);
    let by = fpToBytes(y);
    Array.concat(bx, by);
  };

  // Isogeny map only (without SWU)
  public query func iso11_map(xp : [Nat8], yp : [Nat8]) : async [Nat8] {
    let x = bytesToFp(xp);
    let y = bytesToFp(yp);
    let (ox, oy) = BLS.iso11_map(x, y);
    let bx = fpToBytes(ox);
    let by = fpToBytes(oy);
    Array.concat(bx, by);
  };

  // Evaluate a single polynomial (for debugging coefficient issues)
  // poly_type: 0=XNUM, 1=XDEN, 2=YNUM, 3=YDEN
  // Returns the polynomial value as 48 bytes
  // NOTE: We can't directly access the private arrays, so we go through iso11_map
  // Instead, expose eval_poly_fp indirectly via the full map

  // ══════════════════════════════════════════════════════════════
  //  Pairing
  // ══════════════════════════════════════════════════════════════

  // pairing_check: takes array of (G1, G2) pairs, returns bool
  // Each pair is 128 + 256 = 384 bytes
  public query func pairing_check(input : [Nat8]) : async Bool {
    if (input.size() % 384 != 0) return false;
    let numPairs = input.size() / 384;
    var pairs = PureList.empty<(BLS.G1Point, BLS.G2Point)>();

    var i = 0;
    while (i < numPairs) {
      let offset = i * 384;
      let ?g1 = BLS.decode_g1(input, offset) else return false;
      let ?g2 = BLS.decode_g2(input, offset + 128) else return false;
      pairs := PureList.pushFront(pairs, (g1, g2));
      i += 1;
    };

    BLS.pairing_check(PureList.toArray(pairs));
  };

  // Single pairing: compute e(P, Q) and return Fp12 as serialized bytes
  // Useful for comparing intermediate pairing values
  public query func pairing(g1_input : [Nat8], g2_input : [Nat8]) : async [Nat8] {
    let ?p = BLS.decode_g1(g1_input, 0) else return [];
    let ?q = BLS.decode_g2(g2_input, 0) else return [];
    let result = BLS.pairing(p, q);
    // Serialize Fp12 as 12 * 48 = 576 bytes (each Fp2 component = 2*48 bytes)
    // Fp12 = (Fp6, Fp6), Fp6 = (Fp2, Fp2, Fp2)
    let components : [(Nat, Nat)] = [
      result.0.0, result.0.1, result.0.2,
      result.1.0, result.1.1, result.1.2
    ];
    Array.flatten(Array.map<(Nat, Nat), [Nat8]>(components, func(c) {
      Array.concat(fpToBytes(c.0), fpToBytes(c.1));
    }));
  };

  // ══════════════════════════════════════════════════════════════
  //  MSM (multi-scalar multiplication)
  // ══════════════════════════════════════════════════════════════

  public query func g1_msm(points_bytes : [Nat8], scalars_bytes : [Nat8]) : async [Nat8] {
    let numPoints = points_bytes.size() / 128;
    let numScalars = scalars_bytes.size() / 32;
    if (numPoints != numScalars or numPoints == 0) return [];

    var points = PureList.empty<BLS.G1Point>();
    var scalars = PureList.empty<Nat>();

    var i = 0;
    while (i < numPoints) {
      let ?p = BLS.decode_g1_curve_only(points_bytes, i * 128) else return [];
      points := PureList.pushFront(points, p);
      scalars := PureList.pushFront(scalars, BLS.decode_scalar(scalars_bytes, i * 32));
      i += 1;
    };

    BLS.encode_g1(BLS.g1_msm(PureList.toArray(points), PureList.toArray(scalars)));
  };

  public query func g2_msm(points_bytes : [Nat8], scalars_bytes : [Nat8]) : async [Nat8] {
    let numPoints = points_bytes.size() / 256;
    let numScalars = scalars_bytes.size() / 32;
    if (numPoints != numScalars or numPoints == 0) return [];

    var points = PureList.empty<BLS.G2Point>();
    var scalars = PureList.empty<Nat>();

    var i = 0;
    while (i < numPoints) {
      let ?p = BLS.decode_g2_curve_only(points_bytes, i * 256) else return [];
      points := PureList.pushFront(points, p);
      scalars := PureList.pushFront(scalars, BLS.decode_scalar(scalars_bytes, i * 32));
      i += 1;
    };

    BLS.encode_g2(BLS.g2_msm(PureList.toArray(points), PureList.toArray(scalars)));
  };

  // ══════════════════════════════════════════════════════════════
  //  Encode/Decode verification helpers
  // ══════════════════════════════════════════════════════════════

  public query func encode_fp(val : [Nat8]) : async [Nat8] {
    BLS.encode_fp(bytesToFp(val));
  };

  public query func decode_fp(val : [Nat8]) : async ?[Nat8] {
    switch (BLS.decode_fp(val, 0)) {
      case (?v) { ?fpToBytes(v) };
      case null { null };
    };
  };

  // Debug: raw SWU output for Fp2 (before isogeny and clearing)
  public query func debug_swu_fp2(c0 : [Nat8], c1 : [Nat8]) : async ([Nat8], [Nat8], [Nat8], [Nat8]) {
    let u : BLS.Fp2 = (bytesToFp(c0), bytesToFp(c1));
    let (xp, yp) = BLS.swu_fp2(u);
    (fpToBytes(BLS.fp_mod(xp.0)), fpToBytes(BLS.fp_mod(xp.1)), fpToBytes(BLS.fp_mod(yp.0)), fpToBytes(BLS.fp_mod(yp.1)));
  };

  // Debug: SWU+iso3 output for Fp2 (before clearing)
  public query func debug_iso3_fp2(c0 : [Nat8], c1 : [Nat8]) : async ([Nat8], [Nat8], [Nat8], [Nat8]) {
    let u : BLS.Fp2 = (bytesToFp(c0), bytesToFp(c1));
    let (xp, yp) = BLS.swu_fp2(u);
    let (xe, ye) = BLS.iso3_map_g2(xp, yp);
    (fpToBytes(BLS.fp_mod(xe.0)), fpToBytes(BLS.fp_mod(xe.1)), fpToBytes(BLS.fp_mod(ye.0)), fpToBytes(BLS.fp_mod(ye.1)));
  };

  // Simple health check
  public query func get_p() : async [Nat8] {
    natToBytes(BLS.P, 48);
  };

  public query func get_r() : async [Nat8] {
    natToBytes(BLS.R_, 32);
  };
};
