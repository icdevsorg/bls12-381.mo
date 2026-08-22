import Bench "mo:bench";
import BLS "../src/lib";

module {
  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("BLS12-381 Operations");
    bench.description("Benchmark key BLS12-381 operations: field arithmetic, group operations, pairing, hash-to-curve");
    bench.cols(["1_op"]);
    bench.rows([
      "fp_mul",
      "fp_inv",
      "fp_pow(small)",
      "fp_sqrt",
      "fp2_mul",
      "fp2_inv",
      "fp2_sqrt",
      "g1_add",
      "g1_double",
      "g1_mul(scalar)",
      "g2_add",
      "g2_double",
      "g2_mul(scalar)",
      "fp6_mul",
      "fp6_sq",
      "fp12_mul",
      "fp12_sq",
      "fp12_cyclotomic_sq",
      "miller_loop",
      "final_exponentiation",
      "pairing",
      "pairing_check(1_pair)",
      "map_fp_to_g1",
      "map_fp2_to_g2",
      "g1_msm(2_points)",
      "g2_msm(2_points)",
      "decompress_g1",
      "multi_miller_loop(2_pairs)",
      "separate_miller_x2",
      "pairing_check(2_pairs)",
    ]);

    // G1 generator
    let g1 : BLS.G1Point = BLS.G1_GEN;
    let g1_2 = BLS.g1_double(g1);

    // G2 generator
    let g2 : BLS.G2Point = BLS.G2_GEN;
    let g2_2 = BLS.g2_double(g2);

    // Fp test values (Nat based)
    let a : Nat = 1234567890123456789012345678901234567890123456789012345678901234567890;
    let b : Nat = 9876543210987654321098765432109876543210987654321098765432109876543210;

    // Fp2 test values
    let fp2a : BLS.Fp2 = (a, b);
    let fp2b : BLS.Fp2 = (b, a);

    // Fp6 test values
    let fp6a : BLS.Fp6 = ((a, b), (b, a), (a, a));
    let fp6b : BLS.Fp6 = ((b, a), (a, b), (b, b));

    // Fp12 test value (use a miller loop result for realistic input)
    let fp12a = BLS.miller_loop(g1, g2);
    let fp12b = BLS.final_exponentiation(fp12a);

    // Scalar for mul operations
    let scalar : Nat = 42;

    // Compressed G1 generator (48 bytes, BLS12-381 standard compressed form)
    // This is the compressed form of G1_GEN with the compression flag set
    let compressed_g1 : [Nat8] = [
      0x97, 0xf1, 0xd3, 0xa7, 0x31, 0x97, 0xd7, 0x94,
      0x26, 0x95, 0x63, 0x8c, 0x4f, 0xa9, 0xac, 0x0f,
      0xc3, 0x68, 0x8c, 0x4f, 0x97, 0x74, 0xb9, 0x05,
      0xa1, 0x4e, 0x3a, 0x3f, 0x17, 0x1b, 0xac, 0x58,
      0x6c, 0x55, 0xe8, 0x3f, 0xf9, 0x7a, 0x1a, 0xef,
      0xfb, 0x3a, 0xf0, 0x0a, 0xdb, 0x22, 0xc6, 0xbb,
    ];

    // 2-pair test data for pairing bench (e(G1,G2) * e(-G1,G2) = 1)
    let neg_g1 = BLS.g1_neg(g1);
    let two_pairs : [(BLS.G1Point, BLS.G2Point)] = [(g1, g2), (neg_g1, g2)];

    bench.runner(func(row, _col) {
      switch(row) {
        case("fp_mul") {
          ignore BLS.fp_mul(a, b);
        };
        case("fp_inv") {
          ignore BLS.fp_inv(a);
        };
        case("fp_pow(small)") {
          ignore BLS.fp_pow(a, 65537);
        };
        case("fp_sqrt") {
          ignore BLS.fp_sqrt(a);
        };
        case("fp2_mul") {
          ignore BLS.fp2_mul(fp2a, fp2b);
        };
        case("fp2_inv") {
          ignore BLS.fp2_inv(fp2a);
        };
        case("fp2_sqrt") {
          ignore BLS.fp2_sqrt(fp2a);
        };
        case("g1_add") {
          ignore BLS.g1_add(g1, g1_2);
        };
        case("g1_double") {
          ignore BLS.g1_double(g1);
        };
        case("g1_mul(scalar)") {
          ignore BLS.g1_mul(g1, scalar);
        };
        case("g2_add") {
          ignore BLS.g2_add(g2, g2_2);
        };
        case("g2_double") {
          ignore BLS.g2_double(g2);
        };
        case("g2_mul(scalar)") {
          ignore BLS.g2_mul(g2, scalar);
        };
        case("fp6_mul") {
          ignore BLS.fp6_mul(fp6a, fp6b);
        };
        case("fp6_sq") {
          ignore BLS.fp6_sq(fp6a);
        };
        case("fp12_mul") {
          ignore BLS.fp12_mul(fp12a, fp12a);
        };
        case("fp12_sq") {
          ignore BLS.fp12_sq(fp12a);
        };
        case("fp12_cyclotomic_sq") {
          ignore BLS.fp12_cyclotomic_sq(fp12b);
        };
        case("miller_loop") {
          ignore BLS.miller_loop(g1, g2);
        };
        case("final_exponentiation") {
          ignore BLS.final_exponentiation(fp12a);
        };
        case("pairing") {
          ignore BLS.pairing(g1, g2);
        };
        case("pairing_check(1_pair)") {
          ignore BLS.pairing_check([(g1, g2)]);
        };
        case("map_fp_to_g1") {
          ignore BLS.map_fp_to_g1(42);
        };
        case("map_fp2_to_g2") {
          ignore BLS.map_fp2_to_g2((42, 7));
        };
        case("g1_msm(2_points)") {
          ignore BLS.g1_msm([g1, g1_2], [3, 5]);
        };
        case("g2_msm(2_points)") {
          ignore BLS.g2_msm([g2, g2_2], [3, 5]);
        };
        case("decompress_g1") {
          ignore BLS.decompress_g1(compressed_g1);
        };
        case("multi_miller_loop(2_pairs)") {
          ignore BLS.multi_miller_loop(two_pairs);
        };
        case("separate_miller_x2") {
          let m1 = BLS.miller_loop(two_pairs[0].0, two_pairs[0].1);
          let m2 = BLS.miller_loop(two_pairs[1].0, two_pairs[1].1);
          ignore BLS.fp12_mul(m1, m2);
        };
        case("pairing_check(2_pairs)") {
          ignore BLS.pairing_check(two_pairs);
        };
        case(_) {};
      };
    });

    bench;
  };
};
