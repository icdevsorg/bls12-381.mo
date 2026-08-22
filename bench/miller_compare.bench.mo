import Bench "mo:bench";
import BLS "../src/lib";

module {
  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Miller Loop Comparison");
    bench.description("Compare multi_miller_loop vs separate miller_loops for 2 pairs");
    bench.cols(["1_op"]);
    bench.rows([
      "multi_miller_loop(2_pairs)",
      "separate_miller_x2",
    ]);

    // G1/G2 generators and negation for 2-pair test
    let g1 : BLS.G1Point = BLS.G1_GEN;
    let g2 : BLS.G2Point = BLS.G2_GEN;
    let neg_g1 = BLS.g1_neg(g1);
    let two_pairs : [(BLS.G1Point, BLS.G2Point)] = [(g1, g2), (neg_g1, g2)];

    bench.runner(func(row, _col) {
      switch(row) {
        case("multi_miller_loop(2_pairs)") {
          ignore BLS.multi_miller_loop(two_pairs);
        };
        case("separate_miller_x2") {
          let m1 = BLS.miller_loop(two_pairs[0].0, two_pairs[0].1);
          let m2 = BLS.miller_loop(two_pairs[1].0, two_pairs[1].1);
          ignore BLS.fp12_mul(m1, m2);
        };
        case(_) {};
      };
    });

    bench;
  };
};
