# Changelog

## 0.1.0 — Unreleased

- Initial ICDevs release of BLS12-381 field, curve, hash-to-curve, encoding, multi-scalar multiplication, and pairing operations.
- EIP-2537-compatible test-canister interface.
- Deterministic and randomized correctness comparisons against `@noble/curves`.
- Montgomery-field and pairing performance benchmarks.
- Migrated the implementation, test canister, and benchmarks from `mo:base` to `mo:core` on moc 1.8.2.
- Replaced temporary mutable buffers with fixed arrays or `PureList` accumulators; the post-migration benchmark is neutral overall and improves two-pair Miller-loop instructions and garbage collection by approximately 0.03% and 0.05%, respectively.
