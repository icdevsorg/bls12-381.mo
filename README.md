# BLS12-381.mo

BLS12-381 elliptic-curve and pairing operations for Motoko, including the operations required by Ethereum's EIP-2537 precompile interface.

> [!WARNING]
> This package has not received an independent cryptographic security audit. Review it carefully before using it to protect production assets or consensus-critical state.

## Installation

After the first Mops release is published:

```sh
mops add bls12-381
```

```motoko
import BLS "mo:bls12-381";
```

The public API is exported by `src/lib.mo`. It includes field-tower arithmetic, G1 and G2 point operations, encoding and decoding, hash-to-curve helpers, multi-scalar multiplication, and pairing checks.

## Verification

```sh
mops install
dfx build --check bls_test
npm ci
npm test -- --runInBand
mops bench
```

The randomized pairing/MSM suite is computationally expensive and should run in release CI with a generous timeout. Saved `.bench/` results are local artifacts and are not published.

## Provenance and licensing

The implementation was developed for ICDevs and is licensed under Apache-2.0. Constants and algorithm structure were checked against `@noble/curves`; its MIT attribution is recorded in [THIRD_PARTY_LICENSES.md](THIRD_PARTY_LICENSES.md). Ethereum EIP-2537 defines the externally compatible operation set.

## Release policy

Releases require a clean dependency installation, `dfx build --check bls_test`, the deterministic and randomized Noble-reference suites, and an EVM downstream build/test checkpoint.
