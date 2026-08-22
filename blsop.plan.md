# BLS12-381 Montgomery Form Optimization Plan

## Goal
Rewrite BLS12-381 Fp arithmetic from unbounded `Int` to Montgomery form using 6×Nat64 limbs.
Target: 3-5× speedup on pairing (15B → 3-5B instructions).

## Current Architecture
- `src/lib.mo` (1603 lines): Single module, all arithmetic uses `Int`
- Hot path: `fp_mul(a,b) = (a * b) % P` — 762-bit multiply + 381-bit division
- P = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
- P fits in 6 × 64-bit limbs (381 bits)

## Montgomery Form Overview
Store field elements as `a * R mod P` where R = 2^384.
- `mont_mul(aR, bR) = aR * bR * R^{-1} mod P = (a*b)*R mod P`
- Avoids full division — uses REDC (Montgomery reduction)
- Need: R^2 mod P (for to_mont), R^{-1} mod P (for from_mont), N' = -P^{-1} mod 2^64

## Verified Nat64 Operations (moc 1.1.0)
- `*%` wrapping multiply, `+%` wrapping add, `-%` wrapping subtract
- `>>`, `<<` bit shifts
- `Prim.nat64ToNat`, `Prim.natToNat64`
- `Nat64.bitnot`
- Wide multiply: go through Nat (`nat64ToNat(a) * nat64ToNat(b)`) then extract lo/hi
- NO native 64×64→128 intrinsic — must use Nat intermediary or split-limb approach

## Limb Representation Decision
Since there's no native wide multiply, we have two choices:
1. **6×Nat64 limbs** with wide multiply via Nat conversion (2 conversions per multiply)
2. **12×Nat32 limbs** with native 32×32→64 via `*%` on Nat64-promoted values

**Choice: 6×Nat64 with Nat intermediary for wide multiply.**
Rationale: Fewer limb operations (6 vs 12 means 36 vs 144 partial products). The Nat conversion cost is amortized. We can also try a hybrid: use `*%` for the low 64 bits and compute carry via Nat.

**Alternative if too slow: Use [Nat64, Nat64, Nat64, Nat64, Nat64, Nat64] with schoolbook multiplication where each limb multiply uses a single Nat intermediary.**

## Representation
```
type Fp = {
  l0: Nat64; l1: Nat64; l2: Nat64;
  l3: Nat64; l4: Nat64; l5: Nat64;
};
```
Little-endian: value = l0 + l1*2^64 + l2*2^128 + ... + l5*2^320

Montgomery form: stores `a * R mod P` where R = 2^384.

## Precomputed Constants
- `P_LIMBS`: P as 6 Nat64 limbs
- `R_MOD_P`: 2^384 mod P (for converting 1 to Montgomery)
- `R2_MOD_P`: (2^384)^2 mod P = 2^768 mod P (for to_mont)
- `N_PRIME`: -P^{-1} mod 2^64 (for REDC)
- `ZERO`: all zeros (Montgomery 0)
- `ONE_MONT`: R mod P (Montgomery representation of 1)

## Implementation Tasks

### Task 1: Create `src/fp.mo` — Montgomery Fp module
Create the core Montgomery field module with:
- Type `Fp` (6 × Nat64 record)
- All precomputed constants (P_LIMBS, R_MOD_P, R2_MOD_P, N_PRIME)
- `fp_to_mont(n: Int): Fp` — convert regular Int to Montgomery
- `fp_from_mont(a: Fp): Int` — convert Montgomery back to Int
- `fp_add(a, b): Fp` — modular add (add limbs, subtract P if >= P)
- `fp_sub(a, b): Fp` — modular subtract (sub limbs, add P if borrow)
- `fp_mul(a, b): Fp` — Montgomery multiplication via REDC
- `fp_sq(a): Fp` — dedicated squaring (save ~30% partial products)
- `fp_neg(a): Fp` — P - a (unless zero)
- `fp_inv(a): Fp` — via Fermat's little theorem: a^{P-2}
- `fp_pow(a, exp): Fp` — square-and-multiply
- `fp_eq(a, b): Bool`
- `fp_is_zero(a): Bool`
- Helper: `mul_wide(a: Nat64, b: Nat64): (Nat64, Nat64)` — 64×64→128 split
- Helper: `mont_reduce(t: [var Nat64])` — REDC on 12-limb product

**Compile check**: `dfx build --check bls_test`

### Task 2: Wire Fp into Fp2
Update `src/lib.mo`:
- Import Fp module
- Change `Fp2 = (Fp.Fp, Fp.Fp)` (was `(Int, Int)`)
- All fp2_* functions call Fp.fp_* instead of fp_*
- Conversion functions at I/O boundary: `fp_to_mont`/`fp_from_mont`

### Task 3: Wire Fp2 into Fp6, Fp12 tower
- Fp6 = (Fp2, Fp2, Fp2) — no type change needed if Fp2 changed
- Fp12 = (Fp6, Fp6) — same
- Update fp6_nr (multiply by non-residue) to use new Fp2 ops
- Update fp12_cyclotomic_sq, fp12_cyclotomic_exp_bls_x

### Task 4: Wire into G1, G2 point operations
- G1Point uses Fp for x, y, z
- G2Point uses Fp2 for x, y, z
- Update g1_add, g1_double, g1_mul, g1_neg, g1_to_affine, etc.
- Update g2_add, g2_double, g2_mul, g2_neg, g2_to_affine, etc.

### Task 5: Wire into Miller loop, final exponentiation, pairing
- Update doubling_step, addition_step, apply_line
- Update miller_loop, final_exponentiation, final_exp_easy, final_exp_hard
- Update Frobenius maps (fp6_frob, fp12_frob) — convert precomputed constants

### Task 6: Wire into encode/decode I/O
- decode_fp → returns Fp (in Montgomery form)
- encode_fp → accepts Fp, converts from Montgomery, outputs bytes
- Update decode_g1, decode_g2, encode_g1, encode_g2
- Update hash-to-curve (swu_fp, iso11_map, etc.)

### Task 7: Update constants
- All hardcoded Int constants (G1_GEN, G2_GEN, PSI_X, PSI_Y, etc.) need Montgomery conversion
- Can either precompute and hardcode Montgomery limbs, or convert at module load time
- Isogeny coefficients (ISO11_*, ISO3_*) — large arrays, precompute offline

### Task 8: Update test canister
- `test/canister/main.mo` — update helper functions
- bytesToFp should produce Montgomery values
- fpToBytes should convert from Montgomery

### Task 9: Update bench
- `bench/bls12_381.bench.mo` — update test data to use new types
- Run `mops bench --replica pocket-ic --gc incremental`
- Compare with baseline

### Task 10: Full test + fix cycle
- Build: `dfx build --check bls_test`
- Run pic tests: check test/pic/ directory
- Fix any issues, iterate

## Key Mathematical Constants (to precompute)

P in 64-bit limbs (little-endian):
```
P = 0x1a0111ea397fe69a_4b1ba7b6434bacd7_64774b84f38512bf_6730d2a0f6b0f624_1eabfffeb153ffff_b9feffffffffaaab
l0 = 0xb9feffffffffaaab
l1 = 0x1eabfffeb153ffff
l2 = 0x6730d2a0f6b0f624
l3 = 0x64774b84f38512bf
l4 = 0x4b1ba7b6434bacd7
l5 = 0x1a0111ea397fe69a
```

R = 2^384:
```
R mod P = 0x15f65ec3fa80e493_5c071a97a256ec6d_77ce585370525745_5f489857db34b9f2_b8d1a0a22199ab3c_764774b84f38512c  (need exact computation)
```

R^2 mod P, N' = -P^{-1} mod 2^64: need exact computation (do offline in Python).

## Risk Mitigation
1. **Correctness**: Side-by-side testing — keep old Int functions as `_fp_mul_ref` temporarily
2. **Performance**: If Nat intermediary for wide multiply is too slow, fall back to 32-bit limbs
3. **Instruction count**: Profile individual operations first before full pairing
4. **Compilation**: Check frequently with `dfx build --check bls_test`

## Success Criteria
- All existing tests pass (pic tests, bench compiles)
- `fp_mul` benchmark: <20K instructions (from 68K)
- `pairing` benchmark: <5B instructions (from 15B)
- BLS multi_inf EVM test passes within 40B instruction limit
