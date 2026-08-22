/**
 * BLS12-381 fuzz test suite — 2 000 random inputs per operation
 *
 * Compares our Motoko BLS12-381 implementation against @noble/curves.
 * All BLS inputs are fixed-size (Fp=48 B, G1=128 B, G2=256 B, scalar=32 B).
 *
 * Cheap field-level tests run 2 000 random inputs.
 * Expensive curve/pairing tests use proportionally fewer to keep total time
 * under ~1 hour while still providing strong statistical coverage.
 */

import { PocketIc, PocketIcServer, type Actor } from '@dfinity/pic';
import { IDL } from '@dfinity/candid';
import { Principal } from '@dfinity/principal';
import { resolve } from 'path';
import { existsSync } from 'fs';
import { randomBytes } from 'crypto';
import { bls12_381 as bls } from '@noble/curves/bls12-381';

import { type _SERVICE } from './declarations/bls_test.did.d';
import { idlFactory } from './declarations/bls_test.did.js';

// ────────────────────────────────────────────
// Counts  (tuned so the full suite finishes in ~1 h)
// ────────────────────────────────────────────
const N_FP       = 2000;   // fp_mul, fp_inv, fp2_mul  (~15-20 ms each)
const N_G1_MUL   = 200;    // g1_mul                   (~0.5 s each)
const N_G2_MUL   = 100;    // g2_mul                   (~2 s each)
const N_G1_ADD   = 200;    // g1_add consistency        (~1.5 s each — 3 muls)
const N_MAP_G1   = 200;    // map_fp_to_g1              (~2 s each)
const N_MAP_G2   = 100;    // map_fp2_to_g2             (~8 s each)
const N_PAIRING  = 20;     // pairing bilinearity/check (~30 s each)
const N_MSM      = 20;     // g1_msm (3-point)          (~10 s each)

const WASM_PATH = resolve(
  __dirname, '..', '..', '.dfx', 'local', 'canisters', 'bls_test', 'bls_test.wasm.gz',
);

// ────────────────────────────────────────────
// Field constants
// ────────────────────────────────────────────
const P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;
const R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;

// ────────────────────────────────────────────
// Helpers
// ────────────────────────────────────────────
function bigintToBytes(n: bigint, len: number): Uint8Array {
  const hex = n.toString(16).padStart(len * 2, '0');
  const bytes = new Uint8Array(len);
  for (let i = 0; i < len; i++) bytes[i] = parseInt(hex.substring(i * 2, i * 2 + 2), 16);
  return bytes;
}
function bytesToBigint(bytes: Uint8Array | number[]): bigint {
  let r = 0n;
  for (const b of bytes) r = (r << 8n) | BigInt(b);
  return r;
}
function fpToBytes(n: bigint): number[] { return Array.from(bigintToBytes(((n % P) + P) % P, 48)); }
function fpFromBytes(b: Uint8Array | number[]): bigint { return bytesToBigint(b); }
function fpToEip2537(n: bigint): number[] {
  const r = new Array(64).fill(0);
  const d = fpToBytes(n);
  for (let i = 0; i < 48; i++) r[16 + i] = d[i];
  return r;
}
function fp2ToEip2537(c0: bigint, c1: bigint): number[] { return [...fpToEip2537(c0), ...fpToEip2537(c1)]; }
function g1ToEip2537(x: bigint, y: bigint): number[] { return [...fpToEip2537(x), ...fpToEip2537(y)]; }
function g1FromEip2537(b: Uint8Array | number[]): [bigint, bigint] {
  const a = Array.from(b);
  return [bytesToBigint(a.slice(16, 64)), bytesToBigint(a.slice(80, 128))];
}
function g2FromEip2537(b: Uint8Array | number[]): [[bigint, bigint], [bigint, bigint]] {
  const a = Array.from(b);
  return [[bytesToBigint(a.slice(16, 64)), bytesToBigint(a.slice(80, 128))],
          [bytesToBigint(a.slice(144, 192)), bytesToBigint(a.slice(208, 256))]];
}
function randomFp(): bigint { return ((bytesToBigint(randomBytes(48)) % P) + P) % P; }
function randomScalar(): bigint { return (bytesToBigint(randomBytes(32)) % (R - 1n)) + 1n; }

// Noble helpers
const Fp  = bls.fields.Fp;
const Fp2 = bls.fields.Fp2;

// Generators
const G1_X = 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn;
const G1_Y = 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1n;
const G2_X0 = 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8n;
const G2_X1 = 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7en;
const G2_Y0 = 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801n;
const G2_Y1 = 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79ben;
const G1_GEN = g1ToEip2537(G1_X, G1_Y);
const G2_GEN = [...fpToEip2537(G2_X0), ...fpToEip2537(G2_X1), ...fpToEip2537(G2_Y0), ...fpToEip2537(G2_Y1)];

// ────────────────────────────────────────────
// Suite
// ────────────────────────────────────────────

if (!existsSync(WASM_PATH)) {
  throw new Error(`WASM not found at ${WASM_PATH}. Run "dfx build bls_test --check" first.`);
}

describe('BLS12-381 Fuzz Tests', () => {
  let picServer: PocketIcServer;
  let pic: PocketIc;
  let actor: Actor<_SERVICE>;

  beforeAll(async () => {
    picServer = await PocketIcServer.start();
    pic = await PocketIc.create(picServer.getUrl(), { processingTimeoutMs: 600_000 });
    const canisterId = await pic.createCanister();
    await pic.installCode({ canisterId, wasm: WASM_PATH, arg: new Uint8Array(IDL.encode([], [])) });
    actor = pic.createActor<_SERVICE>(idlFactory, canisterId);
    await pic.addCycles(canisterId, 100_000_000_000_000n);
  }, 120_000);

  afterAll(async () => {
    if (pic) await pic.tearDown();
    if (picServer) await picServer.stop();
  });

  // ──────────── Fp mul ────────────
  it(`fp_mul: ${N_FP} random pairs`, async () => {
    let passed = 0;
    for (let i = 0; i < N_FP; i++) {
      const a = randomFp(), b = randomFp();
      const result = await actor.fp_mul(fpToBytes(a), fpToBytes(b));
      const actual = fpFromBytes(result);
      const expected = Fp.create(a * b);
      if (actual !== expected) throw new Error(`fp_mul mismatch at i=${i} a=${a} b=${b}: got ${actual} expected ${expected}`);
      passed++;
    }
    console.log(`  fp_mul: ${passed}/${N_FP} passed`);
  }, 600_000);

  // ──────────── Fp inv ────────────
  it(`fp_inv: ${N_FP} random values`, async () => {
    let passed = 0;
    for (let i = 0; i < N_FP; i++) {
      let a = randomFp();
      if (a === 0n) a = 1n;
      const result = await actor.fp_inv(fpToBytes(a));
      const actual = fpFromBytes(result);
      const expected = Fp.inv(Fp.create(a));
      if (actual !== expected) throw new Error(`fp_inv mismatch at i=${i} a=${a}: got ${actual} expected ${expected}`);
      passed++;
    }
    console.log(`  fp_inv: ${passed}/${N_FP} passed`);
  }, 600_000);

  // ──────────── Fp2 mul ────────────
  it(`fp2_mul: ${N_FP} random pairs`, async () => {
    let passed = 0;
    for (let i = 0; i < N_FP; i++) {
      const a0 = randomFp(), a1 = randomFp(), b0 = randomFp(), b1 = randomFp();
      const result = await actor.fp2_mul([...fpToBytes(a0), ...fpToBytes(a1)], [...fpToBytes(b0), ...fpToBytes(b1)]);
      const arr = Array.from(result);
      const rc0 = fpFromBytes(arr.slice(0, 48));
      const rc1 = fpFromBytes(arr.slice(48, 96));
      const ec0 = Fp.create(a0 * b0 - a1 * b1);
      const ec1 = Fp.create(a0 * b1 + a1 * b0);
      if (rc0 !== ec0 || rc1 !== ec1) throw new Error(`fp2_mul mismatch at i=${i}`);
      passed++;
    }
    console.log(`  fp2_mul: ${passed}/${N_FP} passed`);
  }, 600_000);

  // ──────────── G1 mul ────────────
  it(`g1_mul: ${N_G1_MUL} random scalars`, async () => {
    let passed = 0;
    const G_noble = bls.G1.ProjectivePoint.fromAffine({ x: G1_X, y: G1_Y });
    for (let i = 0; i < N_G1_MUL; i++) {
      const s = randomScalar();
      const result = await actor.g1_mul(G1_GEN, Array.from(bigintToBytes(s, 32)));
      const [rx, ry] = g1FromEip2537(result);
      const exp = G_noble.multiply(s).toAffine();
      if (rx !== exp.x || ry !== exp.y) throw new Error(`g1_mul mismatch at i=${i} s=${s}`);
      passed++;
      if (passed % 50 === 0) console.log(`    g1_mul: ${passed}/${N_G1_MUL}...`);
    }
    console.log(`  g1_mul: ${passed}/${N_G1_MUL} passed`);
  }, 3_600_000);

  // ──────────── G2 mul ────────────
  it(`g2_mul: ${N_G2_MUL} random scalars`, async () => {
    let passed = 0;
    const G_noble = bls.G2.ProjectivePoint.fromAffine({
      x: Fp2.create({ c0: G2_X0, c1: G2_X1 }),
      y: Fp2.create({ c0: G2_Y0, c1: G2_Y1 }),
    });
    for (let i = 0; i < N_G2_MUL; i++) {
      const s = randomScalar();
      const result = await actor.g2_mul(G2_GEN, Array.from(bigintToBytes(s, 32)));
      const [[rx0, rx1], [ry0, ry1]] = g2FromEip2537(result);
      const exp = G_noble.multiply(s).toAffine();
      if (rx0 !== exp.x.c0 || rx1 !== exp.x.c1 || ry0 !== exp.y.c0 || ry1 !== exp.y.c1)
        throw new Error(`g2_mul mismatch at i=${i} s=${s}`);
      passed++;
      if (passed % 25 === 0) console.log(`    g2_mul: ${passed}/${N_G2_MUL}...`);
    }
    console.log(`  g2_mul: ${passed}/${N_G2_MUL} passed`);
  }, 3_600_000);

  // ──────────── G1 add ────────────
  it(`g1_add: ${N_G1_ADD} random pairs: s1*G + s2*G == (s1+s2)*G`, async () => {
    let passed = 0;
    for (let i = 0; i < N_G1_ADD; i++) {
      const s1 = randomScalar(), s2 = randomScalar();
      const p1 = await actor.g1_mul(G1_GEN, Array.from(bigintToBytes(s1, 32)));
      const p2 = await actor.g1_mul(G1_GEN, Array.from(bigintToBytes(s2, 32)));
      const sum = await actor.g1_add(Array.from(p1), Array.from(p2));
      const [ax, ay] = g1FromEip2537(sum);
      const s_sum = (s1 + s2) % R;
      const direct = await actor.g1_mul(G1_GEN, Array.from(bigintToBytes(s_sum, 32)));
      const [ex, ey] = g1FromEip2537(direct);
      if (ax !== ex || ay !== ey) throw new Error(`g1_add mismatch at i=${i}`);
      passed++;
      if (passed % 50 === 0) console.log(`    g1_add: ${passed}/${N_G1_ADD}...`);
    }
    console.log(`  g1_add: ${passed}/${N_G1_ADD} passed`);
  }, 3_600_000);

  // ──────────── MAP_FP_TO_G1 ────────────
  it(`map_fp_to_g1: ${N_MAP_G1} random Fp values`, async () => {
    let passed = 0;
    for (let i = 0; i < N_MAP_G1; i++) {
      const u = randomFp();
      const result = await actor.map_fp_to_g1(fpToEip2537(u));
      const [rx, ry] = g1FromEip2537(result);
      const noble = bls.G1.mapToCurve([u]).toAffine();
      if (rx !== noble.x || ry !== noble.y)
        throw new Error(`map_fp_to_g1 mismatch at i=${i} u=${u}`);
      passed++;
      if (passed % 50 === 0) console.log(`    map_fp_to_g1: ${passed}/${N_MAP_G1}...`);
    }
    console.log(`  map_fp_to_g1: ${passed}/${N_MAP_G1} passed`);
  }, 3_600_000);

  // ──────────── MAP_FP2_TO_G2 ────────────
  it(`map_fp2_to_g2: ${N_MAP_G2} random Fp2 values`, async () => {
    let passed = 0;
    for (let i = 0; i < N_MAP_G2; i++) {
      const c0 = randomFp(), c1 = randomFp();
      const result = await actor.map_fp2_to_g2(fp2ToEip2537(c0, c1));
      const [[rx0, rx1], [ry0, ry1]] = g2FromEip2537(result);
      const noble = bls.G2.mapToCurve([c0, c1]).toAffine();
      if (rx0 !== noble.x.c0 || rx1 !== noble.x.c1 || ry0 !== noble.y.c0 || ry1 !== noble.y.c1)
        throw new Error(`map_fp2_to_g2 mismatch at i=${i}`);
      passed++;
      if (passed % 25 === 0) console.log(`    map_fp2_to_g2: ${passed}/${N_MAP_G2}...`);
    }
    console.log(`  map_fp2_to_g2: ${passed}/${N_MAP_G2} passed`);
  }, 7_200_000);

  // ──────────── Pairing bilinearity ────────────
  it(`pairing bilinearity: ${N_PAIRING} random scalars: e(a*G1,G2)==e(G1,a*G2)`, async () => {
    let passed = 0;
    for (let i = 0; i < N_PAIRING; i++) {
      const a = randomScalar();
      const aG1 = await actor.g1_mul(G1_GEN, Array.from(bigintToBytes(a, 32)));
      const aG2 = await actor.g2_mul(G2_GEN, Array.from(bigintToBytes(a, 32)));
      const lhs = await actor.pairing(Array.from(aG1), G2_GEN);
      const rhs = await actor.pairing(G1_GEN, Array.from(aG2));
      if (Array.from(lhs).toString() !== Array.from(rhs).toString())
        throw new Error(`pairing bilinearity mismatch at i=${i} a=${a}`);
      passed++;
      console.log(`    pairing bilinearity: ${passed}/${N_PAIRING}...`);
    }
    console.log(`  pairing bilinearity: ${passed}/${N_PAIRING} passed`);
  }, 7_200_000);

  // ──────────── Pairing check ────────────
  it(`pairing check: ${N_PAIRING} random: e(aP,Q)*e(-aP,Q)==1`, async () => {
    let passed = 0;
    for (let i = 0; i < N_PAIRING; i++) {
      const a = randomScalar();
      const aG1 = await actor.g1_mul(G1_GEN, Array.from(bigintToBytes(a, 32)));
      const neg_aG1 = await actor.g1_neg(Array.from(aG1));
      const input = [...Array.from(aG1), ...G2_GEN, ...Array.from(neg_aG1), ...G2_GEN];
      const check = await actor.pairing_check(input);
      if (!check) throw new Error(`pairing_check failed at i=${i} a=${a}`);
      passed++;
      console.log(`    pairing check: ${passed}/${N_PAIRING}...`);
    }
    console.log(`  pairing check: ${passed}/${N_PAIRING} passed`);
  }, 7_200_000);

  // ──────────── G1 MSM ────────────
  it(`g1_msm: ${N_MSM} random 3-point MSMs`, async () => {
    let passed = 0;
    const G_noble = bls.G1.ProjectivePoint.fromAffine({ x: G1_X, y: G1_Y });
    for (let trial = 0; trial < N_MSM; trial++) {
      const n = 3;
      const scalars: bigint[] = [];
      const baseScalars: bigint[] = [];
      const scalarBytes: number[] = [];
      for (let j = 0; j < n; j++) {
        baseScalars.push(randomScalar());
        scalars.push(randomScalar());
        scalarBytes.push(...Array.from(bigintToBytes(scalars[j], 32)));
      }
      const pointBytes: number[] = [];
      let noble_sum = bls.G1.ProjectivePoint.ZERO;
      for (let j = 0; j < n; j++) {
        const pj = await actor.g1_mul(G1_GEN, Array.from(bigintToBytes(baseScalars[j], 32)));
        pointBytes.push(...Array.from(pj));
        noble_sum = noble_sum.add(G_noble.multiply(baseScalars[j]).multiply(scalars[j]));
      }
      const msm_result = await actor.g1_msm(pointBytes, scalarBytes);
      const [rx, ry] = g1FromEip2537(msm_result);
      const exp = noble_sum.toAffine();
      if (rx !== exp.x || ry !== exp.y) throw new Error(`g1_msm mismatch at trial=${trial}`);
      passed++;
      console.log(`    g1_msm: ${passed}/${N_MSM}...`);
    }
    console.log(`  g1_msm: ${passed}/${N_MSM} passed`);
  }, 3_600_000);
});
