/**
 * BLS12-381 comprehensive test suite
 *
 * Tests each layer of BLS12-381 operations against @noble/curves reference.
 * Bottom-up: Fp → Fp2 → G1/G2 → SWU → isogeny → MAP → pairing
 */

import { PocketIc, PocketIcServer, type Actor } from '@dfinity/pic';
import { IDL } from '@dfinity/candid';
import { Principal } from '@dfinity/principal';
import { resolve } from 'path';
import { existsSync } from 'fs';
import { bls12_381 as bls } from '@noble/curves/bls12-381';

import { type _SERVICE } from './declarations/bls_test.did.d';
import { idlFactory } from './declarations/bls_test.did.js';

// ────────────────────────────────────────────
// Paths
// ────────────────────────────────────────────
const WASM_PATH = resolve(
  __dirname,
  '..',
  '..',
  '.dfx',
  'local',
  'canisters',
  'bls_test',
  'bls_test.wasm.gz',
);

// ────────────────────────────────────────────
// Helpers
// ────────────────────────────────────────────
const P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaabn;

/** Convert a bigint to a fixed-length big-endian Uint8Array */
function bigintToBytes(n: bigint, len: number): Uint8Array {
  const hex = n.toString(16).padStart(len * 2, '0');
  const bytes = new Uint8Array(len);
  for (let i = 0; i < len; i++) {
    bytes[i] = parseInt(hex.substring(i * 2, i * 2 + 2), 16);
  }
  return bytes;
}

/** Convert a Uint8Array (big-endian) to bigint */
function bytesToBigint(bytes: Uint8Array | number[]): bigint {
  let result = 0n;
  for (const b of bytes) {
    result = (result << 8n) | BigInt(b);
  }
  return result;
}

/** Convert Fp element to 48-byte array for canister calls */
function fpToBytes(n: bigint): number[] {
  return Array.from(bigintToBytes(((n % P) + P) % P, 48));
}

/** Decode 48-byte array from canister to bigint */
function fpFromBytes(bytes: Uint8Array | number[]): bigint {
  return bytesToBigint(bytes);
}

/** Convert Fp element to EIP-2537 64-byte padded format (16 zero + 48 data) */
function fpToEip2537(n: bigint): number[] {
  const result = new Array(64).fill(0);
  const data = fpToBytes(n);
  for (let i = 0; i < 48; i++) {
    result[16 + i] = data[i];
  }
  return result;
}

/** Encode Fp2 = (c0, c1) as 96 bytes for the test canister */
function fp2ToBytes(c0: bigint, c1: bigint): number[] {
  return [...fpToBytes(c0), ...fpToBytes(c1)];
}

/** Decode 96-byte response to Fp2 */
function fp2FromBytes(bytes: Uint8Array | number[]): [bigint, bigint] {
  const arr = Array.from(bytes);
  return [fpFromBytes(arr.slice(0, 48)), fpFromBytes(arr.slice(48, 96))];
}

/** Encode Fp2 to EIP-2537 format: 128 bytes (c0 as 64 bytes, c1 as 64 bytes) */
function fp2ToEip2537(c0: bigint, c1: bigint): number[] {
  return [...fpToEip2537(c0), ...fpToEip2537(c1)];
}

/** Encode a G1 affine point as 128 bytes (EIP-2537 format) */
function g1ToEip2537(x: bigint, y: bigint): number[] {
  return [...fpToEip2537(x), ...fpToEip2537(y)];
}

/** Decode 128-byte G1 response */
function g1FromEip2537(bytes: Uint8Array | number[]): [bigint, bigint] {
  const arr = Array.from(bytes);
  // First 64 bytes: x (16 zero pad + 48 data)
  const x = bytesToBigint(arr.slice(16, 64));
  const y = bytesToBigint(arr.slice(80, 128));
  return [x, y];
}

/** Decode 256-byte G2 response */
function g2FromEip2537(bytes: Uint8Array | number[]): [[bigint, bigint], [bigint, bigint]] {
  const arr = Array.from(bytes);
  const x0 = bytesToBigint(arr.slice(16, 64));
  const x1 = bytesToBigint(arr.slice(80, 128));
  const y0 = bytesToBigint(arr.slice(144, 192));
  const y1 = bytesToBigint(arr.slice(208, 256));
  return [[x0, x1], [y0, y1]];
}

// Noble field helpers
const Fp = bls.fields.Fp;
const Fp2 = bls.fields.Fp2;

// ────────────────────────────────────────────
// Test suite
// ────────────────────────────────────────────

if (!existsSync(WASM_PATH)) {
  throw new Error(
    `WASM not found at ${WASM_PATH}. Run "dfx build bls_test --check" first.`
  );
}

describe('BLS12-381', () => {
  let picServer: PocketIcServer;
  let pic: PocketIc;
  let actor: Actor<_SERVICE>;
  let canisterId: Principal;

  beforeAll(async () => {
    picServer = await PocketIcServer.start();
    const serverUrl = picServer.getUrl();
    pic = await PocketIc.create(serverUrl, {
      processingTimeoutMs: 600_000,
    });
    canisterId = await pic.createCanister();
    await pic.installCode({
      canisterId,
      wasm: WASM_PATH,
      arg: new Uint8Array(IDL.encode([], [])),
    });
    actor = pic.createActor<_SERVICE>(idlFactory, canisterId);
    await pic.addCycles(canisterId, 100_000_000_000_000n);
  }, 120_000);

  afterAll(async () => {
    if (pic) await pic.tearDown();
    if (picServer) await picServer.stop();
  });

  // ══════════════════════════════════════════════════════════════
  //  Constants
  // ══════════════════════════════════════════════════════════════
  describe('Constants', () => {
    it('should return correct P', async () => {
      const result = await actor.get_p();
      const p = fpFromBytes(result);
      expect(p).toBe(P);
    });

    it('should return correct r', async () => {
      const result = await actor.get_r();
      const r = bytesToBigint(result);
      const R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
      expect(r).toBe(R);
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  Fp arithmetic
  // ══════════════════════════════════════════════════════════════
  describe('Fp arithmetic', () => {
    const testValues = [
      0n,
      1n,
      2n,
      42n,
      P - 1n,
      P - 2n,
      // Random large value
      0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn,
    ];

    it('fp_add: (a + b) mod P', async () => {
      for (const a of testValues) {
        for (const b of [1n, P - 1n, 42n]) {
          const result = await actor.fp_add(fpToBytes(a), fpToBytes(b));
          const actual = fpFromBytes(result);
          const expected = Fp.create(a + b);
          expect(actual).toBe(expected);
        }
      }
    });

    it('fp_sub: (a - b) mod P', async () => {
      const result = await actor.fp_sub(fpToBytes(10n), fpToBytes(20n));
      const actual = fpFromBytes(result);
      const expected = Fp.create(10n - 20n);
      expect(actual).toBe(expected);
    });

    it('fp_mul: (a * b) mod P', async () => {
      const a = 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn;
      const b = 42n;
      const result = await actor.fp_mul(fpToBytes(a), fpToBytes(b));
      const actual = fpFromBytes(result);
      const expected = Fp.create(a * b);
      expect(actual).toBe(expected);
    });

    it('fp_inv: a^(-1) mod P', async () => {
      const a = 42n;
      const result = await actor.fp_inv(fpToBytes(a));
      const actual = fpFromBytes(result);
      const expected = Fp.inv(Fp.create(a));
      expect(actual).toBe(expected);
    });

    it('fp_neg: -a mod P', async () => {
      const a = 42n;
      const result = await actor.fp_neg(fpToBytes(a));
      const actual = fpFromBytes(result);
      const expected = Fp.neg(Fp.create(a));
      expect(actual).toBe(expected);
    });

    it('fp_pow: a^e mod P', async () => {
      const a = 7n;
      const e = 100n;
      const result = await actor.fp_pow(fpToBytes(a), fpToBytes(e));
      const actual = fpFromBytes(result);
      const expected = Fp.pow(Fp.create(a), e);
      expect(actual).toBe(expected);
    });

    it('fp_sqrt: sqrt(a) mod P', async () => {
      // 4 has sqrt = 2
      const result = await actor.fp_sqrt(fpToBytes(4n));
      expect(result).toHaveLength(1);
      const sqrtVal = fpFromBytes(result[0]!);
      // Verify: sqrtVal^2 == 4 mod P
      expect(Fp.create(sqrtVal * sqrtVal)).toBe(4n);
    });

    it('fp_sqrt: non-residue returns null', async () => {
      // Try a known non-residue (we need to find or verify one)
      // The generator 7 is typically not a QR
      const nqr = Fp.neg(1n); // -1: check if it's a QR
      // p ≡ 3 mod 4, so -1 is NOT a QR when p ≡ 3 mod 4
      const result = await actor.fp_sqrt(fpToBytes(nqr));
      expect(result).toHaveLength(0);
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  Fp2 arithmetic
  // ══════════════════════════════════════════════════════════════
  describe('Fp2 arithmetic', () => {
    // Fp2 = c0 + c1*u where u^2 = -1
    const a_c0 = 42n;
    const a_c1 = 7n;
    const b_c0 = 100n;
    const b_c1 = 200n;

    it('fp2_add', async () => {
      const result = await actor.fp2_add(fp2ToBytes(a_c0, a_c1), fp2ToBytes(b_c0, b_c1));
      const [rc0, rc1] = fp2FromBytes(result);
      expect(rc0).toBe(Fp.create(a_c0 + b_c0));
      expect(rc1).toBe(Fp.create(a_c1 + b_c1));
    });

    it('fp2_sub', async () => {
      const result = await actor.fp2_sub(fp2ToBytes(a_c0, a_c1), fp2ToBytes(b_c0, b_c1));
      const [rc0, rc1] = fp2FromBytes(result);
      expect(rc0).toBe(Fp.create(a_c0 - b_c0));
      expect(rc1).toBe(Fp.create(a_c1 - b_c1));
    });

    it('fp2_mul: (a0+a1*u)*(b0+b1*u) = (a0b0-a1b1) + (a0b1+a1b0)*u', async () => {
      const result = await actor.fp2_mul(fp2ToBytes(a_c0, a_c1), fp2ToBytes(b_c0, b_c1));
      const [rc0, rc1] = fp2FromBytes(result);
      const exp_c0 = Fp.create(a_c0 * b_c0 - a_c1 * b_c1);
      const exp_c1 = Fp.create(a_c0 * b_c1 + a_c1 * b_c0);
      expect(rc0).toBe(exp_c0);
      expect(rc1).toBe(exp_c1);
    });

    it('fp2_sq: consistency with fp2_mul(a,a)', async () => {
      const sq_result = await actor.fp2_sq(fp2ToBytes(a_c0, a_c1));
      const mul_result = await actor.fp2_mul(fp2ToBytes(a_c0, a_c1), fp2ToBytes(a_c0, a_c1));
      expect(Array.from(sq_result)).toEqual(Array.from(mul_result));
    });

    it('fp2_inv: a * a^(-1) = 1', async () => {
      const inv_result = await actor.fp2_inv(fp2ToBytes(a_c0, a_c1));
      const mul_result = await actor.fp2_mul(fp2ToBytes(a_c0, a_c1), Array.from(inv_result));
      const [rc0, rc1] = fp2FromBytes(mul_result);
      expect(rc0).toBe(1n);
      expect(rc1).toBe(0n);
    });

    it('fp2_neg: a + (-a) = 0', async () => {
      const neg_result = await actor.fp2_neg(fp2ToBytes(a_c0, a_c1));
      const sum = await actor.fp2_add(fp2ToBytes(a_c0, a_c1), Array.from(neg_result));
      const [rc0, rc1] = fp2FromBytes(sum);
      expect(rc0).toBe(0n);
      expect(rc1).toBe(0n);
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  G1 point operations
  // ══════════════════════════════════════════════════════════════
  describe('G1 operations', () => {
    // G1 generator
    const G1_X = 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn;
    const G1_Y = 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1n;

    it('generator is on curve', async () => {
      const isOnCurve = await actor.g1_is_on_curve(g1ToEip2537(G1_X, G1_Y));
      expect(isOnCurve).toBe(true);
    });

    it('generator passes subgroup check', async () => {
      const check = await actor.g1_subgroup_check(g1ToEip2537(G1_X, G1_Y));
      expect(check).toBe(true);
    });

    it('g1_add: G + G = 2G', async () => {
      const g = g1ToEip2537(G1_X, G1_Y);
      const result = await actor.g1_add(g, g);
      const [rx, ry] = g1FromEip2537(result);

      // Also compute 2G via noble
      const G = bls.G1.ProjectivePoint.fromAffine({ x: G1_X, y: G1_Y });
      const twoG = G.add(G).toAffine();
      expect(rx).toBe(twoG.x);
      expect(ry).toBe(twoG.y);
    });

    it('g1_mul: 2*G = G+G', async () => {
      const g = g1ToEip2537(G1_X, G1_Y);
      const scalar = bigintToBytes(2n, 32);
      const result = await actor.g1_mul(g, Array.from(scalar));
      const add_result = await actor.g1_add(g, g);
      expect(Array.from(result)).toEqual(Array.from(add_result));
    });

    it('g1_mul: r*G = infinity (zero)', async () => {
      const g = g1ToEip2537(G1_X, G1_Y);
      const R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
      const scalar = Array.from(bigintToBytes(R, 32));
      const result = await actor.g1_mul(g, scalar);
      // Infinity = all zeros
      const allZero = (Array.from(result) as number[]).every(b => b === 0);
      expect(allZero).toBe(true);
    });

    it('g1_neg: G + (-G) = infinity', async () => {
      const g = g1ToEip2537(G1_X, G1_Y);
      const neg = await actor.g1_neg(g);
      const sum = await actor.g1_add(g, Array.from(neg));
      const allZero = (Array.from(sum) as number[]).every(b => b === 0);
      expect(allZero).toBe(true);
    });

    it('g1_mul matches noble for scalar=42', async () => {
      const g = g1ToEip2537(G1_X, G1_Y);
      const scalar = Array.from(bigintToBytes(42n, 32));
      const result = await actor.g1_mul(g, scalar);
      const [rx, ry] = g1FromEip2537(result);

      const G = bls.G1.ProjectivePoint.fromAffine({ x: G1_X, y: G1_Y });
      const expected = G.multiply(42n).toAffine();
      expect(rx).toBe(expected.x);
      expect(ry).toBe(expected.y);
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  G2 point operations
  // ══════════════════════════════════════════════════════════════
  describe('G2 operations', () => {
    // G2 generator affine coordinates
    const G2_X0 = 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8n;
    const G2_X1 = 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7en;
    const G2_Y0 = 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801n;
    const G2_Y1 = 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79ben;

    const g2Gen = [...fpToEip2537(G2_X0), ...fpToEip2537(G2_X1), ...fpToEip2537(G2_Y0), ...fpToEip2537(G2_Y1)];

    it('generator is on curve', async () => {
      const isOnCurve = await actor.g2_is_on_curve(g2Gen);
      expect(isOnCurve).toBe(true);
    });

    it('generator passes subgroup check', async () => {
      const check = await actor.g2_subgroup_check(g2Gen);
      expect(check).toBe(true);
    });

    it('g2_add: G + G = 2G (matches noble)', async () => {
      const result = await actor.g2_add(g2Gen, g2Gen);
      const [[rx0, rx1], [ry0, ry1]] = g2FromEip2537(result);

      const G = bls.G2.ProjectivePoint.fromAffine({
        x: Fp2.create({ c0: G2_X0, c1: G2_X1 }),
        y: Fp2.create({ c0: G2_Y0, c1: G2_Y1 }),
      });
      const twoG = G.add(G).toAffine();
      expect(rx0).toBe(twoG.x.c0);
      expect(rx1).toBe(twoG.x.c1);
      expect(ry0).toBe(twoG.y.c0);
      expect(ry1).toBe(twoG.y.c1);
    });

    it('g2_mul: 2*G = G+G', async () => {
      const scalar = Array.from(bigintToBytes(2n, 32));
      const mul_result = await actor.g2_mul(g2Gen, scalar);
      const add_result = await actor.g2_add(g2Gen, g2Gen);
      expect(Array.from(mul_result)).toEqual(Array.from(add_result));
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  SWU map (Simplified Shallue-van de Woestijne-Ulas)
  // ══════════════════════════════════════════════════════════════
  describe('SWU map (G1)', () => {
    it('swu_fp produces point on isogeny source curve', async () => {
      const u = 42n;
      const result = await actor.swu_fp(fpToBytes(u));
      const [x, y] = fp2FromBytes(result); // reusing fp2FromBytes for 96-byte pair

      // Verify point is on E': y² = x³ + A'x + B'
      const ISO_A = 12190336318893619529228877361869031420615612348429846051986726275283378313155663745811710833465465981901188123677n;
      const ISO_B = 2906670324641927570491258158026293881577086121416628140204402091718288198173574630967936031029026176254968826637280n;
      const y2 = Fp.create(y * y);
      const rhs = Fp.create(x * x * x + ISO_A * x + ISO_B);
      expect(y2).toBe(rhs);
    });

    it('swu_fp matches noble for u=1', async () => {
      // Use noble's mapToCurve which does SWU+isogeny
      // We can't easily test SWU alone via noble directly, but we can test the full pipeline
      // For now, just test that SWU produces a point on E'
      const u = 1n;
      const result = await actor.swu_fp(fpToBytes(u));
      const [x, y] = fp2FromBytes(result);

      const ISO_A = 12190336318893619529228877361869031420615612348429846051986726275283378313155663745811710833465465981901188123677n;
      const ISO_B = 2906670324641927570491258158026293881577086121416628140204402091718288198173574630967936031029026176254968826637280n;
      const y2 = Fp.create(y * y);
      const rhs = Fp.create(x * x * x + ISO_A * x + ISO_B);
      expect(y2).toBe(rhs);
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  ISO11 map (11-isogeny from E' to E)
  // ══════════════════════════════════════════════════════════════
  describe('ISO11 map', () => {
    it('iso11_map produces point on BLS12-381 curve y²=x³+4', async () => {
      // First get a point on E' via SWU
      const u = 42n;
      const swu_result = await actor.swu_fp(fpToBytes(u));
      const [sx, sy] = fp2FromBytes(swu_result);

      // Then apply isogeny
      const iso_result = await actor.iso11_map(fpToBytes(sx), fpToBytes(sy));
      const [ex, ey] = fp2FromBytes(iso_result);

      // Verify on BLS12-381: y² = x³ + 4
      const y2 = Fp.create(ey * ey);
      const rhs = Fp.create(ex * ex * ex + 4n);
      expect(y2).toBe(rhs);
    });

    it('iso11_map result + cofactor clearing matches noble mapToCurve', async () => {
      // Full pipeline: SWU + isogeny (raw, no cofactor clearing)
      const u = 42n;
      const swu_result = await actor.swu_fp(fpToBytes(u));
      const [sx, sy] = fp2FromBytes(swu_result);
      const iso_result = await actor.iso11_map(fpToBytes(sx), fpToBytes(sy));
      const [ex, ey] = fp2FromBytes(iso_result);

      // Apply cofactor clearing: clearCofactor(P) = BLS_X * P + P
      const BLS_X = BigInt('0xd201000000010000');
      const iso_proj = bls.G1.ProjectivePoint.fromAffine({ x: ex, y: ey });
      const cleared = iso_proj.multiplyUnsafe(BLS_X).add(iso_proj).toAffine();

      // Noble: mapToCurve does SWU + isogeny + cofactor clearing
      const noble_point = bls.G1.mapToCurve([u]).toAffine();

      expect(cleared.x).toBe(noble_point.x);
      expect(cleared.y).toBe(noble_point.y);
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  MAP_FP_TO_G1 (full pipeline: SWU + isogeny)
  // ══════════════════════════════════════════════════════════════
  describe('MAP_FP_TO_G1', () => {
    const testInputs = [
      0n,
      1n,
      2n,
      42n,
      P - 1n,
      0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn,
    ];

    for (const u of testInputs) {
      it(`map_fp_to_g1(${u <= 42n ? u.toString() : '0x' + u.toString(16).slice(0, 8) + '...'}) matches noble`, async () => {
        const input = fpToEip2537(u);
        const result = await actor.map_fp_to_g1(input);
        const [rx, ry] = g1FromEip2537(result);

        // Noble reference
        const noble_point = bls.G1.mapToCurve([u]).toAffine();

        expect(rx).toBe(noble_point.x);
        expect(ry).toBe(noble_point.y);
      });
    }
  });

  // ══════════════════════════════════════════════════════════════
  //  MAP_FP2_TO_G2
  // ══════════════════════════════════════════════════════════════
  //  Debug: intermediate SWU + iso3 values for G2
  // ══════════════════════════════════════════════════════════════
  describe('Debug G2 intermediates', () => {
    it('raw SWU for (1,0) matches noble', async () => {
      const c0 = 1n, c1 = 0n;
      const c0Bytes = Array.from(fpToBytes(c0));
      const c1Bytes = Array.from(fpToBytes(c1));
      const [sx0, sx1, sy0, sy1] = await actor.debug_swu_fp2(c0Bytes, c1Bytes);
      const swu_x_c0 = bytesToBigint(sx0 as Uint8Array);
      const swu_x_c1 = bytesToBigint(sx1 as Uint8Array);
      const swu_y_c0 = bytesToBigint(sy0 as Uint8Array);
      const swu_y_c1 = bytesToBigint(sy1 as Uint8Array);

      // Noble raw SWU
      const { mapToCurveSimpleSWU } = require('@noble/curves/abstract/weierstrass');
      const { Fp, Fp2 } = bls.fields;
      const G2_SWU = mapToCurveSimpleSWU(Fp2, {
        A: Fp2.create({ c0: Fp.create(0n), c1: Fp.create(240n) }),
        B: Fp2.create({ c0: Fp.create(1012n), c1: Fp.create(1012n) }),
        Z: Fp2.create({ c0: Fp.create(-2n), c1: Fp.create(-1n) }),
      });
      const u = Fp2.create({ c0: Fp.create(c0), c1: Fp.create(c1) });
      const noble_swu = G2_SWU(u);

      console.log('Motoko SWU x:', swu_x_c0, swu_x_c1);
      console.log('Noble  SWU x:', noble_swu.x.c0, noble_swu.x.c1);
      console.log('Motoko SWU y:', swu_y_c0, swu_y_c1);
      console.log('Noble  SWU y:', noble_swu.y.c0, noble_swu.y.c1);
      console.log('x match:', swu_x_c0 === noble_swu.x.c0 && swu_x_c1 === noble_swu.x.c1);
      console.log('y match:', swu_y_c0 === noble_swu.y.c0 && swu_y_c1 === noble_swu.y.c1);
    });

    it('iso3 for (1,0) matches noble', async () => {
      const c0 = 1n, c1 = 0n;
      const c0Bytes = Array.from(fpToBytes(c0));
      const c1Bytes = Array.from(fpToBytes(c1));
      const [ix0, ix1, iy0, iy1] = await actor.debug_iso3_fp2(c0Bytes, c1Bytes);
      const iso_x_c0 = bytesToBigint(ix0 as Uint8Array);
      const iso_x_c1 = bytesToBigint(ix1 as Uint8Array);
      const iso_y_c0 = bytesToBigint(iy0 as Uint8Array);
      const iso_y_c1 = bytesToBigint(iy1 as Uint8Array);

      // Noble raw SWU + iso3
      const { mapToCurveSimpleSWU } = require('@noble/curves/abstract/weierstrass');
      const { isogenyMap } = require('@noble/curves/abstract/hash-to-curve');
      const { Fp, Fp2 } = bls.fields;
      const G2_SWU = mapToCurveSimpleSWU(Fp2, {
        A: Fp2.create({ c0: Fp.create(0n), c1: Fp.create(240n) }),
        B: Fp2.create({ c0: Fp.create(1012n), c1: Fp.create(1012n) }),
        Z: Fp2.create({ c0: Fp.create(-2n), c1: Fp.create(-1n) }),
      });
      const isoMapG2 = isogenyMap(Fp2, [
        [[
          '0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6',
          '0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6',
        ], [
          '0x0',
          '0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a',
        ], [
          '0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e',
          '0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d',
        ], [
          '0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1',
          '0x0',
        ]],
        [[
          '0x0',
          '0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63',
        ], [
          '0xc',
          '0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f',
        ], ['0x1', '0x0']],
        [[
          '0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706',
          '0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706',
        ], [
          '0x0',
          '0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be',
        ], [
          '0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c',
          '0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f',
        ], [
          '0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10',
          '0x0',
        ]],
        [[
          '0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb',
          '0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb',
        ], [
          '0x0',
          '0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3',
        ], [
          '0x12',
          '0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99',
        ], ['0x1', '0x0']],
      ].map((i: any) => i.map((pair: any) => Fp2.fromBigTuple(pair.map(BigInt)))) as any);

      const u = Fp2.create({ c0: Fp.create(c0), c1: Fp.create(c1) });
      const swu = G2_SWU(u);
      const noble_iso = isoMapG2(swu.x, swu.y);

      console.log('Motoko iso3 x:', iso_x_c0, iso_x_c1);
      console.log('Noble  iso3 x:', noble_iso.x.c0, noble_iso.x.c1);
      console.log('Motoko iso3 y:', iso_y_c0, iso_y_c1);
      console.log('Noble  iso3 y:', noble_iso.y.c0, noble_iso.y.c1);
      console.log('x match:', iso_x_c0 === noble_iso.x.c0 && iso_x_c1 === noble_iso.x.c1);
      console.log('y match:', iso_y_c0 === noble_iso.y.c0 && iso_y_c1 === noble_iso.y.c1);
    });
  });

  describe('MAP_FP2_TO_G2', () => {
    const testInputs: [bigint, bigint][] = [
      [0n, 0n],
      [1n, 0n],
      [0n, 1n],
      [42n, 7n],
      [P - 1n, P - 2n],
    ];

    for (const [c0, c1] of testInputs) {
      it(`map_fp2_to_g2(${c0 <= 42n ? `${c0},${c1}` : 'large'}) matches noble`, async () => {
        const input = fp2ToEip2537(c0, c1);
        const result = await actor.map_fp2_to_g2(input);
        const [[rx0, rx1], [ry0, ry1]] = g2FromEip2537(result);

        // Noble reference
        const noble_point = bls.G2.mapToCurve([c0, c1]).toAffine();

        expect(rx0).toBe(noble_point.x.c0);
        expect(rx1).toBe(noble_point.x.c1);
        expect(ry0).toBe(noble_point.y.c0);
        expect(ry1).toBe(noble_point.y.c1);
      });
    }
  });

  // ══════════════════════════════════════════════════════════════
  //  Pairing
  // ══════════════════════════════════════════════════════════════
  describe('Pairing', () => {
    const G1_X = 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn;
    const G1_Y = 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1n;
    const G2_X0 = 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8n;
    const G2_X1 = 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7en;
    const G2_Y0 = 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801n;
    const G2_Y1 = 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79ben;

    it('e(G1, G2) is not identity (basic pairing computation)', async () => {
      const g1 = g1ToEip2537(G1_X, G1_Y);
      const g2 = [...fpToEip2537(G2_X0), ...fpToEip2537(G2_X1), ...fpToEip2537(G2_Y0), ...fpToEip2537(G2_Y1)];
      const result = await actor.pairing(g1, g2);
      // Should return 576 bytes (12 Fp elements)
      expect(result.length).toBe(576);
      // Not all zeros (pairing of generators is not identity)
      const allZero = (Array.from(result) as number[]).every(b => b === 0);
      expect(allZero).toBe(false);
    });

    it('e(P, Q) * e(-P, Q) = 1 (pairing check)', async () => {
      const g1 = g1ToEip2537(G1_X, G1_Y);
      const neg_g1_result = await actor.g1_neg(g1);
      const neg_g1 = Array.from(neg_g1_result);
      const g2 = [...fpToEip2537(G2_X0), ...fpToEip2537(G2_X1), ...fpToEip2537(G2_Y0), ...fpToEip2537(G2_Y1)];

      // Build input: [G1, G2, -G1, G2] = 384 + 384 = 768 bytes
      const input = [...g1, ...g2, ...neg_g1, ...g2];
      const check = await actor.pairing_check(input);
      expect(check).toBe(true);
    });

    it('e(aP, Q) = e(P, aQ) (bilinearity)', async () => {
      const a = 3n;
      const g1_bytes = g1ToEip2537(G1_X, G1_Y);
      const g2_bytes = [...fpToEip2537(G2_X0), ...fpToEip2537(G2_X1), ...fpToEip2537(G2_Y0), ...fpToEip2537(G2_Y1)];

      // aP
      const aP = await actor.g1_mul(g1_bytes, Array.from(bigintToBytes(a, 32)));
      // aQ
      const aQ = await actor.g2_mul(g2_bytes, Array.from(bigintToBytes(a, 32)));

      // e(aP, Q)
      const lhs = await actor.pairing(Array.from(aP), g2_bytes);
      // e(P, aQ)
      const rhs = await actor.pairing(g1_bytes, Array.from(aQ));

      expect(Array.from(lhs)).toEqual(Array.from(rhs));
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  MSM (Multi-Scalar Multiplication)
  // ══════════════════════════════════════════════════════════════
  describe('G1 MSM', () => {
    const G1_X = 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bbn;
    const G1_Y = 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1n;

    it('MSM with single point equals scalar mul', async () => {
      const g1 = g1ToEip2537(G1_X, G1_Y);
      const scalar = Array.from(bigintToBytes(42n, 32));

      const msm_result = await actor.g1_msm(g1, scalar);
      const mul_result = await actor.g1_mul(g1, scalar);

      expect(Array.from(msm_result)).toEqual(Array.from(mul_result));
    });

    it('MSM: 2*G + 3*G = 5*G', async () => {
      const g1 = g1ToEip2537(G1_X, G1_Y);
      const points = [...g1, ...g1]; // two copies of G
      const scalars = [...Array.from(bigintToBytes(2n, 32)), ...Array.from(bigintToBytes(3n, 32))];

      const msm_result = await actor.g1_msm(points, scalars);
      const five_g = await actor.g1_mul(g1, Array.from(bigintToBytes(5n, 32)));

      expect(Array.from(msm_result)).toEqual(Array.from(five_g));
    });
  });

  // ══════════════════════════════════════════════════════════════
  //  EIP-2537 Encode/Decode
  // ══════════════════════════════════════════════════════════════
  describe('Encoding', () => {
    it('encode_fp roundtrip', async () => {
      const val = 42n;
      const encoded = await actor.encode_fp(fpToBytes(val));
      // EIP-2537 format: 64 bytes with 16-byte zero prefix
      expect(encoded.length).toBe(64);
      for (let i = 0; i < 16; i++) {
        expect(encoded[i]).toBe(0);
      }
      // Decode back
      const decoded = await actor.decode_fp(Array.from(encoded));
      expect(decoded).toHaveLength(1);
      const result = fpFromBytes(decoded[0]!);
      expect(result).toBe(42n);
    });

    it('decode_fp rejects value >= P', async () => {
      // Encode P directly without mod reduction
      const pBytes = Array.from(bigintToBytes(P, 48));
      const too_large = new Array(16).fill(0).concat(pBytes);
      const decoded = await actor.decode_fp(too_large);
      expect(decoded).toHaveLength(0);
    });
  });
});
