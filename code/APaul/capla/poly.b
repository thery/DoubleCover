/* poly.b -- the fixed-width integer layer and poly_eval of htr_plain.c,
 * in Capla.  This is the second piece of the port, after scan.b.
 *
 * A value is n limbs of 32 bits (n = 21 in the search), an integer modulo
 * 2^(32n) in two's complement, least significant limb first.  Capla has
 * no global variables, so the coefficient table CO is an array the caller
 * allocates and init_coeffs fills, rather than a static.
 *
 * The C being ported is htr_plain.c's big_* functions and poly_eval.
 */

macro! XDEN { 54u64 }             /* grid scale: x = X / 2^XDEN            */

/* ------------------------------------------------- fixed-width integers */

fun big_set(r: mut [u32; n], a: [u32; n], n: u64) {
  for i: u64 = 0 .. n {
    r[i] = a[i];
  }
}

fun big_zero(r: mut [u32; n], n: u64) {
  for i: u64 = 0 .. n {
    r[i] = 0u32;
  }
}

fun big_add(r: mut [u32; n], a: [u32; n], n: u64) {
  let carry: u64 = 0;
  for i: u64 = 0 .. n {
    let t: u64 = (u64) r[i] + (u64) a[i] + carry;
    r[i] = (u32) t;
    carry = t >> 32;
  }
}

fun big_mul32(r: mut [u32; n], m: u32, n: u64) {
  let carry: u64 = 0;
  for i: u64 = 0 .. n {
    let t: u64 = (u64) r[i] * (u64) m + carry;
    r[i] = (u32) t;
    carry = t >> 32;
  }
}

/* r <<= 32 (one limb) */
fun big_shl_limb(r: mut [u32; n], n: u64) {
  assert n >= 1;
  for decr i: u64 = (n - 1) .. 0 {
    r[i] = r[i - 1];
  }
  r[0] = 0u32;
}

/* r <<= k.  The C walks the limbs downwards from NL-1; a u64 counter
 * cannot run down to -1, so the two halves are written as upward loops
 * over j with i = n - 1 - j. */
fun big_shl(r: mut [u32; n], k: u64, n: u64) {
  let limbs: u64 = k / 32;
  let bits: u64 = k % 32;
  assert limbs <= n;

  for j: u64 = 0 .. (n - limbs) {
    let i: u64 = n - 1 - j;
    r[i] = r[i - limbs];
  }
  for i: u64 = 0 .. limbs {
    r[i] = 0u32;
  }

  if bits > 0 {
    for j: u64 = 0 .. n {
      let i: u64 = n - 1 - j;
      let lo: u32 = 0u32;
      if i > 0 {
        lo = r[i - 1] >> (u32) (32 - bits);
      }
      r[i] = (r[i] << (u32) bits) | lo;
    }
  }
}

/* r = -r */
fun big_neg(r: mut [u32; n], n: u64) {
  let carry: u64 = 1;
  for i: u64 = 0 .. n {
    let t: u64 = (u64) (~r[i]) + carry;
    r[i] = (u32) t;
    carry = t >> 32;
  }
}

/* the 64 bits of a starting at bit p */
fun big_bits64(a: [u32; n], p: u64, n: u64) -> u64 {
  let limb: u64 = p / 32;
  let bits: u64 = p % 32;
  assert limb + 2 < n;

  let lo: u64 = (u64) a[limb] | ((u64) a[limb + 1] << 32);
  if bits == 0 {
    return lo;
  }
  return (lo >> (u32) bits) | ((u64) a[limb + 2] << (u32) (64 - bits));
}

/* is any bit of a below position p set? */
fun big_low_nonzero(a: [u32; n], p: u64, n: u64) -> bool {
  let limb: u64 = p / 32;
  let bits: u64 = p % 32;
  assert limb < n;

  for i: u64 = 0 .. limb {
    if a[i] != 0u32 {
      return true;
    }
  }
  if bits > 0 {
    if (a[limb] & ((1u32 << (u32) bits) - 1u32)) != 0u32 {
      return true;
    }
  }
  return false;
}

/* ---------------------------------------- the certified polynomial (Cheb) */

/* CO[k] = A_k * 2^(XDEN*(7-k)), the coefficients of Horner's rule on V.
 * The A_k are the degree-7 Chebyshev interpolant of exp on [0.25, 0.25001)
 * certified in rocq/Cheb.v.  Capla has no hexadecimal literals, so each
 * limb is given in decimal with its hexadecimal value in comment. */
fun init_coeffs(CO: mut [[u32; n]; 8], n: u64) {
  assert n >= 7;

  for k: u64 = 0 .. 8 {
    big_zero(CO[k], n);
  }

  CO[0][0] = 3217918771u32;                                /* 0xbfcd8b33 */
  CO[0][1] = 2725669418u32;                                /* 0xa2766a2a */
  CO[0][2] = 530707746u32;                                 /* 0x1fa1f522 */
  CO[0][3] = 3653852563u32;                                /* 0xd9c95d93 */
  CO[0][4] = 2159947499u32;                                /* 0x80be2eeb */
  CO[0][5] = 2741106576u32;                                /* 0xa361f790 */
  CO[0][6] = 344679671u32;                                 /* 0x148b64f7 */

  CO[1][0] = 3467566012u32;                                /* 0xceaedbbc */
  CO[1][1] = 2759561012u32;                                /* 0xa47b8f34 */
  CO[1][2] = 530707746u32;                                 /* 0x1fa1f522 */
  CO[1][3] = 3653852563u32;                                /* 0xd9c95d93 */
  CO[1][4] = 2159947499u32;                                /* 0x80be2eeb */
  CO[1][5] = 2741106576u32;                                /* 0xa361f790 */
  CO[1][6] = 344679671u32;                                 /* 0x148b64f7 */

  CO[2][0] = 363618264u32;                                 /* 0x15ac5fd8 */
  CO[2][1] = 1167292282u32;                                /* 0x4593777a */
  CO[2][2] = 890978022u32;                                 /* 0x351b3ee6 */
  CO[2][3] = 3974409932u32;                                /* 0xece4aecc */
  CO[2][4] = 1079973749u32;                                /* 0x405f1775 */
  CO[2][5] = 3518036936u32;                                /* 0xd1b0fbc8 */
  CO[2][6] = 172339835u32;                                 /* 0x0a45b27b */

  CO[3][0] = 43408006u32;                                  /* 0x02965a86 */
  CO[3][1] = 3776778684u32;                                /* 0xe11d11bc */
  CO[3][2] = 635183673u32;                                 /* 0x25dc2239 */
  CO[3][3] = 1324803310u32;                                /* 0x4ef6e4ee */
  CO[3][4] = 1791647015u32;                                /* 0x6aca5d27 */
  CO[3][5] = 4035990509u32;                                /* 0xf09053ed */
  CO[3][6] = 57446611u32;                                  /* 0x036c90d3 */

  CO[4][0] = 3151405722u32;                                /* 0xbbd6a29a */
  CO[4][1] = 2853697771u32;                                /* 0xaa17f8eb */
  CO[4][2] = 1969350754u32;                                /* 0x7561e862 */
  CO[4][3] = 2700509051u32;                                /* 0xa0f67f7b */
  CO[4][4] = 1521653454u32;                                /* 0x5ab296ce */
  CO[4][5] = 4230223099u32;                                /* 0xfc2414fb */
  CO[4][6] = 14361652u32;                                  /* 0x00db2434 */

  CO[5][0] = 3574362114u32;                                /* 0xd50c7002 */
  CO[5][1] = 3369497746u32;                                /* 0xc8d67492 */
  CO[5][2] = 3568360808u32;                                /* 0xd4b0dd68 */
  CO[5][3] = 329496634u32;                                 /* 0x13a3b83a */
  CO[5][4] = 1163324161u32;                                /* 0x4556eb01 */
  CO[5][5] = 2564031538u32;                                /* 0x98d40432 */
  CO[5][6] = 2872330u32;                                   /* 0x002bd40a */

  CO[6][0] = 3781515065u32;                                /* 0xe1655739 */
  CO[6][1] = 2157836023u32;                                /* 0x809df6f7 */
  CO[6][2] = 2414889998u32;                                /* 0x8ff04c0e */
  CO[6][3] = 1862143731u32;                                /* 0x6efe0ef3 */
  CO[6][4] = 760143891u32;                                 /* 0x2d4ee013 */
  CO[6][5] = 3290651956u32;                                /* 0xc4235d34 */
  CO[6][6] = 478721u32;                                    /* 0x00074e01 */

  CO[7][0] = 561758758u32;                                 /* 0x217bc226 */
  CO[7][1] = 1835480026u32;                                /* 0x6d6733da */
  CO[7][2] = 2062168057u32;                                /* 0x7aea2ff9 */
  CO[7][3] = 2712686719u32;                                /* 0xa1b0507f */
  CO[7][4] = 749631732u32;                                 /* 0x2cae78f4 */
  CO[7][5] = 3537926861u32;                                /* 0xd2e07acd */
  CO[7][6] = 68388u32;                                     /* 0x00010b24 */

  for k: u64 = 0 .. 8 {
    big_shl(CO[k], XDEN! * (7 - k), n);
  }
}

/* V = P(x) * 2^VDEN for x = (Cc + d) / 2^XDEN.  Horner, with a signed d.
 * t is scratch the caller owns, since Capla has no globals. */
fun poly_eval(d: i64, V: mut [u32; n], CO: [[u32; n]; 8],
              t: mut [u32; n], n: u64) {
  let neg: bool = false;
  let e: i64 = d;

  if e < 0 {
    neg = true;
    e = -e;
  }
  let u: u64 = (u64) e;
  let dlo: u32 = (u32) u;
  let dhi: u32 = (u32) (u >> 32);

  big_set(V, CO[7], n);
  for j: u64 = 0 .. 7 {
    let k: u64 = 6 - j;
    big_set(t, V, n);
    big_mul32(t, dhi, n);
    big_shl_limb(t, n);
    big_mul32(V, dlo, n);
    big_add(V, t, n);
    if neg {
      big_neg(V, n);
    }
    big_add(V, CO[k], n);
  }
}
