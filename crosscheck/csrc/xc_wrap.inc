/* Exported wrappers around one mldsa-native build. Included after xc_all.inc with
 *   XC_NS   namespace prefix of the build (mldsap or mldsaa)
 *   XC_BE   short backend tag used in the exported names (p or a)
 * Every wrapper takes the security level (44, 65 or 87) and returns mldsa-native's int status; -1000 means "bad
 * level". The randomized entry points read their random bytes from xc_rng_buf (thread-local), set per call. */
#include <string.h>

#define XC_CAT_(a, b) a##b
#define XC_CAT(a, b) XC_CAT_(a, b)
#define XC_CAT3_(a, b, c) a##b##c
#define XC_CAT3(a, b, c) XC_CAT3_(a, b, c)
#define XC_EXPORT(name) XC_CAT3(xc_, XC_BE, XC_CAT(_, name))

/* mldsa-native symbol for a level: <XC_NS><level>_<fn> */
#define XC_SYM(lvl, fn) XC_CAT3(XC_NS, lvl, XC_CAT(_, fn))

static _Thread_local uint8_t xc_rng_buf[256];
static _Thread_local size_t xc_rng_len;
static _Thread_local size_t xc_rng_pos;

int XC_RNG_FN(uint8_t *ptr, size_t len)
{
  if (xc_rng_pos + len > xc_rng_len)
  {
    return -1; /* MLD_ERR_RNG_FAIL path: the harness asked for more than it supplied */
  }
  memcpy(ptr, xc_rng_buf + xc_rng_pos, len);
  xc_rng_pos += len;
  return 0;
}

static void xc_rng_set(const uint8_t *buf, size_t len)
{
  memcpy(xc_rng_buf, buf, len);
  xc_rng_len = len;
  xc_rng_pos = 0;
}

#define XC_SWITCH(lvl, call44, call65, call87) \
  switch (lvl)                                 \
  {                                            \
    case 44:                                   \
      return call44;                           \
    case 65:                                   \
      return call65;                           \
    case 87:                                   \
      return call87;                           \
    default:                                   \
      return -1000;                            \
  }

/* Algorithm 6 (KeyGen_internal) from a 32-byte seed. */
int XC_EXPORT(keypair_internal)(int lvl, uint8_t *pk, uint8_t *sk, const uint8_t *seed)
{
  XC_SWITCH(lvl, XC_SYM(44, keypair_internal)(pk, sk, seed), XC_SYM(65, keypair_internal)(pk, sk, seed),
            XC_SYM(87, keypair_internal)(pk, sk, seed))
}

/* Algorithm 1 (KeyGen): the 32-byte seed is drawn from the randombytes hook. */
int XC_EXPORT(keypair)(int lvl, uint8_t *pk, uint8_t *sk, const uint8_t *seed)
{
  xc_rng_set(seed, 32);
  XC_SWITCH(lvl, XC_SYM(44, keypair)(pk, sk), XC_SYM(65, keypair)(pk, sk), XC_SYM(87, keypair)(pk, sk))
}

/* Algorithm 7 (Sign_internal): explicit rnd, explicit prefix, not external mu. */
int XC_EXPORT(signature_internal)(int lvl, uint8_t *sig, const uint8_t *m, size_t mlen, const uint8_t *pre,
                                  size_t prelen, const uint8_t *rnd, const uint8_t *sk)
{
  XC_SWITCH(lvl, XC_SYM(44, signature_internal)(sig, m, mlen, pre, prelen, rnd, sk, 0),
            XC_SYM(65, signature_internal)(sig, m, mlen, pre, prelen, rnd, sk, 0),
            XC_SYM(87, signature_internal)(sig, m, mlen, pre, prelen, rnd, sk, 0))
}

/* Algorithm 2 (Sign): rnd comes from the randombytes hook. */
int XC_EXPORT(signature)(int lvl, uint8_t *sig, const uint8_t *m, size_t mlen, const uint8_t *ctx, size_t ctxlen,
                         const uint8_t *rnd, const uint8_t *sk)
{
  xc_rng_set(rnd, 32);
  XC_SWITCH(lvl, XC_SYM(44, signature)(sig, m, mlen, ctx, ctxlen, sk),
            XC_SYM(65, signature)(sig, m, mlen, ctx, ctxlen, sk), XC_SYM(87, signature)(sig, m, mlen, ctx, ctxlen, sk))
}

/* Algorithm 8 (Verify_internal) with explicit prefix. 0 = valid. */
int XC_EXPORT(verify_internal)(int lvl, const uint8_t *sig, const uint8_t *m, size_t mlen, const uint8_t *pre,
                               size_t prelen, const uint8_t *pk)
{
  XC_SWITCH(lvl, XC_SYM(44, verify_internal)(sig, m, mlen, pre, prelen, pk, 0),
            XC_SYM(65, verify_internal)(sig, m, mlen, pre, prelen, pk, 0),
            XC_SYM(87, verify_internal)(sig, m, mlen, pre, prelen, pk, 0))
}

/* Algorithm 3 (Verify). 0 = valid. */
int XC_EXPORT(verify)(int lvl, const uint8_t *sig, const uint8_t *m, size_t mlen, const uint8_t *ctx, size_t ctxlen,
                      const uint8_t *pk)
{
  XC_SWITCH(lvl, XC_SYM(44, verify)(sig, m, mlen, ctx, ctxlen, pk), XC_SYM(65, verify)(sig, m, mlen, ctx, ctxlen, pk),
            XC_SYM(87, verify)(sig, m, mlen, ctx, ctxlen, pk))
}

/* Secret-key validation and public-key recomputation (checks s1/s2 range, t0 and tr). 0 = valid. */
int XC_EXPORT(pk_from_sk)(int lvl, uint8_t *pk, const uint8_t *sk)
{
  XC_SWITCH(lvl, XC_SYM(44, pk_from_sk)(pk, sk), XC_SYM(65, pk_from_sk)(pk, sk), XC_SYM(87, pk_from_sk)(pk, sk))
}
