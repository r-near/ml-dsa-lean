/* mldsa-native configuration for the crosscheck harness.
 *
 * Multi-level build (44/65/87 in one translation unit) with a per-build namespace prefix (XC_NS), so the portable
 * and the AVX2 builds can be linked into the same binary. Entry points are static; xc_wrap.inc exports thin
 * wrappers. The only non-default pieces are the namespace, the native backends (AVX2 build only) and a
 * randombytes hook that returns bytes the harness chose, so the randomized entry points (keypair, signature)
 * can be driven deterministically. */
#ifndef XC_CONFIG_H
#define XC_CONFIG_H

#ifndef MLD_CONFIG_PARAMETER_SET
#define MLD_CONFIG_PARAMETER_SET 44
#endif

#define MLD_CONFIG_NAMESPACE_PREFIX XC_NS
#define MLD_CONFIG_MULTILEVEL_BUILD
#define MLD_CONFIG_EXTERNAL_API_QUALIFIER static
#define MLD_CONFIG_INTERNAL_API_QUALIFIER static

#if defined(MLD_BUILD_INTERNAL)

#if defined(XC_NATIVE)
#define MLD_CONFIG_USE_NATIVE_BACKEND_ARITH
#define MLD_CONFIG_ARITH_BACKEND_FILE "native/meta.h"
#define MLD_CONFIG_USE_NATIVE_BACKEND_FIPS202
#define MLD_CONFIG_FIPS202_BACKEND_FILE "fips202/native/auto.h"
#endif

#define MLD_CONFIG_CUSTOM_RANDOMBYTES
#if !defined(__ASSEMBLER__)
#include <stddef.h>
#include <stdint.h>
#include "src/sys.h"
/* Defined in xc_wrap.inc: fills ptr from the thread-local buffer set by the harness. */
int XC_RNG_FN(uint8_t *ptr, size_t len);
static MLD_INLINE int mld_randombytes(uint8_t *ptr, size_t len)
{
  return XC_RNG_FN(ptr, len);
}
#endif /* !__ASSEMBLER__ */

#endif /* MLD_BUILD_INTERNAL */

#endif /* XC_CONFIG_H */
