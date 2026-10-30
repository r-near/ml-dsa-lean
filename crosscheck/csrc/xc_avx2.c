/* mldsa-native, x86_64 AVX2 backend (native arithmetic and Keccak). Built only for x86_64; the Rust side must
 * check for AVX2 at run time before calling anything in here (the library itself assumes the compile-time
 * feature set is present). */
#define XC_NS mldsaa
#define XC_BE a
#define XC_NATIVE 1
#define XC_RNG_FN xc_a_randombytes
#define MLD_CONFIG_FILE "xc_config.h"
#include "xc_all.inc"
#include "xc_wrap.inc"
