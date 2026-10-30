/* Assembly half of the mldsa-native AVX2 backend, same configuration as xc_avx2.c. */
#define XC_NS mldsaa
#define XC_NATIVE 1
#define XC_RNG_FN xc_a_randombytes
#define MLD_CONFIG_FILE "xc_config.h"
#define MLD_CONFIG_MULTILEVEL_WITH_SHARED
#include "mldsa_native_asm.S"
