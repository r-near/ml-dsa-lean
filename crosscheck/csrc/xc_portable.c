/* mldsa-native, portable C backend (no native arithmetic, no native FIPS 202). */
#define XC_NS mldsap
#define XC_BE p
#define XC_RNG_FN xc_p_randombytes
#define MLD_CONFIG_FILE "xc_config.h"
#include "xc_all.inc"
#include "xc_wrap.inc"
