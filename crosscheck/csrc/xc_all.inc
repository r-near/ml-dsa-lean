/* Three-level monolithic build of mldsa-native, as in examples/monolithic_build_multilevel_native. */
#define MLD_CONFIG_MULTILEVEL_WITH_SHARED 1
#define MLD_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#define MLD_CONFIG_PARAMETER_SET 44
#include "mldsa_native.c"
#undef MLD_CONFIG_MULTILEVEL_WITH_SHARED
#undef MLD_CONFIG_PARAMETER_SET

#define MLD_CONFIG_MULTILEVEL_NO_SHARED
#define MLD_CONFIG_PARAMETER_SET 65
#include "mldsa_native.c"
#undef MLD_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#undef MLD_CONFIG_PARAMETER_SET

#define MLD_CONFIG_PARAMETER_SET 87
#include "mldsa_native.c"
#undef MLD_CONFIG_PARAMETER_SET
