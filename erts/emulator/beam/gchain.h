#ifndef __GCHAIN_H
#define __GCHAIN_H

#define GCHAIN_MAX_ORDER 16
#define GCHAIN_MAX_IDX 12
extern erts_atomic64_t gchain_counts[GCHAIN_MAX_ORDER][GCHAIN_MAX_IDX];

#endif /* __GCHAIN_H */

