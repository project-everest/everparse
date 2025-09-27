#ifndef __TIMING_H
#define __TIMING_H

#include <time.h>
#include <stdio.h>

static inline float __tdiff(struct timespec t1, struct timespec t2)
{
	return (t2.tv_sec - t1.tv_sec)
		+ 1e-9 * (t2.tv_nsec - t1.tv_nsec);
}

/* Set to 0 to not print the parallel factor */
static int time_par = 0;
/* Set to 0 to not print any messages */
static int print = 0;

#ifdef __cplusplus // typeof is not defined in C++
#define __TIME(s, expr, v) ({						\
		struct timespec __t1p, __t2p;				\
		struct timespec __t1w, __t2w;				\
		float *__vv = v;					\
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &__t1p);	\
		clock_gettime(CLOCK_REALTIME, &__t1w);			\
		print && fprintf(stderr, "About to call `" s "` \n");	\
		auto __ret = expr;					\
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &__t2p);	\
		clock_gettime(CLOCK_REALTIME, &__t2w);			\
		print && fprintf(stderr, "computed `" s "` in %.5fs total "	\
				"CPU time (wall time = %.5fs)\n",	\
				__tdiff(__t1p, __t2p),			\
				__tdiff(__t1w, __t2w));			\
		if (print && time_par)						\
			fprintf(stderr, "(parallel factor = %.2f)\n",	\
					__tdiff(__t1p, __t2p)/		\
					__tdiff(__t1w, __t2w));		\
		if (__vv)						\
		        *__vv = __tdiff(__t1w, __t2w);			\
		__ret;})
#else // __cplusplus
#define __TIME(s, expr, v) ({						\
		struct timespec __t1p, __t2p;				\
		struct timespec __t1w, __t2w;				\
		typeof(expr) __ret;					\
		float *__vv = v;					\
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &__t1p);	\
		clock_gettime(CLOCK_REALTIME, &__t1w);			\
		print && fprintf(stderr, "About to call `" s "` \n");	\
		__ret = expr;						\
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &__t2p);	\
		clock_gettime(CLOCK_REALTIME, &__t2w);			\
		print && fprintf(stderr, "computed `" s "` in %.5fs total "	\
				"CPU time (wall time = %.5fs)\n",	\
				__tdiff(__t1p, __t2p),			\
				__tdiff(__t1w, __t2w));			\
		if (print && time_par)						\
			fprintf(stderr, "(parallel factor = %.2f)\n",	\
					__tdiff(__t1p, __t2p)/		\
					__tdiff(__t1w, __t2w));		\
		if (__vv)						\
		        *__vv = __tdiff(__t1w, __t2w);			\
		__ret;})
#endif // __cplusplus

/*
 * Given an expression [expr] y a float pointer [v]
 * this prints the time taken by computing [expr]
 * (if print above is non-zero) and stores it in [v]
 * (if v != NULL).
 */
#define TIME0(expr, v) __TIME(#expr, expr, v)
/* Extra indirection expands stmt before we stringify it. */
#define TIME(expr, v) TIME0(expr, v)

/* Similar to TIME, for statements. */
#define TIME_void0(stmt, v) __TIME(#stmt, (stmt, 1), v)
/* Extra indirection expands stmt before we stringify it. */
#define TIME_void(stmt, v) TIME_void0(stmt, v)

#define __TIMEREP(s, n, expr, v)		\
	__TIME(s,				\
		({				\
		int __i;			\
		int __n = n;			\
		typeof(expr) __r;		\
		for (__i = 0; __i < __n; ++__i)	\
			__r = expr;		\
		__r; }), v )

#endif
