/* proto.h */

#ifndef PROTO

#ifndef NeedFunctionPrototypes
#if defined(FUNCPROTO) || __STDC__ || defined(__cplusplus) || defined(c_plusplus) //__STDC__, __cplusplus, c_plusplus是标准宏，意思是是否符合C标准，是否是C++。见：http://zh.wikipedia.org/zh/ANSI_C
#define NeedFunctionPrototypes 1//会执行。因为编译器是gcc？
#else
#define NeedFunctionPrototypes 0
#endif
#endif /* NeedFunctionPrototypes */

#  if NeedFunctionPrototypes
#    define PROTO( x )  x
#    define PARAMS( x )
#    define EXTERN_FUNCTION( fun, args ) extern fun args
#    define STATIC_FUNCTION( fun, args ) static fun args
#  else
#    define PROTO( x )
#    define PARAMS( x ) x 
#    define EXTERN_FUNCTION( fun, args ) extern fun ()
#    define STATIC_FUNCTION( fun, args ) static fun ()
#  endif

#endif /* PROTO */

