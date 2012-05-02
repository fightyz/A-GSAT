CFLAGS = -g # -O1...-O3是指的编译器的优化级别,用GDB调试时不能使用优化选项，否则会出现变量值和源代码无法对应等问题

LIB    =   -lm # 指名需要用libm.so, libm.a这两个数学库；连静态库的时候前面的lib（l代表lib）和后面的.a是省略的，-lm应该是连libm.a库。优先选libm.so,没有就libm.a 

SOURCES = gsat.c anneal.c urand.c  utils.c globals.c
HEADERS = gsat.h anneal.h urand.h utils.h proto.h adjust_bucket.h
OBJECTS = urand.o gsat.o globals.o anneal.o utils.o
AUX = Makefile GSAT_USERS_GUIDE gsat.1 ex.wff

gsat: $(SOURCES) $(HEADERS)
	gcc $(CFLAGS) $(SOURCES) $(LIB) -o gsat # 这里是用隐晦规则判定出.o依赖文件

clean:
	'rm' -f gsat *.o

tar:
	'rm' -f gsat.tar.Z*
	tar cvof gsat.tar $(SOURCES) $(HEADERS) $(AUX)
	compress gsat.tar
	uuencode gsat.tar.Z gsat.tar.Z > gsat.tar.Z.uu



