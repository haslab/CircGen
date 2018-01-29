include ../../../Makefile.config

CCOMP=../../../circgen
CCOMPFLAGS=-stdlib ../../../runtime -floop_unroll 10 -dcminor -drtl

PROGS=test1 test2 test3 test4 test5 test6 sha256-blocks

all: $(PROGS:%=%.hlc)

%.hlc: %.c $(CCOMP)
	($(CCOMP) $(CCOMPFLAGS) $*.c $(LIBS); true)

clean:
	rm -f *.cm *.rtl.? *.rtl.circ *.hlc *~
