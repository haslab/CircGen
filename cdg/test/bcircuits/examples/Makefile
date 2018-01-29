include ../../../Makefile.config

CCOMP=../../../circgen
CCOMPFLAGS=-floop_unroll 100

PROGS= millionaires isort lsearch ce isort_chk

all: $(PROGS:%=%.circ)

%.hlc: %.c $(CCOMP)
	($(CCOMP) $(CCOMPFLAGS) -dhlc $*.c $(LIBS); true)

%.llc: %.c $(CCOMP)
	($(CCOMP) $(CCOMPFLAGS) -dllc $*.c $(LIBS); true)

%.circ: %.c $(CCOMP)
	($(CCOMP) $(CCOMPFLAGS) -bristol-smc $*.c $(LIBS); true)

clean:
	rm -f *.cm *.rtl.* *.rtlc.* *.valc *.hlc *.llc *.circ *~

unittest: CCOMPFLAGS += -unittest -show-stats
unittest: all

selftest: CCOMPFLAGS += -selftest 100
selftest: unittest

dbg: CCOMPFLAGS += -drtl -drtlc -dhlc -dllc
dbg: all

