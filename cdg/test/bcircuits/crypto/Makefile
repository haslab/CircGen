include ../../../Makefile.config

CCOMP=../../../circgen
CCOMPFLAGS=-floop_unroll 64

PROGS= sha256-blocks aes-tab32 aes-tab-sbox aes-opt-sbox

all: $(PROGS:%=%.circ)

%.hlc: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -dhlc $*.c

%.llc: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -dllc $*.c)

%.circ: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -bristol-smc $*.c

%.circ.noopt: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -nosimpl -noxpnd -bristol-smc $*.c

clean:
	rm -f *.cm *.rtl.* *.rtlc.* *.valc *.hlc *.llc *.circ *~

unittest: CCOMPFLAGS += -unittest -show-stats
unittest: all

selftest: CCOMPFLAGS += -selftest 100
selftest: unittest

noopt: CCOMPFLAGS += -nosimpl -noxpnd
noopt: all

dbg: CCOMPFLAGS += -drtl -drtlc -dhlc -dllc
dbg: all

