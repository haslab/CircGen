CCOMP=../../../../circgen
CCOMPFLAGS=-fce -bristol-smc -floop_unroll $(UNROLLS) -p1inputs $(INPUTS1)

all: $(PROGS:%=%.circ) $(PROGS:%=%.count)

noopt: $(PROGS:%=%.circ.noopt) $(PROGS:%=%.count)

%.circ: %.c
	($(CCOMP) $(CCOMPFLAGS) $*.c; true)

%.circ.noopt: %.c
	($(CCOMP) $(CCOMPFLAGS) -nosimpl -noxpnd $*.c; true)

count: $(PROGS:%=%.count)

%.count: %.circ
	../count_gates.sh $*.circ

clean:
	rm -f *.circ
