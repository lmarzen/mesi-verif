CC=gcc
CFLAGS=-w -O2
NPROC=1 #$(shell nproc)

# Compile Time Options for Spin and Pan
# https://spinroot.com/spin/Man/Pan.html#B
PAN_FLAGS=                            \
  -DXUSAFE -DMEMLIM=1500000           \
  -DNCORE=$(NPROC)                    \
  -DNOBOUNDCHECK -DNIBIS              \
  -DCOLLAPSE -DSPACE -DJOINPROCS

all: pan

mesi.i: mesi.pml Makefile
	python3 preprocess.py mesi.pml mesi.i

pan.c: mesi.i Makefile
	spin -a mesi.i

pan: pan.c Makefile
	$(CC) $(CFLAGS) $(PAN_FLAGS) -o pan pan.c

clean:
	rm -f *- pan pan.* *.trail *.rst *.cpu*_trail *.cpu*_rst *.i *.out *.tmp core


#-DCOLLAPSE 
#  -DCOLLAPSE # good, fast compression, or
#  -DMA=1340   # better/slower compression, or
#  -DHC # hash-compaction, approximation
#  -DBITSTATE # supertrace, approximation

# -DNOFAIR -DNOBOUNDCHECK

# -DBFS_PAR
# -DCOLLAPSE -DJOINPROCS -DSEPQS -DSPACE
