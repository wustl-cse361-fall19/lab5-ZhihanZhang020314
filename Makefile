#
# Makefile for the malloc lab
#
CC = gcc

# Change this to -O0 (big-Oh, numeral zero) if you need to use a debugger on your code
COPT = -O3
CFLAGS = -Wall -Wextra -Werror $(COPT) -g -DDRIVER -Wno-unused-function -Wno-unused-parameter
LIBS = -lm

COBJS = memlib.o fcyc.o clock.o stree.o
NOBJS = mdriver.o mm.o $(COBJS)

MC = ./macro-check.pl
MCHECK = $(MC)

all: mdriver

# Regular driver
mdriver: $(NOBJS)
	$(CC) $(CFLAGS) -o mdriver $(NOBJS) $(LIBS)

mm.o: mm.c mm.h memlib.h $(MC)
	$(MCHECK) -f mm.c
	$(CC) $(CFLAGS) -c mm.c -o mm.o

mdriver.o: mdriver.c fcyc.h clock.h memlib.h config.h mm.h stree.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h
stree.o: stree.c stree.h

clean:
	rm -f *~ *.o mdriver

handin:
	@echo 'Commit your mm.c file into your GitHub repo.'
