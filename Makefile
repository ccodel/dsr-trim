CC = gcc
CFLAGS = -DLONGTYPE -std=c99 -O3

OFILES = xmalloc.o xio.o cnf_parser.o global_data.o
FILES = xmalloc.c xio.c cnf_parser.c global_data.c
EXES  = sr-trim sr-check

all: $(EXES)

sr-trim: sr-trim.c $(OFILES)
	$(CC) $(CFLAGS) sr-trim.c $(OFILES) -o sr-trim

sr-check: sr-check.c $(FILES)
	$(CC) $(CFLAGS) sr-check.c $(OFILES) -o sr-check

xmalloc.o: xmalloc.c
	$(CC) $(CFLAGS) -c xmalloc.c

xio.o: xio.c
	$(CC) $(CFLAGS) -c xio.c

cnf_parser.o: cnf_parser.c
	$(CC) $(CFLAGS) -c cnf_parser.c

global_data.o: global_data.c
	$(CC) $(CFLAGS) -c global_data.c

clean:
	rm -rf *.o
	rm -f $(EXES)
