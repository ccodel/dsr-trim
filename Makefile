CC = gcc
# CFLAGS = -DLONGTYPE -std=c99 -O3
CFLAGS = -std=c99 -O3

OFILES = xmalloc.o xio.o cnf_parser.o sr_parser.o global_data.o global_parsing.o
FILES = xmalloc.c xio.c cnf_parser.c global_data.c global_parsing.c
TRIM = dsr-trim
CHECK = lsr-check
EXECS = $(TRIM) $(CHECK)

all: $(EXECS)

dsr-trim: $(TRIM).c $(OFILES)
	$(CC) $(CFLAGS) $(TRIM).c $(OFILES) -o $(TRIM)

lsr-check: $(CHECK).c $(OFILES)
	$(CC) $(CFLAGS) $(CHECK).c $(OFILES) -o $(CHECK)

xmalloc.o: xmalloc.c
	$(CC) $(CFLAGS) -c xmalloc.c

xio.o: xio.c
	$(CC) $(CFLAGS) -c xio.c

cnf_parser.o: cnf_parser.c
	$(CC) $(CFLAGS) -c cnf_parser.c

sr_parser.o: sr_parser.c
	$(CC) $(CFLAGS) -c sr_parser.c

global_data.o: global_data.c
	$(CC) $(CFLAGS) -c global_data.c

global_parsing.o: global_parsing.c
	$(CC) $(CFLAGS) -c global_parsing.c

clean:
	rm -rf *.o
	rm -f $(EXECS)
