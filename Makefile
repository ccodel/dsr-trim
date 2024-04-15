CC = gcc
# CFLAGS = -DLONGTYPE -std=c99 -O3
# CFLAGS = -std=c99 -O2
CFLAGS = -std=c99 -O3

OFILES = xmalloc.o xio.o cnf_parser.o sr_parser.o global_data.o global_parsing.o
FILES = xmalloc.c xio.c cnf_parser.c global_data.c global_parsing.c
TRIM = dsr-trim
CHECK = lsr-check
COMPRESS = compress
DECOMPRESS = decompress
EXECS = $(TRIM) $(CHECK) $(COMPRESS) $(DECOMPRESS)

all: $(EXECS)

dsr-trim: $(TRIM).c $(OFILES)
	$(CC) $(CFLAGS) $(TRIM).c $(OFILES) -o $(TRIM)

lsr-check: $(CHECK).c $(OFILES)
	$(CC) $(CFLAGS) $(CHECK).c $(OFILES) -o $(CHECK)

compress: $(COMPRESS).c $(OFILES)
	$(CC) $(CFLAGS) $(COMPRESS).c $(OFILES) -o $(COMPRESS)

decompress: $(DECOMPRESS).c $(OFILES)
	$(CC) $(CFLAGS) $(DECOMPRESS).c $(OFILES) -o $(DECOMPRESS)

xmalloc.o: xmalloc.c
	$(CC) $(CFLAGS) -c xmalloc.c xmalloc.h

xio.o: xio.c
	$(CC) $(CFLAGS) -c xio.c xio.h

cnf_parser.o: cnf_parser.c
	$(CC) $(CFLAGS) -c cnf_parser.c cnf_parser.h

sr_parser.o: sr_parser.c
	$(CC) $(CFLAGS) -c sr_parser.c sr_parser.h

global_data.o: global_data.c global_data.h
	$(CC) $(CFLAGS) -c global_data.c global_data.h

global_parsing.o: global_parsing.c
	$(CC) $(CFLAGS) -c global_parsing.c global_parsing.h

clean:
	rm -rf *.o
	rm -f $(EXECS)
