CC     = gcc
# CFLAGS = -DLONGTYPE -O3
# CFLAGS = -O2
CFLAGS = -O3
RM     = rm -f
SRCDIR = src

OFILES = xmalloc.o xio.o logger.o cnf_parser.o sr_parser.o global_data.o global_parsing.o range_array.o hash_table.o cli.o
FILES = xmalloc.c xio.c logger.c cnf_parser.c global_data.c global_parsing.c range_array.c hash_table.c cli.c
TRIM = dsr-trim
CHECK = lsr-check
COMPRESS = compress
DECOMPRESS = decompress
EXECS = $(TRIM) $(CHECK) $(COMPRESS) $(DECOMPRESS)
# EXECS = $(CHECK) $(COMPRESS) $(DECOMPRESS)

define cc-command
$(CC) $(CFLAGS) -c $^ -o $@
endef

define cc-bin-command
$(CC) $(CFLAGS) $^ -o $@
endef

# .PHONY means these rules get executed even if files of these names exist
.PHONY: all clean

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
	$(cc-command)

xio.o: xio.c
	$(cc-command)

logger.o: logger.c
	$(cc-command)

range_array.o: range_array.c
	$(cc-command)

hash_table.o: hash_table.c
	$(cc-command)

cli.o: cli.c
	$(cc-command)

cnf_parser.o: cnf_parser.c
	$(CC) $(CFLAGS) -c cnf_parser.c

sr_parser.o: sr_parser.c
	$(CC) $(CFLAGS) -c sr_parser.c

global_data.o: global_data.c
	$(CC) $(CFLAGS) -c global_data.c

global_parsing.o: global_parsing.c
	$(CC) $(CFLAGS) -c global_parsing.c

clean:
	$(RM) *.o
	$(RM) $(EXECS)
