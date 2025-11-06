CC ?= gcc
CFLAGS = -DLONGTYPE -std=c99 -O3
EXECS = php php-sr

all: $(EXECS)

php: php.c
	$(CC) $(CFLAGS) php.c -o php

php-sr: php-sr.c
	$(CC) $(CFLAGS) php-sr.c -o php-sr

clean:
	rm -rf *.o
	rm -f $(EXECS)
