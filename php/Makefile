CC = gcc
CFLAGS = -DLONGTYPE -std=c99 -O3

all: php php-sr

php: php.c $(OFILES)
	$(CC) $(CFLAGS) php.c $(OFILES) -o php

php-sr: php-sr.c $(OFILES)
	$(CC) $(CFLAGS) php-sr.c $(OFILES) -o php-sr

clean:
	rm -rf *.o
	rm -f $(EXES)
