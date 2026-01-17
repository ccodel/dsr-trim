CC     = gcc
CFLAGS = -O3
RM     = rm -f
SRCDIR = src
BINDIR = bin

# Supporting files
# These get compiled to `.o` files without linking
SUPPFILES = bitmask cli cnf_parser global_data global_parsing hash_table \
						lit_occ logger range_array sr_parser timer xio xmalloc \
						lsr-check/lsr_data lsr-check/lsr_err
SUPPFILESWITHDIR = $(addprefix $(SRCDIR)/,$(SUPPFILES))
OFILES = $(addsuffix .o,$(SUPPFILESWITHDIR))

# Executable files
EXECS = dsr-trim lsr-check compress
EXECSWITHBINDIR = $(addprefix $(BINDIR)/,$(EXECS))

# A note on Makefile conventions/syntax:
# `$^` means all prerequisites for the rule
# `$<` is the first prerequisite for the rule
# `$@` means the target of the rule

# Compiles the `.c` files to make the target `.o` file
define cc-command
$(CC) $(CFLAGS) -c $< -o $@
endef

# Compiles the `.c` files to make an executable file
define cc-bin-command
$(CC) $(CFLAGS) $(SRCDIR)/$@.c $(OFILES) -o $(BINDIR)/$@
endef

# .PHONY means these rules get executed even if files of these names exist
.PHONY: all clean long

all: $(BINDIR) $(OFILES) $(EXECS)

long: CFLAGS += -DLONGTYPE
long: $(EXECS)

debug: CFLAGS += -DDEBUG -g
debug: $(EXECS)

clean:
	$(RM) $(SRCDIR)/*.o $(SRCDIR)/dsr-trim/*.o $(SRCDIR)/lsr-check/*.o
	$(RM) $(EXECSWITHBINDIR) $(EXECS) decompress $(BINDIR)/decompress

# Make the `bin/` directory, ignoring it if it already exists
$(BINDIR):
	mkdir -p $(BINDIR)

# Compile object files for the non-executable `.c` files
$(OFILES): %.o: %.c
	$(cc-command)

$(EXECS): % : $(SRCDIR)/%.c $(OFILES)
	$(cc-bin-command)
	ln -sf $(BINDIR)/$@ $@
