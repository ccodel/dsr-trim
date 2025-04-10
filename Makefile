CC     = gcc
CFLAGS = -O3
RM     = rm -f
SRCDIR = src
BINDIR = bin

# Supporting files
# These get compiled to `.o` files without linking
SUPPFILES = cli cnf_parser global_data global_parsing hash_table logger \
						range_array sr_parser timer xio xmalloc
SUPPFILESWITHDIR = $(addprefix $(SRCDIR)/,$(SUPPFILES))
OFILES = $(addsuffix .o,$(SUPPFILESWITHDIR))

# Executable files
EXECS = dsr-trim lsr-check compress decompress
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

all: $(BINDIR) $(EXECS)

long: CFLAGS += -DLONGTYPE
long: $(EXECS)

debug: CFLAGS += -DDEBUG -g
debug: $(EXECS)

clean:
	$(RM) $(SRCDIR)/*.o
	$(RM) $(EXECSWITHBINDIR)
	$(RM) $(EXECS)

# Make the `bin/` directory, ignoring it if it already exists
$(BINDIR):
	mkdir -p $(BINDIR)

# Compile object files for the non-executable `.c` files
$(OFILES): %.o: %.c
	$(cc-command)

$(EXECS): % : $(SRCDIR)/%.c $(OFILES)
	$(cc-bin-command)
	ln -sf $(BINDIR)/$@ $@
