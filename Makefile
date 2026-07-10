CC     = gcc
CFLAGS = -O3
RM     = rm -f
SRCDIR = src
BINDIR = bin

#############
# Note: Add to `SUPPFILES` and `EXECS` when new files are added.
#############

# Supporting source files (without .c extension)
SUPPFILES = bitmask cli cnf_parser global_data global_parsing hash_table \
            lit_occ logger range_array sr_parser timer xio xmalloc \
            lsr-check/lsr_data lsr-check/lsr_err

# Executable files
EXECS = dsr-trim lsr-check compress
EXECSWITHBINDIR = $(addprefix $(BINDIR)/,$(EXECS))

# Object files get compiled to `bin/`, flattened
OFILES = $(addprefix $(BINDIR)/,$(addsuffix .o,$(notdir $(SUPPFILES))))

# Compiles the `.c` file into an object file
define cc-command
$(CC) $(CFLAGS) -c $< -o $@
endef

# Compiles the `.c` file into an executable
define cc-bin-command
$(CC) $(CFLAGS) $(SRCDIR)/$(notdir $@).c $(OFILES) -o $@
endef

.PHONY: all clean veryclean long debug

all: $(BINDIR) $(OFILES) $(EXECS)

long: CFLAGS += -DLONGTYPE
long: all

debug: CFLAGS += -DDEBUG -g
debug: all

clean:
	$(RM) $(OFILES)
	$(RM) $(EXECSWITHBINDIR)
	$(RM) $(EXECS) decompress $(BINDIR)/decompress

# Remove any symbolic debug files created on Mac (e.g. `*.dSYM/`)
veryclean: clean
	$(RM) -r $(addsuffix .dSYM,$(EXECSWITHBINDIR))

# Create the `bin/` directory
$(BINDIR):
	mkdir -p $(BINDIR)

# Compile all supporting object files
$(BINDIR)/%.o: $(SRCDIR)/%.c
	$(cc-command)

# Special rule for nested sources
$(BINDIR)/%.o:
	$(CC) $(CFLAGS) -c $(shell find $(SRCDIR) -name $*.c) -o $@

# Build the executables, and symlink them to the root directory
$(EXECSWITHBINDIR): $(OFILES)
$(EXECS): %: $(BINDIR)/%
	$(cc-bin-command)
	ln -sf $(BINDIR)/$@ $@
