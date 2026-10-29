CC     = gcc
CFLAGS = -O3 -flto

# Tracks whether header files have changed
DEPFLAGS = -MMD -MP

# Important directories, relative to the Makefile
SRCDIR = src
BINDIR = bin

# Base cleanup command
RM     = rm -f

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
EXEC_OFILES = $(addsuffix .o,$(EXECSWITHBINDIR))

# Header dependency files, generated alongside each object file
DFILES = $(OFILES:.o=.d) $(EXEC_OFILES:.o=.d)

# Compiles the `.c` file into an object file
define cc-command
$(CC) $(CFLAGS) $(DEPFLAGS) -c $< -o $@
endef

# Links the executable's object file with the supporting object files
define cc-bin-command
$(CC) $(CFLAGS) $^ -o $@
endef

.PHONY: all clean veryclean long debug

all: $(BINDIR) $(OFILES) $(EXECS)

long: CFLAGS += -DLONGTYPE
long: all

debug: CFLAGS += -DDEBUG -g
debug: all

clean:
	$(RM) $(OFILES) $(EXEC_OFILES) $(DFILES)
	$(RM) $(EXECSWITHBINDIR)
	$(RM) $(EXECS) decompress $(BINDIR)/decompress

# Remove any symbolic debug files created on Mac (e.g. `*.dSYM/`)
veryclean: clean
	$(RM) -r $(addsuffix .dSYM,$(EXECSWITHBINDIR))

# Create the `bin/` directory
$(BINDIR):
	mkdir -p $(BINDIR)

# Search the source directory and any nested source directories for `.c` files
vpath %.c $(SRCDIR) $(addprefix $(SRCDIR)/,$(dir $(SUPPFILES)))

# Compile all object files
$(BINDIR)/%.o: %.c | $(BINDIR)
	$(cc-command)

# Link the executables, and symlink them to the root directory
$(EXECSWITHBINDIR): $(BINDIR)/%: $(BINDIR)/%.o $(OFILES)
	$(cc-bin-command)

$(EXECS): %: $(BINDIR)/%
	ln -sf $(BINDIR)/$@ $@

-include $(DFILES)
