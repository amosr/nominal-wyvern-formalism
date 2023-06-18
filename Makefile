BUILD       ?= build

FSTAR_EXE   ?= fstar.exe
Q           ?= @

# Set ADMIT=1 to admit queries
ADMIT ?=
FSTAR_MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR_NL_DISABLE  ?= --z3smtopt '(set-option :smt.arith.nl false)'
FSTAR_ARITH_UNBOX ?= --smtencoding.l_arith_repr native --smtencoding.elim_box true
# Disable FSTAR_NL_DISABLE and FSTAR_ARITH_UNBOX?
FSTAR_PROOF_OPT   ?= $(FSTAR_NL_DISABLE) $(FSTAR_ARITH_UNBOX)

FSTAR_INCLUDES	  ?= --include src
FSTAR_CACHE       ?= --cache_dir $(BUILD)/cache --cache_checked_modules --already_cached Prims,FStar,LowStar
FSTAR_HINTS       ?= --hint_dir $(BUILD)/hint --use_hints --record_hints --warn_error -333

FSTAR_DEP_OPT     ?= $(FSTAR_INCLUDES) $(FSTAR_CACHE)

FSTAR_EXTRA_OPT   ?=
FSTAR_OPT		  ?= $(FSTAR_INCLUDES) $(FSTAR_PROOF_OPT) $(FSTAR_CACHE) $(FSTAR_EXTRA_OPT) $(FSTAR_MAYBE_ADMIT)

FSTAR_SRCS = $(wildcard src/**.fst src/**.fsti)

.PHONY: all
all: verify

$(BUILD)/deps.mk.rsp:
	@mkdir -p $(BUILD)

$(BUILD)/deps.mk: $(BUILD)/deps.mk.rsp $(FSTAR_SRCS)
	@echo "* Updating dependencies"
	@true $(shell rm -f $@.rsp) $(foreach f,$(FSTAR_SRCS),$(shell echo $(f) >> $@.rsp))
	$(Q)$(FSTAR_EXE) $(FSTAR_DEP_OPT) --dep full @$@.rsp > $@.tmp
	@mv $@.tmp $@

include $(BUILD)/deps.mk

%.fst.checked:
	@echo "* Checking: $<"
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $<
	@touch -c $@

.PHONY: verify
verify: $(ALL_CHECKED_FILES)

.PHONY: clean
clean:
	@echo "* Cleaning *.checked"
	@rm -f $(BUILD)/cache/*.checked
