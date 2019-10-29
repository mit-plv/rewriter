.SUFFIXES:

MOD_NAME:=Rewriter
SRC_DIR:=src/Rewriter
PLUGINS_DIR:=$(SRC_DIR)/Util/plugins

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

PYTHON3 := python3

STRICT_DEPS?=

EXTERNAL_PERF_DEPENDENCIES?=

include Makefile.local.common
include Makefile.coq

ifneq ($(COQ_EXTENDED_VERSION),$(COQ_EXTENDED_VERSION_OLD))
$(COQ_VERSION_FILE)::
	$(SHOW)'echo $$COQ_VERSION_INFO ($(COQ_VERSION)) > $@'
	$(HIDE)echo "$(COQ_EXTENDED_VERSION)" > $@
endif

clean::
	rm -f $(COQ_VERSION_FILE)

# This target is used to update the _CoqProject file.
SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
EXISTING_COQPROJECT_CONTENTS:=$(shell cat _CoqProject 2>&1)
WARNINGS:=+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern
COQPROJECT_CMD:=echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-I $(PLUGINS_DIR)'; echo '-arg -w -arg $(WARNINGS)'; (git ls-files '$(SRC_DIR)/*.v' '$(SRC_DIR)/*.mlg' '$(SRC_DIR)/*.mllib' '$(SRC_DIR)/*.ml' '$(SRC_DIR)/*.mli' | $(SORT_COQPROJECT)); (echo '$(COMPATIBILITY_FILES)' | tr ' ' '\n')
NEW_COQPROJECT_CONTENTS:=$(shell $(COQPROJECT_CMD))

ifneq ($(EXISTING_COQPROJECT_CONTENTS),$(NEW_COQPROJECT_CONTENTS))
.PHONY: _CoqProject
_CoqProject:
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)($(COQPROJECT_CMD)) > $@
endif

clean::
	rm -f _CoqProject



.DEFAULT_GOAL := all

# Setting this will make things unpleasant on a clean build, but also helps enormously with diagnosing errors
EXTRA_SED_FOR_DEPS:=
ifneq (,$(STRICT_DEPS))
EXTRA_SED_FOR_DEPS:=| sed s'/-include $$(ALLDFILES)/include $$(ALLDFILES)/g'
endif

# Note that the OTHERFLAGS bit is to work around COQBUG(https://github.com/coq/coq/issues/10905)
# We must also work around COQBUG(https://github.com/coq/coq/issues/10907) and fix the conf target
Makefile.coq Makefile-old.conf: Makefile _CoqProject $(COQ_VERSION_FILE)
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > Makefile.coq'
	$(HIDE)(($(COQBIN)coq_makefile -f _CoqProject -o Makefile-old && cat Makefile-old | sed s'/OTHERFLAGS        :=/OTHERFLAGS        ?=/g' | sed s'/Makefile-old.conf:/Makefile-old-old.conf:/g' | sed s'/Makefile-old.local/Makefile.local/g' $(EXTRA_SED_FOR_DEPS)); echo; echo 'include Makefile.local-late') > Makefile.coq && rm Makefile-old

Makefile.coq: | Makefile-old.conf

clean::
	rm -f Makefile.coq

##########################################
## Perf-testing section
include Makefile.perf

NO_LIMIT_PERF?=
MAX_PERF_KB?=10000000 # 10 GB
MAX_PERF_SEC?=
TIMEOUT_CMD?=
TIMEOUT_SHOW?=

ifneq (,$(NO_LIMIT_PERF))
ifneq (,$(MAX_PERF_SEC))
PERF_T_ARG:=-t $(MAX_PERF_SEC) # trailing space important
else
PERF_T_ARG:=
endif

TIMEOUT_CMD := etc/timeout/timeout -m $(MAX_PERF_KB) $(PERF_T_ARG)
TIMEOUT_SHOW:=TIMEOUT -m $(MAX_PERF_KB) $(PERF_T_ARG)
endif

.PHONY: perf
perf: $(ALL_PERF_LOGS)

ifneq ($(EXTERNAL_PERF_DEPENDENCIES),1)
$(ALL_PERF_LOGS): src/Rewriter/Rewriter/Examples/PerfTesting/Harness.vo
endif

$(ALL_PERF_LOGS) : %.log : %.v
	$(SHOW)'$(TIMEOUT_SHOW)COQC $(<:src/Rewriter/Rewriter/Examples/PerfTesting/%.v=%) > LOG'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(TIMEOUT_CMD) $(COQC) $(COQDEBUG) $(TIMING_ARG) $(COQFLAGS) $(COQLIBS) $< && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok
	$(HIDE)mv -f $@.tmp $@

EXTRA_PERF_CSVS := $(KINDS:%=perf-%.csv)

.PHONY: perf-csv
perf-csv: perf.csv $(EXTRA_PERF_CSVS)

.PHONY: perf.csv
perf.csv:
	$(SHOW)'PYTHON3 aggregate.py -o $@'
	$(HIDE)$(PYTHON3) src/Rewriter/Rewriter/Examples/PerfTesting/aggregate.py -o $@ $(wildcard $(ALL_PERF_LOGS))

$(EXTRA_PERF_CSVS) : perf-%.csv : perf.csv
	$(PYTHON3) src/Rewriter/Rewriter/Examples/PerfTesting/process.py -o $@ $* $<
## End Perf-testing section
##########################################
