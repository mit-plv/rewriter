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

.PHONY: clean

# Makefile.coq from Coq 8.9 is incompatible with Coq >= 8.10, so we invoke clean a different way, and force a remake of Makefile.coq
ifeq ($(MAKECMDGOALS),clean)
clean::
	$(MAKE) -B Makefile.coq
	$(MAKE) -f Makefile.coq clean
else
include Makefile.local.common
include Makefile.coq
endif

clean::
	rm -f _CoqProject Makefile.coq Makefile-old.conf $(COQ_VERSION_FILE)

ifneq ($(COQ_EXTENDED_VERSION),$(COQ_EXTENDED_VERSION_OLD))
$(COQ_VERSION_FILE)::
	$(SHOW)'echo $$COQ_VERSION_INFO ($(COQ_VERSION)) > $@'
	$(HIDE)echo "$(COQ_EXTENDED_VERSION)" > $@
endif

_CoqProject: _CoqProject.in
	sed s'/@ML4_OR_MLG@/$(ML4_OR_MLG)/g' $< > $@

# This target is used to update the _CoqProject file.
# But it only works if we have git
ifneq (,$(wildcard .git/))
SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
EXISTING_COQPROJECT_CONTENTS_SORTED:=$(shell cat _CoqProject.in 2>&1 | $(SORT_COQPROJECT))
WARNINGS := +implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+variable-collision,+unexpected-implicit-declaration
COQPROJECT_CMD:=(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-I $(PLUGINS_DIR)'; echo '-arg -w -arg $(WARNINGS)'; (git ls-files '$(SRC_DIR)/*.v' '$(SRC_DIR)/*.mlg' '$(SRC_DIR)/*.mllib' '$(SRC_DIR)/*.ml' '$(SRC_DIR)/*.mli' | $(SORT_COQPROJECT)); (echo '$(COMPATIBILITY_FILES_PATTERN)' | tr ' ' '\n'))
NEW_COQPROJECT_CONTENTS_SORTED:=$(shell $(COQPROJECT_CMD) | $(SORT_COQPROJECT))

ifneq ($(EXISTING_COQPROJECT_CONTENTS_SORTED),$(NEW_COQPROJECT_CONTENTS_SORTED))
.PHONY: _CoqProject.in
_CoqProject.in:
	$(SHOW)'ECHO > $@'
	$(HIDE)$(COQPROJECT_CMD) > $@
endif
endif


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
PERF_MAX_KB?=10000000 # 10 GB
PERF_MAX_SEC?=
TIMEOUT_CMD?=
TIMEOUT_SHOW?=
PERF_SET_LIMITS?=

ifneq (,$(NO_LIMIT_PERF))
ifneq (,$(PERF_MAX_SEC))
TIMEOUT_CMD:=$(PERF_MAX_SEC)
PERF_T_ARG:=-t $(PERF_MAX_SEC) # trailing space important
else
PERF_T_ARG:=
endif

# apparently ulimit -m doesn't work anymore https://superuser.com/a/1497437/59575 / https://thirld.com/blog/2012/02/09/things-to-remember-when-using-ulimit/
PERF_SET_LIMITS = ulimit -S -m $(PERF_MAX_KB); ulimit -S -v $(PERF_MAX_KB);
TIMEOUT_SHOW:=TIMEOUT -m $(PERF_MAX_KB) $(PERF_T_ARG)
endif

.PHONY: perf
perf: $(ALL_PERF_LOGS)

ifneq ($(EXTERNAL_PERF_DEPENDENCIES),1)
$(ALL_PERF_LOGS): src/Rewriter/Rewriter/Examples/PerfTesting/Harness.vo
endif

$(ALL_PERF_LOGS) : %.log : %.v
	$(SHOW)'$(TIMEOUT_SHOW)COQC $(<:src/Rewriter/Rewriter/Examples/PerfTesting/%.v=%) > LOG'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(PERF_SET_LIMITS) $(TIMER) $(TIMEOUT_CMD) $(COQC) $(COQDEBUG) $(TIMING_ARG) $(COQFLAGS) $(COQLIBS) $< && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok
	$(HIDE)mv -f $@.tmp $@

EXTRA_PERF_CSVS := $(KINDS:%=perf-%.csv)

.PHONY: perf-csv
perf-csv: perf.csv $(EXTRA_PERF_CSVS)

.PHONY: perf.csv
perf.csv:
	$(SHOW)'PYTHON3 aggregate.py -o $@'
	$(HIDE)$(PYTHON3) src/Rewriter/Rewriter/Examples/PerfTesting/aggregate.py -o $@ $(wildcard $(ALL_PERF_LOGS))

.PHONY: perf.m
perf.m:
	$(SHOW)'PYTHON3 aggregate.py -o $@'
	$(HIDE)$(PYTHON3) src/Rewriter/Rewriter/Examples/PerfTesting/aggregate.py --mathematica -o $@ $(wildcard $(ALL_PERF_LOGS))

$(EXTRA_PERF_CSVS) : perf-%.csv : perf.csv
	$(PYTHON3) src/Rewriter/Rewriter/Examples/PerfTesting/process.py --txts -o $@ $* $<
## End Perf-testing section
##########################################
