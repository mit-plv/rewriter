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
	sed 's?@META@?$(META_FILE_FRAGMENT)?g' $< > $@

# This target is used to update the _CoqProject file.
# But it only works if we have git
ifneq (,$(wildcard .git/))
SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
EXISTING_COQPROJECT_CONTENTS_SORTED:=$(shell cat _CoqProject.in 2>&1 | $(SORT_COQPROJECT))
WARNINGS_PLUS := +implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+undeclared-scope,+deprecated-typeclasses-transparency-without-locality,+future-coercion-class-field
WARNINGS := $(WARNINGS_PLUS),unsupported-attributes
COQPROJECT_CMD:=(echo @META@; echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-I $(PLUGINS_DIR)'; echo '-arg -w -arg $(WARNINGS)'; echo '-arg -native-compiler -arg ondemand'; (git ls-files '$(SRC_DIR)/*.v' '$(SRC_DIR)/*.mlg' '$(SRC_DIR)/*.mllib' '$(SRC_DIR)/*.ml' '$(SRC_DIR)/*.mli' | $(SORT_COQPROJECT)); (echo '$(COMPATIBILITY_FILES)' | tr ' ' '\n'))
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

# We must work around COQBUG(https://github.com/coq/coq/issues/10907) and fix the conf target
Makefile.coq Makefile-old.conf: Makefile _CoqProject $(COQ_VERSION_FILE)
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > Makefile.coq'
	$(HIDE)(($(COQBIN)coq_makefile -f _CoqProject -o Makefile-old && cat Makefile-old | sed s'/Makefile-old.conf:/Makefile-old-old.conf:/g' | sed 's/Makefile-old.local/Makefile.local/g; s/^-\?include Makefile.local-late$$//g' $(EXTRA_SED_FOR_DEPS)); echo; echo 'include Makefile.local-late') > Makefile.coq && rm Makefile-old

Makefile.coq: | Makefile-old.conf

clean::
	rm -f Makefile.coq
