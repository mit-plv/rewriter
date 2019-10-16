.SUFFIXES:

MOD_NAME:=Rewriter
SRC_DIR:=src/Rewriter
PLUGINS_DIR:=$(SRC_DIR)/Util/plugins

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

STRICT_DEPS?=

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
NEW_COQPROJECT_CONTENTS:=$(shell echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-I $(PLUGINS_DIR)'; (git ls-files '$(SRC_DIR)/*.v' '$(SRC_DIR)/*.mlg' '$(SRC_DIR)/*.mllib' '$(SRC_DIR)/*.ml' '$(SRC_DIR)/*.mli' | $(SORT_COQPROJECT)); (echo '$(ML_COMPATIBILITY_FILES)' | tr ' ' '\n'))

ifneq ($(EXISTING_COQPROJECT_CONTENTS),$(NEW_COQPROJECT_CONTENTS))
.PHONY: _CoqProject
_CoqProject:
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)echo '$(NEW_COQPROJECT_CONTENTS)' > $@
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

clean::
	rm -f Makefile.coq
