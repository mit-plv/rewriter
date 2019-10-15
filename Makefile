.SUFFIXES:

MOD_NAME := Rewriter
SRC_DIR  := src/Rewriter
PLUGINS_DIR := $(SRC_DIR)/Util/plugins

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

.PHONY: update-_CoqProject

-include Makefile.coq

.DEFAULT_GOAL := all

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-I $(PLUGINS_DIR)'; (git ls-files '$(SRC_DIR)/*.v' '$(SRC_DIR)/*.mlg' '$(SRC_DIR)/*.mllib' '$(SRC_DIR)/*.ml' '$(SRC_DIR)/*.mli' | $(SORT_COQPROJECT))) > _CoqProject

# Remove -undeclared-scope once we stop supporting 8.9
OTHERFLAGS += -w -notation-overridden,-undeclared-scope,+implicit-core-hint-db,+implicits-in-term
ifneq ($(PROFILE),)
OTHERFLAGS += -profile-ltac
endif

export OTHERFLAGS

Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)($(COQBIN)coq_makefile -f _CoqProject -o Makefile-old && cat Makefile-old | sed s'/OTHERFLAGS        :=/OTHERFLAGS        ?=/g' > $@) && rm Makefile-old

clean::
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
