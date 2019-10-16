.SUFFIXES:

MOD_NAME:=Rewriter
SRC_DIR:=src/Rewriter
PLUGINS_DIR:=$(SRC_DIR)/Util/plugins

_COQPROJECT_NAME?=_CoqProject
UPDATE_COQPROJECT_TARGET?=update-_CoqProject
_COQPROJECT_EXCLUDED_VFILES?=

FAST_TARGETS += archclean clean cleanall printenv clean-old $(UPDATE_COQPROJECT_TARGET) Makefile.coq
SUPER_FAST_TARGETS += $(UPDATE_COQPROJECT_TARGET) Makefile.coq

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

UPDATE_COQPROJECT = yes # always update _CoqProject, since we sometimes switch between ml4 and mlg
EXTRA_PIPE_SED_FOR_COQPROJECT = | sed s'/\.@ML4_OR_MLG@/.$(ML4_OR_MLG)/g'
DONT_USE_ADMIT_AXIOM = 1

COMPATIBILITY_FILE:=$(SRC_DIR)/Util/Compat.v

include etc/coq-scripts/compatibility/Makefile.coq.compat_84_85-early

ifneq (,$(filter 8.9%,$(COQ_VERSION)))
EXPECTED_EXT:=.v89
ML_DESCRIPTION := "Coq v8.9"
ML4_OR_MLG := ml4
else
ifneq (,$(filter 8.10%,$(COQ_VERSION)))
EXPECTED_EXT:=.v810
ML_DESCRIPTION := "Coq v8.10"
ML4_OR_MLG := mlg
else
ifneq (,$(filter 8.11%,$(COQ_VERSION)))
EXPECTED_EXT:=.v811
ML_DESCRIPTION := "Coq v8.11"
ML4_OR_MLG := mlg
else
ifdef COQ_VERSION # if not, we're just going to remake the relevant Makefile to include anyway, so we shouldn't error
$(error Unrecognized Coq version $(COQ_VERSION))
endif
endif
endif
endif

IS_FAST := 1
IS_SUPER_FAST := 1

ifeq ($(MAKECMDGOALS),)
IS_FAST := 0
IS_SUPER_FAST := 0
endif

ifneq ($(filter-out $(SUPER_FAST_TARGETS) $(FAST_TARGETS),$(MAKECMDGOALS)),)
IS_FAST := 0
endif

ifneq ($(filter-out $(SUPER_FAST_TARGETS),$(MAKECMDGOALS)),)
IS_SUPER_FAST := 0
endif

ifneq ($(IS_SUPER_FAST),1)
include Makefile.coq
endif

ML_COMPATIBILITY_FILES_PATTERN := \
	src/Rewriter/Util/plugins/definition_by_tactic.ml \
	src/Rewriter/Util/plugins/definition_by_tactic.mli \
	src/Rewriter/Util/plugins/definition_by_tactic_plugin.@ML4_OR_MLG@ \
	src/Rewriter/Util/plugins/definition_by_tactic_plugin.mllib \
	src/Rewriter/Util/plugins/inductive_from_elim.ml \
	src/Rewriter/Util/plugins/inductive_from_elim.mli \
	src/Rewriter/Util/plugins/inductive_from_elim_plugin.@ML4_OR_MLG@ \
	src/Rewriter/Util/plugins/inductive_from_elim_plugin.mllib \
	src/Rewriter/Util/plugins/rewriter_build.ml \
	src/Rewriter/Util/plugins/rewriter_build.mli \
	src/Rewriter/Util/plugins/rewriter_build_plugin.@ML4_OR_MLG@ \
	src/Rewriter/Util/plugins/rewriter_build_plugin.mllib \
	src/Rewriter/Util/plugins/strategy_tactic.ml \
	src/Rewriter/Util/plugins/strategy_tactic.mli \
	src/Rewriter/Util/plugins/strategy_tactic_plugin.@ML4_OR_MLG@ \
	src/Rewriter/Util/plugins/strategy_tactic_plugin.mllib

ML_COMPATIBILITY_FILES := $(subst @ML4_OR_MLG@,$(ML4_OR_MLG),$(ML_COMPATIBILITY_FILES_PATTERN))

include etc/coq-scripts/compatibility/Makefile.coq.compat_84_85

# This target is used to update the _CoqProject.in file.
SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
$(UPDATE_COQPROJECT_TARGET):
	$(SHOW)'ECHO > _CoqProject.in'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-I $(PLUGINS_DIR)'; (git ls-files '$(SRC_DIR)/*.v' '$(SRC_DIR)/*.mlg' '$(SRC_DIR)/*.mllib' '$(SRC_DIR)/*.ml' '$(SRC_DIR)/*.mli' | $(SORT_COQPROJECT)); (echo '$(ML_COMPATIBILITY_FILES_PATTERN)' | tr ' ' '\n')) > _CoqProject.in

ifeq ($(IS_FAST),0)
# see http://stackoverflow.com/a/9691619/377022 for why we need $(eval $(call ...))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/definition_by_tactic.ml,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/definition_by_tactic.mli,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/definition_by_tactic_plugin.$(ML4_OR_MLG),$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/definition_by_tactic_plugin.mllib,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/inductive_from_elim.ml,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/inductive_from_elim.mli,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/inductive_from_elim_plugin.$(ML4_OR_MLG),$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/inductive_from_elim_plugin.mllib,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/rewriter_build.ml,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/rewriter_build.mli,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/rewriter_build_plugin.$(ML4_OR_MLG),$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/rewriter_build_plugin.mllib,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/strategy_tactic.ml,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/strategy_tactic.mli,$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/strategy_tactic_plugin.$(ML4_OR_MLG),$(EXPECTED_EXT)))
$(eval $(call SET_ML_COMPATIBILITY,src/Rewriter/Util/plugins/strategy_tactic_plugin.mllib,$(EXPECTED_EXT)))
endif


.DEFAULT_GOAL := all

# Remove -undeclared-scope once we stop supporting 8.9
OTHERFLAGS += -w -notation-overridden,-undeclared-scope,+implicit-core-hint-db,+implicits-in-term
ifneq ($(PROFILE),)
OTHERFLAGS += -profile-ltac
endif

export OTHERFLAGS

# Note that the OTHERFLAGS bit is to work around COQBUG(https://github.com/coq/coq/issues/10905)
Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject -o Makefile-old && cat Makefile-old | sed s'/OTHERFLAGS        :=/OTHERFLAGS        ?=/g' > $@ && rm Makefile-old

clean::
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
