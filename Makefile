# Adapted from https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile

# Main .v files for default target
MAIN_VFILES := $(wildcard linear_pi*.v)

# Output of main .v files
MAIN_OUT := $(patsubst %.v,%.vo,$(MAIN_VFILES))

# All .v files in project
VFILES := $(wildcard *.v)

GLOBFILES := $(patsubst %.v,%.glob,$(VFILES))

# Documentation files
# HTML_FILES := $(patsubst %.v,RC3.%.html,$(VFILES))

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile main-files coq2html
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

# # This rule builds only the main files
# main-files: $(MAIN_OUT)
# 	@ echo Making main files: $^

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile $(VFILES)

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES) main-files coq2html clean

####################################################################
##                      Your targets here                         ##
####################################################################

coq2html:
	coq2html -base SR $(VFILES) $(GLOBFILES)

clean: invoke-coqmakefile
	rm -f SR.*.html

TAGS: $(VFILES)
	.util/coqtags $^

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
