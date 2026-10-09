# Principia — Lean course task runner.  Run `make` for help.
.DEFAULT_GOAL := help

help:  ## show this help
	@echo "Principia — commands:"
	@grep -E '^[a-z].*:.*##' $(MAKEFILE_LIST) | sed -E 's/:.*## /\t/' | awk -F'\t' '{printf "  make %-22s %s\n",$$1,$$2}'
	@echo
	@echo "  C=<dir> is a concept dir, e.g.  make lab C=00-foundations/00-setup"

setup:  ## build toolchain + the Principia library (run once)
	@lake build
	@echo "✓ Lean toolchain + Principia ready.  Next: make test"

build:  ## build the Principia library
	@lake build

test: build  ## build the library + kernel-check every Solution.lean (always GREEN)
	@set -e; \
	files=$$(find . \( -path ./.lake -o -path ./_TEMPLATE-concept \) -prune -o -name 'Solution.lean' -print); \
	if [ -z "$$files" ]; then echo "(no Solution.lean yet)"; else \
	  for f in $$files; do echo "  lean  $$f"; lake env lean "$$f"; done; fi; \
	echo "✓ all solutions kernel-certified"

lab: build  ## check required exercises + report optional progress: make lab C=<dir>
	@test -n "$(C)" || { echo "usage: make lab C=<concept-dir>  (e.g. 00-foundations/00-setup)"; exit 2; }
	@bash tooling/lab.sh "$(C)/Skeleton.lean"

reset:  ## reset exercises to sorry (backup saved); optional C=<dir> or DRY_RUN=1
	@python3 tooling/reset_exercises.py $(if $(C),--concept "$(C)",) $(if $(filter 1,$(DRY_RUN)),--dry-run,)

test-reset:  ## check the exercise reset tool on temporary copies
	@python3 -m unittest discover -s tooling -p 'test_reset_exercises.py'

axioms:  ## honesty audit: no stray sorry/axiom; no sorryAx in keystones
	@bash tooling/audit.sh

explainer:  ## render one lesson to HTML/PDF: make explainer C=<dir>
	@test -n "$(C)" || { echo "usage: make explainer C=<concept-dir>"; exit 2; }
	@quarto render "$(C)/explainer.qmd"

docs:  ## render all explainers
	@quarto render

preview:  ## live-preview the docs
	@quarto preview

clean:  ## remove Lean build artifacts
	@lake clean

.PHONY: help setup build test lab reset test-reset axioms explainer docs preview clean
