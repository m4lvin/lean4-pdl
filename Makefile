
all: pdl bml

.PHONY: all pdl bml doc show-doc clean delete-unused-oleans check update-fix

pdl: .first-run-done
	lake build Pdl

bml: .first-run-done
	lake build Bml

# https://leanprover-community.github.io/install/project.html#creating-a-lean-project
.first-run-done:
	lake exe cache get
	touch .first-run-done

doc:
	cd docbuild && lake -Kenv=dev build Pdl:docs
	cat docbuild/docs/additional.css >> docbuild/.lake/build/doc/style.css

show-doc: doc
	(sleep 2 && firefox http://127.0.0.1:8000/Pdl.html) &
	cd docbuild/.lake/build/doc && python -m http.server --bind 127.0.0.1

clean:
	rm -rf .first-run-done lake-packages .lake build lakefile.olean

# lean4checker

BASE = https://m4lvin.github.io/lean4-pdl/docs/Pdl/

OLEANS = $(wildcard .lake/build/lib/lean/Pdl/*.olean) $(wildcard .lake/build/lib/lean/Bml/*.olean)

delete-unused-oleans:
	@for olean in $(OLEANS); do \
		dir=$$(dirname $$olean); \
		base=$$(basename $$olean .olean); \
		lean=$$base.lean; \
		if [ "$$dir" = ".lake/build/lib/lean/Pdl" ] && [ ! -f ./Pdl/$$lean ]; then \
			echo "Deleting $$olean"; \
			rm -f $$olean; \
		elif [ "$$dir" = ".lake/build/lib/lean/Bml" ] && [ ! -f ./Bml/$$lean ]; then \
			echo "Deleting $$olean"; \
			rm -f $$olean; \
		fi \
	done
	@echo "Deleted unused .olean files."

check: pdl bml delete-unused-oleans
	rm -rf lean4checker
	chmod +x ./scripts/run_lean4checker.sh
	./scripts/run_lean4checker.sh

# Dependency Graph

PDL_LEAN_FILES := $(wildcard Pdl/*.lean)

dependencies.svg: dependencies.dot
	dot -Tsvg dependencies.dot > $@

dependencies.dot: $(PDL_LEAN_FILES)
	@echo "digraph {" > $@
	@$(foreach file, $^ ,\
		if grep -q "sorry" "$(file)"; then \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))?\", color="red", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		else \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))✓\", color="green", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		fi;)
	@(grep -nr "import Pdl" Pdl/*.lean | awk -F '[./]' '{print $$4 " -> " $$2}') >> $@
	@echo "}" >> $@

update-fix:
	rm -rf .lake
	echo "leanprover/lean4:v4.23.0-rc2" > lean-toolchain
	echo "If next command fails, edit lakefile.lean manually."
	grep v4.22.0-rc2 lakefile.lean
	lake update -R
