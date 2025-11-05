
all: pdl bml

.PHONY: all pdl bml doc

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

PDL_LEAN_FILES := $(wildcard Pdl/*.lean)

BASE = https://m4lvin.github.io/lean4-pdl/docs/Pdl/

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
