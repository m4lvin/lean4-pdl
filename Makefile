
all: pdl bml

.PHONY: all pdl bml doc show-doc clean delete-unused-oleans check stats

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

OLEAN_DIRS = .lake/build/lib/lean/Pdl .lake/build/lib/lean/Bml
OLEANS = $(shell find $(OLEAN_DIRS) -name "*.olean" 2>/dev/null)

delete-unused-oleans:
	@for olean in $(OLEANS); do \
		lean_src=$$(echo "$$olean" | sed 's|^\.lake/build/lib/lean/||' | sed 's|\.olean$$|.lean|'); \
		if [ ! -f "./$$lean_src" ]; then \
			echo "Deleting $$olean"; \
			rm -f "$$olean"; \
		fi \
	done
	@echo "Deleted unused .olean files."

check: pdl bml delete-unused-oleans
	lake env leanchecker Pdl
	lake env leanchecker Bml

# Dependency Graph

dependencies.svg dependencies.png: scripts/venv scripts/dependencies_v1.py Pdl/**/*.lean
	scripts/venv/bin/python3 scripts/dependencies_v1.py

scripts/venv:
	mkdir -p build
	python -m venv scripts/venv
	scripts/venv/bin/pip install graphviz

# Update top-level file

Pdl.lean: Pdl/**/*.lean
	cat Pdl.lean | grep -v "import Pdl" > footer.lean
	find Pdl -type f | sed "s/Pdl\//import\ Pdl\./" | sed "s/\//\./g" | sed "s/\.lean//" | sort  | sort > Pdl.lean
	cat footer.lean >> Pdl.lean
	rm footer.lean

# Count lines

SHELL:=/bin/bash -O globstar

stats:
	wc -l Pdl/**/*.lean
