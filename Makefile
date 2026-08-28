
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

dependencies.svg: scripts/venv scripts/dependencies_v1.py Pdl/**/*.lean
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
