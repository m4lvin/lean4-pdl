
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

clean:
	rm -rf .first-run-done lake-packages .lake build lakefile.olean

dependencies.svg: Pdl/*.lean
	(echo "digraph {"; (grep -nr "import Pdl" Pdl/*.lean | awk -F[./] '{print $$4 " -> " $$2}'); echo "}") | dot -Tsvg > dependencies.svg

update-fix:
	rm -rf .lake
	echo "leanprover/lean4:v4.16.0-rc2" > lean-toolchain
	echo "If next command fails, edit lakefile.lean manually."
	grep v4.16.0-rc2 lakefile.lean
	lake update -R
