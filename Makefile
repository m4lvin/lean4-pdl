
all: pdl bml

pdl: .first-run-done
	lake build Pdl

bml: .first-run-done
	lake build Bml

# https://leanprover-community.github.io/install/project.html#creating-a-lean-project
.first-run-done:
	lake exe cache get
	touch .first-run-done

clean:
	rm -rf .first-run-done lake-packages .lake build lakefile.olean


# From https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Invalid.20lake.20configuration/near/405630149
update-fix:
	cp .lake/packages/mathlib/lean-toolchain .
	lake update -R
