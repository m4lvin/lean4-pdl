
default: .first-run-done
	lake build

# https://leanprover-community.github.io/install/project.html#creating-a-lean-project
.first-run-done:
	lake exe cache get
	touch .first-run-done

clean:
	rm -rf .first-run-done lake-packages build lakefile.olean
