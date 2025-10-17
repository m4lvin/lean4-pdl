import Pdl.FischerLadner
import Pdl.Sequent

-- Quick reminder how ≤ and ⊆ work on multisets.
example : ¬ {2,2,1} ≤ ({1,2} : Multiset Nat) := by decide -- cares about multiplicity
example :   {2,2,1} ⊆ ({1,2} : Multiset Nat) := by simp_all -- set-like / only cares about support

/-- `X` is a component-wise *multi*subset of the FL-closure of `Y`.
Implies `Sequent.subseteq_FL` but not vice versa, as infinitely many multisets yield the same set.

BROKEN - does not take into account X.O and Y.O on both sides.
Hopefully we will never need this anyway. Use `Sequent.subseteq_FL` instead. -/
def Sequent.multisubseteq_FL (X : Sequent) (Y : Sequent) : Prop :=
    Multiset.ofList X.R < Multiset.ofList (FLL Y.R)
  ∧ Multiset.ofList X.L < Multiset.ofList (FLL Y.L)
