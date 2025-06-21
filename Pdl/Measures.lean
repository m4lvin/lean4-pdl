import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Basic

import Pdl.Syntax

/-! # Measures -/

mutual
  @[simp]
  def lengthOfProgram : Program → Nat
    | ·_ => 1
    | α;'β => 1 + lengthOfProgram α + lengthOfProgram β
    | α⋓β => 1 + lengthOfProgram α + lengthOfProgram β
    | ∗α => 1 + lengthOfProgram α
    | ?'φ => 2 + lengthOfFormula φ -- 2 not 1, to make F^ℓ go down ;-)
  @[simp]
  def lengthOfFormula : Formula → Nat
    | Formula.bottom => 1
    | ·_ => 1
    | ~φ => 1 + lengthOfFormula φ
    | φ⋀ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
    | ⌈α⌉φ => 1 + lengthOfProgram α + lengthOfFormula φ
end

lemma lengthOfProgram_gt_zero (α : Program) : 0 < lengthOfProgram α := by
  cases α <;> simp <;> omega

class HasLength (α : Type) where
  lengthOf : α → ℕ

open HasLength
@[simp]
instance formulaHasLength : HasLength Formula := ⟨lengthOfFormula⟩
@[simp]
instance setFormulaHasLength : HasLength (Finset Formula) := ⟨fun X => X.sum lengthOfFormula⟩
@[simp]
instance listFormulaHasLength : HasLength (List Formula) := ⟨fun X => (X.map lengthOfFormula).sum⟩
@[simp]
instance programHasLength : HasLength Program := ⟨lengthOfProgram⟩
@[simp]
instance setProgramHasLength : HasLength (Finset Program) := ⟨fun X => X.sum lengthOfProgram⟩
