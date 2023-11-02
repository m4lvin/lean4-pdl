-- MEASURES

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic

import Pdl.Syntax

-- COMPLEXITY

mutual
  def lengthOfProgram : Program → Nat
    | ·_ => 1
    | α;'β => 1 + lengthOfProgram α + lengthOfProgram β
    | α⋓β => 1 + lengthOfProgram α + lengthOfProgram β
    | ∗α => 1 + lengthOfProgram α
    | ?'φ => 1 + lengthOfFormula φ
  def lengthOfFormula : Formula → Nat
    | Formula.bottom => 1
    | ·_ => 1
    | ~φ => 1 + lengthOfFormula φ
    | φ⋀ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
    | ⌈α⌉φ => 1 + lengthOfProgram α + lengthOfFormula φ
end
termination_by -- silly but needed?!
  lengthOfProgram p => sizeOf p
  lengthOfFormula f => sizeOf f

-- mwah
@[simp]
def lengthOfEither : PSum Program Formula → Nat
  | PSum.inl p => lengthOfProgram p
  | PSum.inr f => lengthOfFormula f

class HasLength (α : Type) where
  lengthOf : α → ℕ

open HasLength
@[simp]
instance formulaHasLength : HasLength Formula := ⟨lengthOfFormula⟩
@[simp]
instance setFormulaHasLength : HasLength (Finset Formula) := ⟨fun X => X.sum lengthOfFormula⟩

-- MEASURE
mutual
  @[simp]
  def mOfProgram : Program → Nat
    | ·_ => 0
    | ?'φ => 1 + mOfFormula φ
    | α;'β => 1 + mOfProgram α + mOfProgram β + 1 -- TODO: max (mOfFormula φ) (mOfFormula (~φ))
    | α⋓β => 1 + mOfProgram α + mOfProgram β + 1
    | ∗α => 1 + mOfProgram α
  @[simp]
  def mOfFormula : Formula → Nat
    | ⊥ => 0
    | ~⊥ => 0
    | ·_ => 0
    | ~·_ => 0
    | ~~φ => 1 + mOfFormula φ
    | φ⋀ψ => 1 + mOfFormula φ + mOfFormula ψ
    | ~φ⋀ψ => 1 + mOfFormula (~φ) + mOfFormula (~ψ)
    | ⌈α⌉ φ => mOfProgram α + mOfFormula φ
    | ~⌈α⌉ φ => mOfProgram α + mOfFormula (~φ)
end
termination_by -- silly but needed?!
  mOfProgram p => sizeOf p
  mOfFormula f => sizeOf f
