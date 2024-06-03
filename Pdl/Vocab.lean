import Pdl.Syntax

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union

mutual
  def vocabOfProgram : Program → Finset Nat
    | ·c => {c}
    | α;'β => vocabOfProgram α ∪ vocabOfProgram β
    | α ⋓ β => vocabOfProgram α ∪ vocabOfProgram β
    | ∗α => vocabOfProgram α
    | ?' φ => vocabOfFormula φ
  def vocabOfFormula : Formula → Finset Nat
    | ⊥ => ∅
    | ·c => {c}
    | ~φ => vocabOfFormula φ
    | φ⋀ψ => vocabOfFormula φ ∪ vocabOfFormula ψ
    | ⌈α⌉ φ => vocabOfProgram α ∪ vocabOfFormula φ
end

def vocabOfSetFormula : Finset Formula → Finset Nat
  | X => X.biUnion vocabOfFormula

def vocabOfListFormula : List Formula → Finset Nat
  | X => (X.toFinset).biUnion vocabOfFormula

def vocabOfListProgram : List Program → Finset Nat
  | X => (X.toFinset).biUnion vocabOfProgram

theorem inVocList : ℓ ∈ vocabOfListFormula L ↔ ∃φ ∈ L, ℓ ∈ vocabOfFormula φ := by
  simp only [vocabOfListFormula, Finset.mem_biUnion, List.mem_toFinset]

class HasVocabulary (α : Type) where
  voc : α → Finset Nat

instance formulaHasVocabulary : HasVocabulary Formula := ⟨vocabOfFormula⟩
instance programHasVocabulary : HasVocabulary Program := ⟨vocabOfProgram⟩
instance finsetFormulaHasVocabulary : HasVocabulary (Finset Formula) := ⟨vocabOfSetFormula⟩
instance listFormulaHasVocabulary : HasVocabulary (List Formula) := ⟨vocabOfListFormula⟩
instance listProgramHasVocabulary : HasVocabulary (List Program) := ⟨vocabOfListProgram⟩

/-- Tests(α) -/
def testsOfProgram : Program → List Formula
| ·_ => ∅
| ?' τ => [τ] -- no sub-tests etc. needed?
| α;'β => testsOfProgram α ++ testsOfProgram β
| α ⋓ β => testsOfProgram α ++ testsOfProgram β
| ∗α => testsOfProgram α
-- IDEA ? def testsOfFormula : Formula → Finset Formula
-- class HasTests (α : Type) where testsOf : α  → Finset Formula

/-- Progs(α) -/
def subprograms : Program → List Program
| ·a => [(·a : Program)]
| ?' φ => [?' φ]
| α;'β => [α;'β ] ++ subprograms α ++ subprograms β
| α ⋓ β => [α ⋓ β] ++ subprograms α ++ subprograms β
| ∗α => [∗α] ++ subprograms α
