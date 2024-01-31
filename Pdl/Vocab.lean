import Pdl.Syntax

import Mathlib.Data.Finset.Basic

mutual
  def vocabOfProgram : Program → Finset Char
    | ·c => {c}
    | α;'β => vocabOfProgram α ∪ vocabOfProgram β
    | Program.union α β => vocabOfProgram α ∪ vocabOfProgram β
    | ∗α => vocabOfProgram α
    | ?' φ => vocabOfFormula φ
  def vocabOfFormula : Formula → Finset Char
    | ⊥ => ∅
    | ·c => {c}
    | ~φ => vocabOfFormula φ
    | φ⋀ψ => vocabOfFormula φ ∪ vocabOfFormula ψ
    | ⌈α⌉ φ => vocabOfProgram α ∪ vocabOfFormula φ
end

def vocabOfSetFormula : Finset Formula → Finset Char
  | X => X.biUnion vocabOfFormula

def vocabOfListFormula : List Formula → Finset Char := λX =>
  X.foldl (λV φ => V ∪ vocabOfFormula φ ) ∅

theorem inVocList : ℓ ∈ vocabOfListFormula L ↔ ∃φ ∈ L, ℓ ∈ vocabOfFormula φ := by sorry

class HasVocabulary (α : Type) where
  voc : α → Finset Char

instance formulaHasVocabulary : HasVocabulary Formula := ⟨vocabOfFormula⟩
instance programHasVocabulary : HasVocabulary Program := ⟨vocabOfProgram⟩
instance finsetFormulaHasVocabulary : HasVocabulary (Finset Formula) := ⟨vocabOfSetFormula⟩
instance listFormulaHasVocabulary : HasVocabulary (List Formula) := ⟨vocabOfListFormula⟩
