import Pdl.Syntax

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Fold

abbrev Vocab := Finset (Sum Nat Nat)

def Vocab.atomProps : Vocab → Finset Nat :=
  fun X => X.biUnion (fun x => match x with | Sum.inl n => {n} | Sum.inr _ => {} )

def Vocab.atomProgs : Vocab → Finset Nat :=
  fun X => X.biUnion (fun x => match x with | Sum.inl _ => {} | Sum.inr n => {n} )

mutual
  def vocabOfProgram : Program → Vocab
    | ·n => {.inr n}
    | α;'β => vocabOfProgram α ∪ vocabOfProgram β
    | α ⋓ β => vocabOfProgram α ∪ vocabOfProgram β
    | ∗α => vocabOfProgram α
    | ?' φ => vocabOfFormula φ
  def vocabOfFormula : Formula → Vocab
    | ⊥ => ∅
    | ·n => {.inl n}
    | ~φ => vocabOfFormula φ
    | φ⋀ψ => vocabOfFormula φ ∪ vocabOfFormula ψ
    | ⌈α⌉ φ => vocabOfProgram α ∪ vocabOfFormula φ
end

class HasVocabulary (α : Type) where
  voc : α → Vocab

open HasVocabulary

instance formulaHasVocabulary : HasVocabulary Formula := ⟨vocabOfFormula⟩

instance programHasVocabulary : HasVocabulary Program := ⟨vocabOfProgram⟩

def Vocab.fromList : (L : List Vocab) → Vocab
| [] => {}
| (v::vs) => v ∪ Vocab.fromList vs

instance [HasVocabulary α] : HasVocabulary (List α) :=
  ⟨fun X => .fromList (X.map voc)⟩

instance [HasVocabulary α] : HasVocabulary (Finset α) :=
  ⟨fun X => (X.biUnion (fun f => {voc f})).fold (fun x y => x ∪ y) {} id⟩

theorem Vocab.fromListFormula_map_iff n (L : List Formula): n ∈ Vocab.fromList (L.map vocabOfFormula) ↔ ∃ φ ∈ L, n ∈ vocabOfFormula φ := by
  induction L
  · simp [fromList]
  case cons h t IH =>
    simp only [fromList, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [← IH]

theorem Vocab.fromListProgram_map_iff n (L : List Program): n ∈ Vocab.fromList (L.map vocabOfProgram) ↔ ∃ α ∈ L, n ∈ vocabOfProgram α := by
  induction L
  · simp [fromList]
  case cons h t IH =>
    simp only [fromList, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [← IH]

theorem inVocList {α} [HasVocabulary α] n (L : List α): n ∈ voc L ↔ ∃ φ ∈ L, n ∈ voc φ := by
  induction L
  · simp [voc, Finset.mem_biUnion, List.mem_toFinset, Vocab.fromList]
  case cons h t IH =>
    simp only [voc, Vocab.fromList, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [← IH]
    simp only [voc]

/-- Test(α) -/
def testsOfProgram : Program → List Formula
| ·_ => []
| ?' τ => [τ] -- no sub-tests etc. needed?
| α;'β => testsOfProgram α ++ testsOfProgram β
| α ⋓ β => testsOfProgram α ++ testsOfProgram β
| ∗α => testsOfProgram α

/-- Prog(α) -/
def subprograms : Program → List Program
| ·a => [(·a : Program)]
| ?' φ => [?' φ]
| α;'β => [α;'β ] ++ subprograms α ++ subprograms β
| α ⋓ β => [α ⋓ β] ++ subprograms α ++ subprograms β
| ∗α => [∗α] ++ subprograms α
