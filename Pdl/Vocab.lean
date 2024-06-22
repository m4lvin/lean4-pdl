import Pdl.Syntax

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Fold

/-- A vocabulary is a pair of
    1. a set of atomic propositions and
    2. a set of atomic programs. -/
structure Vocab where
  props : Finset Nat
  progs : Finset Nat
deriving DecidableEq

-- no simp here!
instance instMembershipNatVocab : Membership ℕ Vocab := ⟨fun n v => n ∈ v.1 ∨ n ∈ v.2⟩

@[simp]
def Vocab.union (a : Vocab) (b : Vocab) : Vocab := ⟨a.1 ∪ b.1, a.2 ∪ b.2⟩

instance : Std.Commutative Vocab.union := by constructor; aesop

instance : Std.Associative Vocab.union := by constructor; aesop

instance instUnionVocab : Union Vocab := ⟨Vocab.union⟩

@[simp]
instance : EmptyCollection Vocab := ⟨ ⟨{}, {}⟩ ⟩

class HasVocabulary (α : Type) where
  voc : α → Vocab

open HasVocabulary

mutual
  def vocabOfProgram : Program → Vocab
    | ·c => ⟨{c}, {}⟩
    | α;'β => vocabOfProgram α ∪ vocabOfProgram β
    | α ⋓ β => vocabOfProgram α ∪ vocabOfProgram β
    | ∗α => vocabOfProgram α
    | ?' φ => vocabOfFormula φ
  def vocabOfFormula : Formula → Vocab
    | ⊥ => {}
    | ·c => ⟨{c}, {}⟩
    | ~φ => vocabOfFormula φ
    | φ⋀ψ => vocabOfFormula φ ∪ vocabOfFormula ψ
    | ⌈α⌉ φ => vocabOfProgram α ∪ vocabOfFormula φ
end

instance formulaHasVocabulary : HasVocabulary Formula := ⟨vocabOfFormula⟩

instance programHasVocabulary : HasVocabulary Program := ⟨vocabOfProgram⟩

@[simp]
theorem Vocab.props_dist {X Y : Vocab} : (X ∪ Y).props = X.props ∪ Y.props := by
  ext a; simp [instUnionVocab]

@[simp]
theorem Vocab.progs_dist {X Y : Vocab} : (X ∪ Y).progs = X.progs ∪ Y.progs := by
  ext a; simp [instUnionVocab]

instance [HasVocabulary α] : HasVocabulary (List α) :=
  ⟨fun X => (X.map voc).foldr (.union) {}⟩

instance [HasVocabulary α] : HasVocabulary (Finset α) :=
  ⟨fun X => (X.biUnion (fun f => {voc f})).fold (Vocab.union) {} id ⟩

@[simp]
theorem inVocList [HasVocabulary α] {L : List α} : n ∈ voc L ↔ ∃ φ ∈ L, n ∈ voc φ := by
  induction L
  · simp [voc, instMembershipNatVocab]
  case cons φ L IH =>
    cases em (n ∈ voc φ) <;> simp_all [voc, instMembershipNatVocab ]
    aesop

@[simp]
theorem voc_mem_union [HasVocabulary α] n (x y : α) :
      n ∈ voc x ∪ voc y
    ↔ (n ∈ voc x ∨ n ∈ voc y) := by
  simp_all [voc, instMembershipNatVocab]
  tauto

@[simp]
theorem voc_not_mem_union [HasVocabulary α] {x y : α} :
      n ∉ voc x ∪ voc y
    ↔ (n ∉ voc x ∧ n ∉ voc y) := by
  simp_all [voc, instMembershipNatVocab]


@[simp]
theorem vocabOfFormula_mem_union n (x y : Formula) :
      n ∈ vocabOfFormula x ∪ vocabOfFormula y
    ↔ (n ∈ vocabOfFormula x ∨ n ∈ vocabOfFormula y) := by
  simp_all [instMembershipNatVocab]
  tauto

@[simp]
theorem vocabOfProgram_mem_union n (x y : Program) :
      n ∈ vocabOfProgram x ∪ vocabOfProgram y
    ↔ (n ∈ vocabOfProgram x ∨ n ∈ vocabOfProgram y) := by
  simp_all [instMembershipNatVocab]
  tauto

/-- Test(α) -/
def testsOfProgram : Program → List Formula
| ·_ => ∅
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
