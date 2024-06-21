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

@[simp]
def Vocab.union (a : Vocab) (b : Vocab) : Vocab := ⟨a.1 ∪ b.1, a.2 ∪ b.2⟩

instance : Std.Commutative Vocab.union := sorry

instance : Std.Associative Vocab.union := sorry

instance : Union Vocab := ⟨Vocab.union⟩

@[simp]
instance : EmptyCollection Vocab := ⟨ ⟨{}, {}⟩ ⟩

@[simp]
instance : Membership ℕ Vocab := ⟨fun n v => n ∈ v.1 ∨ n ∈ v.2⟩

@[simp]
def Vocab.fromList (l : List Vocab) : Vocab := l.foldr (.union) {}

@[simp]
def Vocab.fromFinset (X : Finset Vocab) : Vocab := X.fold (Vocab.union) {} id

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

@[simp]
theorem Vocab.props_dist {X Y : Vocab} : (X ∪ Y).props = X.props ∪ Y.props := by sorry

@[simp]
theorem Vocab.progs_dist {X Y : Vocab} : (X ∪ Y).progs = X.progs ∪ Y.progs := by sorry

def vocabOfSetFormula : Finset Formula → Vocab
  | X => .fromFinset (X.biUnion (fun f => {vocabOfFormula f}))

def vocabOfListFormula : List Formula → Vocab
  | X => .fromList (X.map vocabOfFormula)

def vocabOfListProgram : List Program → Vocab
  | X => .fromList (X.map vocabOfProgram)

@[simp]
theorem inVocList : n ∈ vocabOfListFormula L ↔ ∃φ ∈ L, n ∈ vocabOfFormula φ := by
  induction L
  · simp [vocabOfListFormula]
  case cons φ L IH =>
    cases em (n ∈ vocabOfFormula φ) <;> simp_all [vocabOfListFormula]
    sorry

class HasVocabulary (α : Type) where
  voc : α → Vocab

instance formulaHasVocabulary : HasVocabulary Formula := ⟨vocabOfFormula⟩
instance programHasVocabulary : HasVocabulary Program := ⟨vocabOfProgram⟩
instance finsetFormulaHasVocabulary : HasVocabulary (Finset Formula) := ⟨vocabOfSetFormula⟩
instance listFormulaHasVocabulary : HasVocabulary (List Formula) := ⟨vocabOfListFormula⟩
instance listProgramHasVocabulary : HasVocabulary (List Program) := ⟨vocabOfListProgram⟩

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
