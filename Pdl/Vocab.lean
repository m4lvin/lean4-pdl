import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Fold

import Pdl.Syntax

/-! # Syntax (Section 2.1) -/

abbrev Vocab := Finset (Sum Nat Nat)

def Vocab.atomProps : Vocab → Finset Nat :=
  fun X => X.biUnion (fun x => match x with | Sum.inl n => {n} | Sum.inr _ => {} )

def Vocab.atomProgs : Vocab → Finset Nat :=
  fun X => X.biUnion (fun x => match x with | Sum.inl _ => {} | Sum.inr n => {n} )

mutual
  @[simp]
  def Program.voc : Program → Vocab
    | ·n => {.inr n}
    | α;'β => α.voc ∪ β.voc
    | α ⋓ β => α.voc ∪ β.voc
    | ∗α => α.voc
    | ?' φ => φ.voc
  @[simp]
  def Formula.voc : Formula → Vocab
    | ⊥ => ∅
    | ·n => {.inl n}
    | ~φ => φ.voc
    | φ⋀ψ => φ.voc ∪ ψ.voc
    | ⌈α⌉ φ => α.voc ∪ φ.voc
end

-- rename to Vocab.join? or use `class Hadd`?
-- QUESTION: Is there a List.flatten but for Finset?
@[simp]
def Vocab.fromList : (L : List Vocab) → Vocab
| [] => {}
| (v::vs) => v ∪ Vocab.fromList vs

@[simp]
abbrev List.fvoc (L : List Formula) := Vocab.fromList (L.map Formula.voc)

@[simp]
abbrev List.pvoc (L : List Program) := Vocab.fromList (L.map Program.voc)

@[simp]
theorem Vocab.fromList_singleton : Vocab.fromList [V] = V := by
  simp [Vocab.fromList]

@[simp]
theorem Vocab.fromList_append : Vocab.fromList (L ++ R) = Vocab.fromList L ∪ Vocab.fromList R := by
  induction L <;> induction R <;> simp_all

theorem Vocab.fromListFormula_map_iff n (L : List Formula) :
    n ∈ Vocab.fromList (L.map Formula.voc)
    ↔ ∃ φ ∈ L, n ∈ Formula.voc φ := by
  induction L
  · simp [fromList]
  case cons h t IH =>
    simp only [List.map_cons, fromList, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [← IH]

theorem Vocab.fromListProgram_map_iff n (L : List Program) :
    n ∈ Vocab.fromList (L.map vocabOfProgram)
    ↔ ∃ α ∈ L, n ∈ vocabOfProgram α := by
  induction L
  · simp [fromList]
  case cons h t IH =>
    simp only [List.map_cons, fromList, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [← IH]

theorem Formula.voc_boxes : (⌈⌈δ⌉⌉φ).voc = δ.pvoc ∪ φ.voc := by
  induction δ
  · simp
  case cons α δ IH =>
    simp only [List.map_cons, List.pvoc, voc, Vocab.fromList, Finset.union_assoc] at *
    rw [← IH]
    rfl

@[simp]
def LoadFormula.voc (lf : LoadFormula) : Vocab := (unload lf).voc

@[simp]
def NegLoadFormula.voc (nlf : NegLoadFormula) : Vocab := (negUnload nlf).voc

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

@[simp]
theorem subprograms.refl : α ∈ subprograms α := by
  cases α <;> simp [subprograms]

theorem testsOfProgram.voc α {τ} (τ_in : τ ∈ testsOfProgram α) : τ.voc ⊆ α.voc := by
  cases α <;> simp_all [testsOfProgram]
  case sequence α β =>
    intro x x_in
    rcases τ_in with hyp | hyp
    all_goals
      have := testsOfProgram.voc _ hyp
      specialize this x_in
      simp only [Finset.mem_union]
      tauto
  case union α β =>
    intro x x_in
    rcases τ_in with hyp | hyp
    all_goals
      have := testsOfProgram.voc _ hyp
      specialize this x_in
      simp only [Finset.mem_union]
      tauto
  case star α =>
    intro x x_in
    have := testsOfProgram.voc _ τ_in
    exact this x_in
