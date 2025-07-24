import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold

import Pdl.Syntax

/-! # Vocabulary (part of Section 2.1) -/

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
def Vocab.fromList (L : List Vocab) : Vocab := L.toFinset.sup id

@[simp]
abbrev List.fvoc (L : List Formula) := Vocab.fromList (L.map Formula.voc)

@[simp]
abbrev List.pvoc (L : List Program) := Vocab.fromList (L.map Program.voc)

@[simp]
theorem Vocab.fromList_append : Vocab.fromList (L ++ R) = Vocab.fromList L ∪ Vocab.fromList R := by
  induction L <;> induction R <;> simp_all

theorem Vocab.fromList_map_iff n (L : List α) f :
    n ∈ Vocab.fromList (L.map f)
    ↔ ∃ x ∈ L, n ∈ f x := by
  simp

theorem Vocab.fromListFormula_map_iff n (L : List Formula) :
    n ∈ Vocab.fromList (L.map Formula.voc)
    ↔ ∃ φ ∈ L, n ∈ Formula.voc φ := by apply fromList_map_iff

theorem Vocab.fromListProgram_map_iff n (L : List Program) :
    n ∈ Vocab.fromList (L.map vocabOfProgram)
    ↔ ∃ α ∈ L, n ∈ vocabOfProgram α := by
  simp

theorem Formula.voc_boxes : (⌈⌈δ⌉⌉φ).voc = δ.pvoc ∪ φ.voc := by
  induction δ <;> simp_all

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

lemma subprograms_voc {α β} : β ∈ subprograms α → β.voc ⊆ α.voc := by
  cases α <;> simp [subprograms, Program.voc]
  · simp_all
  case sequence α1 α2  =>
    rintro (β_def|β_in|β_in)
    · simp_all
    · have := @subprograms_voc α1 β; intro x x_in; aesop
    · have := @subprograms_voc α2 β; intro x x_in; aesop
  case union α1 α2  =>
    rintro (β_def|β_in|β_in)
    · simp_all
    · have := @subprograms_voc α1 β; intro x x_in; aesop
    · have := @subprograms_voc α2 β; intro x x_in; aesop
  case star α1  =>
    rintro (β_def|β_in)
    · simp_all
    · have := @subprograms_voc α1 β; intro x x_in; aesop
  · simp_all

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

/-! ## Fresh variables -/

mutual
  /-- Get a fresh atomic proposition `x` not occuring in `ψ`. -/
  def freshVarForm : Formula → Nat
    | ⊥ => 0
    | ·c => c + 1
    | ~φ => freshVarForm φ
    | φ1⋀φ2 => max (freshVarForm φ1) (freshVarForm φ2)
    | ⌈α⌉ φ => max (freshVarProg α) (freshVarForm φ)
  /-- Get a fresh atomic proposition `x` not occuring in `α`. -/
  def freshVarProg : Program → Nat
    | ·_ => 0 -- don't care!
    | α;'β  => max (freshVarProg α) (freshVarProg β)
    | α⋓β  =>  max (freshVarProg α) (freshVarProg β)
    | ∗α  => freshVarProg α
    | ?'φ  => freshVarForm φ
end

mutual
theorem freshVarForm_is_larger (φ) : ∀ n ∈ φ.voc.atomProps, n < freshVarForm φ := by
  cases φ
  all_goals simp [freshVarForm, Formula.voc, Vocab.atomProps]
  case neg φ =>
    have IH := freshVarForm_is_larger φ
    simp [Vocab.atomProps] at *
    assumption
  case and φ1 φ2 =>
    have IH1 := freshVarForm_is_larger φ1
    have IH2 := freshVarForm_is_larger φ2
    simp [Vocab.atomProps] at *
    aesop
  case box α φ =>
    have IHφ := freshVarForm_is_larger φ
    have IHα := freshVarProg_is_larger α
    simp [Vocab.atomProps] at *
    aesop

theorem freshVarProg_is_larger (α) : ∀ n ∈ α.voc.atomProps, n < freshVarProg α := by
  cases α
  all_goals simp [freshVarProg, Program.voc, Vocab.atomProps]
  case union α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp [Vocab.atomProps] at *
    aesop
  case sequence α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp [Vocab.atomProps] at *
    aesop
  case star α =>
    have IHα := freshVarProg_is_larger α
    simp [Vocab.atomProps] at *
    aesop
  case test φ =>
    have IHφ := freshVarForm_is_larger φ
    simp [Vocab.atomProps] at *
    aesop
end

theorem freshVarForm_is_fresh (φ) : Sum.inl (freshVarForm φ) ∉ φ.voc := by
  have := freshVarForm_is_larger φ
  simp [Vocab.atomProps] at *
  by_contra hyp
  specialize this (freshVarForm φ)
  have := Nat.lt_irrefl (freshVarForm φ)
  tauto

theorem freshVarProg_is_fresh (α) : Sum.inl (freshVarProg α) ∉ α.voc := by
  have := freshVarProg_is_larger α
  simp [Vocab.atomProps] at *
  by_contra hyp
  specialize this (freshVarProg α)
  have := Nat.lt_irrefl (freshVarProg α)
  tauto
