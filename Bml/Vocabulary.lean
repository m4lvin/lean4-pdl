-- VOCABULARY

import Mathlib.Tactic.NormNum

import Bml.Syntax
import Bml.Setsimp

@[simp]
def vocabOfFormula : Formula → Finset Char
  | ⊥ => Set.toFinset { }
  | ·c => {c}
  | ~φ => vocabOfFormula φ
  | φ⋀ψ => vocabOfFormula φ ∪ vocabOfFormula ψ
  | □φ => vocabOfFormula φ

@[simp]
def vocabOfSetFormula : Finset Formula → Finset Char
  | X => Finset.biUnion X vocabOfFormula

class HasVocabulary (α : Type) where
  voc : α → Finset Char

open HasVocabulary

@[simp]
instance formulaHasVocabulary : HasVocabulary Formula :=
  HasVocabulary.mk vocabOfFormula

@[simp]
instance setFormulaHasVocabulary : HasVocabulary (Finset Formula) :=
  HasVocabulary.mk vocabOfSetFormula

@[simp]
theorem vocOfNeg {ϕ} : vocabOfFormula (~ϕ) = vocabOfFormula ϕ := by constructor

theorem vocElem_subs_vocSet {ϕ X} : ϕ ∈ X → vocabOfFormula ϕ ⊆ vocabOfSetFormula X :=
  by
  induction X using Finset.induction_on
  -- case ∅:
  case empty =>
    intro phi_in_X;
    cases phi_in_X
  case insert ψ S _ IH =>
    intro psi_in_insert
    simp at *
    intro a aIn
    aesop

theorem vocMonotone {X Y : Finset Formula} (hyp : X ⊆ Y) : voc X ⊆ voc Y :=
  by
  unfold voc
  simp at *
  intro a aIn
  unfold Finset.biUnion at *
  intro p pIn
  aesop

theorem vocErase {X : Finset Formula} {ϕ : Formula} : voc (X \ {ϕ}) ⊆ voc X :=
  by
  apply vocMonotone
  rw [sdiff_singleton_is_erase]
  intro a aIn
  exact Finset.mem_of_mem_erase aIn

theorem vocUnion {X Y : Finset Formula} : voc (X ∪ Y) = voc X ∪ voc Y :=
  by
  simp
  ext1
  aesop

theorem vocPreserved (X : Finset Formula) (ψ ϕ) :
    ψ ∈ X → voc ϕ = voc ψ → voc X = voc (X \ {ψ} ∪ {ϕ}) :=
  by
  intro psi_in_X eq_voc
  simp at *
  ext1
  constructor
  all_goals intro a_in
  all_goals norm_num at *
  · rcases a_in with ⟨θ, _, a_in_vocTheta⟩
    by_cases h : θ = ψ
    · aesop
    · aesop
  · aesop

theorem vocPreservedTwo {X : Finset Formula} (ψ ϕ1 ϕ2) :
    ψ ∈ X → voc ({ϕ1, ϕ2} : Finset Formula) = voc ψ → voc X = voc (X \ {ψ} ∪ {ϕ1, ϕ2}) :=
  by
  intro psi_in_X eq_voc
  rw [vocUnion]
  simp at *
  ext1
  constructor
  all_goals intro a_in; norm_num at *
  · rcases a_in with ⟨θ, theta_in_X, a_in_vocTheta⟩
    by_cases h : θ = ψ
    · right; subst h; unfold vocabOfSetFormula vocabOfFormula at *; simp at *;
      rw [← eq_voc] at a_in_vocTheta ; simp at a_in_vocTheta ; tauto
    · constructor
      · use θ
  cases a_in
  · aesop
  · use ψ; constructor
    · aesop
    · rw [← eq_voc]; simp; aesop

theorem vocPreservedSub {X : Finset Formula} (ψ ϕ) :
    ψ ∈ X → voc ϕ ⊆ voc ψ → voc (X \ {ψ} ∪ {ϕ}) ⊆ voc X :=
  by
  intro psi_in_X sub_voc
  simp at *
  intro a a_in; norm_num at *
  cases a_in
  · use ψ; rw [Finset.subset_iff] at sub_voc ; tauto
  · aesop
