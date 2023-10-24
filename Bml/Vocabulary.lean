-- VOCABULARY
import Tactic.NormNum
import Syntax
import Setsimp

#align_import vocabulary

def vocabOfFormula : Formula → Finset Char
  | ⊥ => Set.toFinset { }
  | ·c => {c}
  | ~φ => vocabOfFormula φ
  | φ⋏ψ => vocabOfFormula φ ∪ vocabOfFormula ψ
  | □φ => vocabOfFormula φ
#align vocabOfFormula vocabOfFormula

def vocabOfSetFormula : Finset Formula → Finset Char
  | X => Finset.biUnion X vocabOfFormula
#align vocabOfSetFormula vocabOfSetFormula

class HasVocabulary (α : Type) where
  voc : α → Finset Char
#align hasVocabulary HasVocabulary

open HasVocabulary

instance formulaHasVocabulary : HasVocabulary Formula :=
  HasVocabulary.mk vocabOfFormula
#align formula_hasVocabulary formulaHasVocabulary

instance setFormulaHasVocabulary : HasVocabulary (Finset Formula) :=
  HasVocabulary.mk vocabOfSetFormula
#align setFormula_hasVocabulary setFormulaHasVocabulary

@[simp]
theorem vocOfNeg {ϕ} : vocabOfFormula (~ϕ) = vocabOfFormula ϕ := by constructor
#align vocOfNeg vocOfNeg

theorem vocElem_subs_vocSet {ϕ X} : ϕ ∈ X → vocabOfFormula ϕ ⊆ vocabOfSetFormula X :=
  by
  apply Finset.induction_on X
  -- case ∅:
  intro phi_in_X;
  cases phi_in_X
  -- case insert:
  intro ψ S psi_not_in_S IH psi_in_insert
  unfold vocabOfSetFormula at *
  simp
  intro a aIn
  simp at *
  cases psi_in_insert
  · subst psi_in_insert; left; exact aIn
  · tauto
#align vocElem_subs_vocSet vocElem_subs_vocSet

theorem vocMonotone {X Y : Finset Formula} (hyp : X ⊆ Y) : voc X ⊆ voc Y :=
  by
  unfold voc; unfold vocabOfSetFormula at *
  intro a aIn
  unfold Finset.biUnion at *
  simp at *
  tauto
#align vocMonotone vocMonotone

theorem vocErase {X : Finset Formula} {ϕ : Formula} : voc (X \ {ϕ}) ⊆ voc X :=
  by
  apply vocMonotone
  rw [sdiff_singleton_is_erase]
  intro a aIn
  exact Finset.mem_of_mem_erase aIn
#align vocErase vocErase

theorem vocUnion {X Y : Finset Formula} : voc (X ∪ Y) = voc X ∪ voc Y :=
  by
  unfold voc vocabOfSetFormula
  ext1
  simp
  constructor <;> · intro; finish
#align vocUnion vocUnion

theorem vocPreserved (X : Finset Formula) (ψ ϕ) :
    ψ ∈ X → voc ϕ = voc ψ → voc X = voc (X \ {ψ} ∪ {ϕ}) :=
  by
  intro psi_in_X eq_voc
  unfold voc at *
  unfold vocabOfSetFormula
  ext1
  constructor
  all_goals intro a_in; norm_num at *
  · rcases a_in with ⟨θ, _, a_in_vocTheta⟩
    by_cases h : θ = ψ
    · left; rw [eq_voc]; rw [← h]; exact a_in_vocTheta
    · right; use θ; tauto
  · cases a_in
    · use ψ; rw [← eq_voc]; tauto
    · rcases a_in with ⟨θ, _, a_in_vocTheta⟩; use θ; tauto
#align vocPreserved vocPreserved

theorem vocPreservedTwo {X : Finset Formula} (ψ ϕ1 ϕ2) :
    ψ ∈ X → voc ({ϕ1, ϕ2} : Finset Formula) = voc ψ → voc X = voc (X \ {ψ} ∪ {ϕ1, ϕ2}) :=
  by
  intro psi_in_X eq_voc
  rw [vocUnion]
  unfold voc at *
  unfold vocabOfSetFormula
  ext1
  constructor
  all_goals intro a_in; norm_num at *
  · rcases a_in with ⟨θ, theta_in_X, a_in_vocTheta⟩
    by_cases h : θ = ψ
    · right; subst h; unfold vocabOfSetFormula vocabOfFormula at *; simp at *;
      rw [← eq_voc] at a_in_vocTheta ; simp at a_in_vocTheta ; tauto
    · use θ; itauto
  cases a_in
  · rcases a_in with ⟨θ, theta_in_X, a_in_vocTheta⟩; use θ; itauto
  · use ψ; constructor; itauto; rw [← eq_voc]; unfold vocabOfSetFormula; simp; itauto
#align vocPreservedTwo vocPreservedTwo

theorem vocPreservedSub {X : Finset Formula} (ψ ϕ) :
    ψ ∈ X → voc ϕ ⊆ voc ψ → voc (X \ {ψ} ∪ {ϕ}) ⊆ voc X :=
  by
  intro psi_in_X sub_voc
  unfold voc at *
  unfold vocabOfSetFormula
  intro a a_in; norm_num at *
  cases a_in
  · use ψ; rw [Finset.subset_iff] at sub_voc ; tauto
  · rcases a_in with ⟨θ, _, a_in_vocTheta⟩; use θ; tauto
#align vocPreservedSub vocPreservedSub

