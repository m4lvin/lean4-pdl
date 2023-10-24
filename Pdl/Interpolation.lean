import Mathlib.Data.Finset.Basic

import Pdl.Syntax
import Pdl.Vocab
import Pdl.Semantics

open HasVocabulary vDash

def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  φ⊨θ ∧ θ⊨ψ ∧ voc θ ⊆ voc φ ∩ voc ψ

-- TODO: should set interpolation be defined using ⊨ or ⊢ or do we need both?
-- NOTE: this notion here is NOT (yet) equivalent to the one used by Borzechowski.
def SetInterpolant (X : Finset Formula) (Y : Finset Formula) (θ : Formula) :=
  X⊨θ ∧ θ⊨Y ∧ voc θ ⊆ voc X ∩ voc Y

theorem setInterpolation :
    ∀ (X : Finset Formula) (Y : Finset Formula), X⊨Y → ∃ θ : Formula, SetInterpolant X Y θ := by
  sorry

theorem interpolation : ∀ (φ : Formula) (ψ : Formula), φ⊨ψ → ∃ θ : Formula, Interpolant φ ψ θ :=
  by
  intro φ ψ hyp
  have haveInt := setInterpolation {φ} {ψ} (forms_to_sets hyp)
  cases' haveInt with θ haveInt_hyp
  use θ
  unfold SetInterpolant at haveInt_hyp 
  cases' haveInt_hyp with φ_θ haveInt_hyp
  cases' haveInt_hyp with θ_ψ vocSubs
  unfold Interpolant
  constructor
  · use φ_θ
  constructor
  · use θ_ψ
  · unfold voc at *
    unfold formulaHasVocabulary finsetFormulaHasVocabulary vocabOfSetFormula at *
    simp at *
    tauto
