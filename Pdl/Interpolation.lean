import Mathlib.Data.Finset.Basic

import Pdl.Syntax
import Pdl.Vocab
import Pdl.Semantics

open HasVocabulary vDash HasSat

def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  voc θ ⊆ voc φ ∩ voc ψ  ∧  φ ⊨ θ  ∧  θ ⊨ ψ

def PartInterpolant (X1 X2 : Finset Formula) (θ : Formula) :=
  voc θ ⊆ voc X1 ∩ voc X2  ∧  ¬ satisfiable (X1 ∪ {~θ})  ∧  ¬ satisfiable ({θ} ∪ X2)

theorem partInterpolation :
    ∀ (X1 X2 : Finset Formula), ¬satisfiable (X1 ∪ X2) → ∃ θ : Formula, PartInterpolant X1 X2 θ := by
  sorry

theorem interpolation : ∀ (φ : Formula) (ψ : Formula), φ⊨ψ → ∃ θ : Formula, Interpolant φ ψ θ :=
  by
  intro φ ψ hyp
  let X1 : Finset Formula := {φ}
  let X2 : Finset Formula := {~ψ}
  have : ¬satisfiable (X1 ∪ X2) := by
    rw [notSat_iff_semImplies]
    exact forms_to_sets hyp
  have haveInt := partInterpolation X1 X2 this
  rcases haveInt with ⟨θ, ⟨vocSubs, φ_θ, θ_ψ⟩⟩
  use θ
  rw [notSat_iff_semImplies] at φ_θ
  rw [notSat_iff_semImplies] at θ_ψ
  unfold Interpolant
  simp [voc, vocabOfFormula, vocabOfSetFormula] at vocSubs
  tauto
