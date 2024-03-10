import Mathlib.Data.Finset.Basic

import Pdl.PartInterpolation

open HasVocabulary vDash HasSat

def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  voc θ ⊆ voc φ ∩ voc ψ  ∧  φ ⊨ θ  ∧  θ ⊨ ψ



theorem interpolation : ∀ (φ : Formula) (ψ : Formula), φ⊨ψ → ∃ θ : Formula, Interpolant φ ψ θ :=
  by sorry /-
  intro φ ψ hyp
  let L : List Formula := {φ}
  let R : List Formula := {~ψ}
  have : ¬Satisfiable (L ∪ R) := by
    rw [notSat_iff_semImplies]
    exact forms_to_sets hyp
  have haveInt := partInterpolation L R this
  rcases haveInt with ⟨θ, ⟨vocSubs, φ_θ, θ_ψ⟩⟩
  use θ
  rw [notSat_iff_semImplies] at φ_θ
  rw [notSat_iff_semImplies] at θ_ψ
  unfold Interpolant
  simp [voc, vocabOfFormula, vocabOfSetFormula] at vocSubs
  tauto-/
