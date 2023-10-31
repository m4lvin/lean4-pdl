-- INTERPOLATION

import Bml.Syntax
import Bml.Completeness
import Bml.Partitions

open HasVocabulary

def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  Tautology (φ↣θ) ∧ Tautology (θ↣ψ) ∧ voc θ ⊆ voc φ ∩ voc ψ

theorem interpolation {ϕ ψ} : Tautology (ϕ↣ψ) → ∃ θ, Interpolant ϕ ψ θ :=
  by
  intro hyp
  let X1 : Finset Formula := {ϕ}
  let X2 : Finset Formula := {~ψ}
  have ctX : ClosedTableau (X1 ∪ X2) :=
    by
    rw [tautImp_iff_comboNotUnsat] at hyp 
    rw [← completeness] at hyp 
    -- using completeness!
    unfold Consistent at hyp 
    simp at hyp 
    unfold Inconsistent at hyp 
    change ClosedTableau {ϕ, ~ψ}
    exact Classical.choice hyp
  have partInt := tabToInt ctX
  -- using tableau interpolation!
  rcases partInt with ⟨θ, pI_prop⟩
  unfold PartInterpolant at pI_prop 
  use θ
  constructor
  · rw [tautImp_iff_comboNotUnsat]; tauto
  constructor
  · rw [tautImp_iff_comboNotUnsat]; simp at *; tauto
  · cases pI_prop; simp at *; tauto
