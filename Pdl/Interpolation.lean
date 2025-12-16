import Mathlib.Data.Finset.Basic

import Pdl.PartInterpolation
import Pdl.Completeness

/-! # Interpolation (Sections 2.3 and 7) -/

open vDash HasSat

/-- An interpolant θ for φ and ψ only uses the vocabulary
in both, is implied by φ and implies ψ. -/
def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  θ.voc ⊆ φ.voc ∩ ψ.voc  ∧  tautology (φ ↣ θ)  ∧  tautology (θ ↣ ψ)

theorem interpolation {φ ψ : Formula} :
    tautology (φ ↣ ψ) → ∃ θ : Formula, Interpolant φ ψ θ := by
  intro hyp
  let X : Sequent := ([φ], [~(ψ)], none)
  have ctX : Tableau .nil ([φ], [~(ψ)], none) :=
    by
    rw [tautImp_iff_SequentUnsat rfl] at hyp
    rw [← consIffSat _ (by simp)] at hyp -- using completeness
    simp only [consistent, inconsistent, not_nonempty_iff, not_isEmpty_iff] at hyp
    exact Classical.choice hyp
  have partInt := tabToInt ctX -- using tableau interpolation
  rcases partInt with ⟨θ, pI_prop⟩
  unfold isPartInterpolant at pI_prop
  use θ
  constructor
  · intro f f_in
    have := pI_prop.1 f_in
    clear pI_prop
    simpa
  constructor
  · have := pI_prop.2.1
    clear pI_prop
    rw [tautImp_iff_comboNotUnsat]
    simp only [satisfiable, Sequent.left_eq, Olf.L_none, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, evaluate, forall_eq, not_exists, not_and,
      not_not] at *
    intro W M w
    specialize this W M w
    tauto
  · have := pI_prop.2.2
    clear pI_prop
    rw [tautImp_iff_comboNotUnsat]
    simp only [satisfiable, Sequent.right_eq, Olf.R_none, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, evaluate, not_exists, not_and,
      not_not] at *
    intro W M w
    specialize this W M w
    tauto
