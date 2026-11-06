module

public import Mathlib.Data.Finset.Basic

public import Pdl.Interpolation.Def
public import Pdl.Completeness.Theorem
public import Pdl.Interpolation.Statement

/-! # Interpolation (Section 7) -/

@[expose] public section

open vDash HasSat

theorem interpolation :
    PdlHasInterpolation := by
  unfold PdlHasInterpolation
  intro φ ψ hyp
  let X : Sequent := ({φ}, {~(ψ)}, none)
  have have_tab : ∃ u_tab : Tableau .nil ({φ}, {~(ψ)}, none), u_tab.isUniform := by
    rw [tautImp_iff_SequentUnsat rfl] at hyp
    rw [← consIffSat _] at hyp -- using completeness
    simp [consistent,inconsistent] at hyp
    rcases hyp with ⟨tab⟩
    have := Tableau.toUniformViaGame tab -- Yeah.
    rcases this with ⟨t, t_h⟩
    exact ⟨t, t_h⟩
  rcases have_tab with ⟨tab, tab_uni⟩
  have partInt := tabToInt tab tab_uni -- using tableau interpolation
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
    simp [satisfiable] at *
    intro W M w
    specialize this W M w
    tauto
  · have := pI_prop.2.2
    clear pI_prop
    rw [tautImp_iff_comboNotUnsat]
    simp [satisfiable] at *
    intro W M w
    specialize this W M w
    tauto
