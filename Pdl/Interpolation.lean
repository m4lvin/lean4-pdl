import Mathlib.Data.Finset.Basic

import Pdl.PartInterpolation

open HasVocabulary vDash HasSat

def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  voc θ ⊆ voc φ ∩ voc ψ  ∧  φ ⊨ θ  ∧  θ ⊨ ψ

theorem interpolation : ∀ (φ ψ : Formula), φ⊨ψ → ∃ θ : Formula, Interpolant φ ψ θ :=
  by
  intro φ ψ hyp
  let X : TNode := ([φ], [~(ψ)], none)
  have ctX : ClosedTableau ([],[]) X :=
    by
    rw [tautImp_iff_TNodeUnsat rfl] at hyp
    rw [← completeness] at hyp -- using completeness
    simp [consistent,inconsistent] at hyp
    exact Classical.choice hyp
  have partInt := tabToInt ctX -- using tableau interpolation
  rcases partInt with ⟨θ, pI_prop⟩
  unfold isPartInterpolant at pI_prop
  use θ
  constructor
  · intro f f_in
    simp [voc,jvoc,vocabOfListFormula,vocabOfFormula] at pI_prop
    exact pI_prop.1 f_in
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
