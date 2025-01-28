import Pdl.Interpolation

/-! # Beth Definability (Sections 2.3 and 7) -/

open vDash HasSat

def Formula.implicitlyDefines (φ : Formula) (q : Nat) : Prop :=
  ∀ q', φ ⋀ repl_in_F q (·q') φ ⊨ (·q) ⟷ (·q')

def Formula.explicitlyDefines (ψ : Formula) (φ : Formula) (q : Nat) : Prop :=
  φ ⊨ (·q) ⟷ ψ

theorem beth (φ : Formula) (h : φ.implicitlyDefines q) :
    ∃ (ψ : Formula), ψ.explicitlyDefines φ q := by
  unfold Formula.implicitlyDefines at h
  -- Question How to choose q' ?
  let q' : Nat := 42 -- ?!?!?!
  -- PROBLEM: that this works tells me that the definitions of
  -- implicitly and explicitly defining above are too weak.
  specialize h q'
  -- The following would be needed if we change the `Interpolant` def.
  -- have := deduction [] _ _ this
  have : φ ⊨ repl_in_F q (·q') φ ↣ ((·q) ⟷ (·q')) := by
    intro W M w
    specialize h W M w
    aesop
  have := interpolation _ _ this
  rcases this with ⟨ψ, ip_voc, ip_one, ip_two⟩
  use ψ
  unfold Formula.explicitlyDefines
  intro W M w w_φ
  simp at w_φ
  simp
  intro w_q
  aesop
