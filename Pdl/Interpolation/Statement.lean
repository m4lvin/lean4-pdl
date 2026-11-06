module

public import Pdl.Semantics
public import Pdl.Vocab

/-! # Interpolation: Definition and Statement -/

@[expose] public section

open vDash HasSat

/-- An interpolant θ for φ and ψ only uses the vocabulary
in both, is implied by φ and implies ψ. -/
def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  θ.voc ⊆ φ.voc ∩ ψ.voc  ∧  tautology (φ ↣ θ)  ∧  tautology (θ ↣ ψ)

/-- The *statement* that PDL has Craig Interpolation.
We define it here in a separate file to make it easier to import,
without pulling in the whole proof system and completeness proofs.
The proof is in `interpolation`. -/
abbrev PdlHasInterpolation : Prop := ∀ {φ ψ},
  tautology (φ ↣ ψ) → ∃ θ : Formula, Interpolant φ ψ θ
