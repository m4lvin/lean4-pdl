import Pdl.Vocab
import Pdl.Semantics

/-- An interpolant θ for φ and ψ only uses the vocabulary
in both, is implied by φ and implies ψ. -/
def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  θ.voc ⊆ φ.voc ∩ ψ.voc  ∧  tautology (φ ↣ θ)  ∧  tautology (θ ↣ ψ)
