import Pdl.Semantics
import Pdl.Unfold

def atomRel (M : KripkeModel W) (v w : W) := ∃ a, relate M (·a) v w

def WorldPath {W} (M : KripkeModel W) := Subtype $ List.Chain' (atomRel M)

/-- Does path `π` witness `¬□(δ,ξ)` at `v0`? -/
def witnessing (M : KripkeModel W) (v0 : W) (π : WorldPath M) (δ : List Program) (ξ : Formula) : Prop :=
  match π, δ with
    -- Case |π| = 0:
    | ⟨[],_⟩, [] => (M,v0) ⊨ (~ξ)
    | ⟨[],_⟩, (_::_) => False
    -- Case |π| > 0:
    | ⟨_::_, _⟩ , [] => False
    | π@⟨v1::rest, _⟩ , α::γs =>
        (∃ a, α = (Program.atom_prog a) ∧ witnessing M v1 ⟨rest, sorry⟩ γs ξ)
      ∨ ∃ Fβ ∈ H α,
        (M,v0) ⊨ Fβ.1
        ∧ (
          (Fβ.2 = ε ∧ witnessing M v0 π γs ξ)
          ∨
          (∃ a, ∃ ηs, Fβ.2 = ((Program.atom_prog a) :: ηs) ∧ witnessing M v1 ⟨rest, sorry⟩ (ηs ++ γs) ξ)
          )
termination_by (π.1.length, δ.length)
decreasing_by
  all_goals sorry

theorem existsWitnessPath {M : KripkeModel W} :
    (M,v) ⊨ (~ Formula.boxes δ ξ) ↔ ∃ π, witnessing M v π δ ξ := by
  sorry
