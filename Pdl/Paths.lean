
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

theorem existsWitnessPath {M : KripkeModel W} δ v :
    (M,v) ⊨ (~ Formula.boxes δ ξ) ↔ ∃ π, witnessing M v π δ ξ := by
  induction δ generalizing v
  case nil =>
    simp [modelCanSemImplyForm, witnessing]
    constructor
    · intro nvXi
      use ⟨[], by simp⟩
      simp only [witnessing, modelCanSemImplyForm, evaluatePoint, evaluate]
      exact nvXi
    · rintro ⟨π, foo⟩
      rcases π with ⟨no|bla, foo⟩
      · simp [witnessing, modelCanSemImplyForm, evaluatePoint, evaluate] at *
        assumption
      · simp [witnessing] at *
  case cons d δ IH =>
    simp only [Formula.boxes]
    constructor
    · simp only [modelCanSemImplyForm, evaluatePoint, evaluate, not_forall, exists_prop, forall_exists_index, and_imp] at *
      intro w v_d_w not_w_
      rw [IH] at not_w_
      -- rcases not_w_ with ⟨π, wit⟩
      -- simp [witnessing] at *

      sorry
    ·
      sorry
