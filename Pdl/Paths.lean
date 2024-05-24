
import Pdl.Unfold

def atomRel {W} (M : KripkeModel W) (v w : W) := ∃ a, relate M (·a) v w

abbrev WorldPath {W} (M : KripkeModel W) := Subtype $ List.Chain' (atomRel M)

@[simp]
def WorldPath.tail (π : WorldPath M) : WorldPath M := ⟨π.1.tail, π.2.tail⟩

/-- Does path `π` starting at v0 witness `¬□(δ,ξ)`? -/
-- IDEA: rewrite this as an inductive prop instead of matching?
def witnessing (M : KripkeModel W) (v0 : W) (π : WorldPath M) (δ : List Program) (ξ : Formula) : Prop :=
  match π.1, δ with
    -- Case |π| = 0:
    | [], [] => (M,v0) ⊨ (~ξ)
    | [], _::_ => False
    -- Case |π| > 0:
    | _ :: _ , [] => False
    | v1 :: rest , α::γs =>
        (∃ a, α = (Program.atom_prog a) ∧ witnessing M v1 π.tail γs ξ)
      ∨ ∃ Fβ ∈ H α,
        (M,v0) ⊨ Fβ.1
        ∧ (
          (Fβ.2 = ε ∧ witnessing M v0 π γs ξ)
          ∨
          (∃ a, ∃ ηs, Fβ.2 = ((Program.atom_prog a) :: ηs) ∧ witnessing M v1 π.tail (ηs ++ γs) ξ)
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
      use [], (by simp)
      simp only [witnessing, modelCanSemImplyForm, evaluatePoint, evaluate]
      exact nvXi
    · rintro ⟨π, ⟨l, foo⟩⟩
      cases π
      · simp_all [witnessing, modelCanSemImplyForm]
      · exfalso; unfold witnessing at foo; tauto
  case cons d δ IH =>
    simp only [Formula.boxes]
    constructor
    · simp only [modelCanSemImplyForm, evaluatePoint, evaluate, not_forall, exists_prop, forall_exists_index, and_imp] at *
      intro w v_d_w not_w_
      rw [IH] at not_w_
      clear IH
      rcases not_w_ with ⟨⟨π, l⟩, wit⟩
      -- simp [witnessing] at *
      cases d
      all_goals simp only [relate] at v_d_w
      case atom_prog a =>
        cases π <;> cases δ -- yield four cases, matching those in `def witnessing`.
        · refine ⟨⟨[w], ?_⟩, ?_⟩
          simp
          unfold witnessing
          simp
          left
          assumption
        · exfalso; simp [witnessing] at wit
        · exfalso; unfold witnessing at wit; exact wit
        · unfold witnessing
          simp
          sorry
      case test φ =>
        sorry
      case sequence α β =>
        sorry
      case union α β =>
        sorry
      case star α =>
        sorry
    ·
      sorry
