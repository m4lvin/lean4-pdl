
import Pdl.Unfold

def atomRel {W} (M : KripkeModel W) (v w : W) := ∃ a, relate M (·a) v w

abbrev WorldPath {W} (M : KripkeModel W) := Subtype $ List.Chain' (atomRel M)

@[simp]
def WorldPath.tail (π : WorldPath M) : WorldPath M := ⟨π.1.tail, π.2.tail⟩

/-- Does path `π` starting at v0 witness `¬□(δ,ξ)`? -/
-- NOTE: Not using `WorldPath` any more, atom relation is built in here!
inductive witness (M : KripkeModel W) : W  → List W → List Program → Formula → Prop
 -- Case |π| = 0:
| nil : (M,v0) ⊨ (~ξ) → witness M v0 [] [] ξ
 -- Case |π| > 0:
| consAtom : M.Rel a v0 v1 → witness M v1 rest γs ξ → witness M v0 (v1 :: rest) ((·a) :: γs) ξ
| consEmpty Fs : (⟨Fs, ε⟩ ∈ H α) → (M, v0) ⊨ Fs → witness M v0 π γs ξ → witness M v0 π (α::γs) ξ
| consComp : M.Rel a v0 v1 → (⟨Fs, (·a : Program) :: η⟩ ∈ H α) → (M, v0) ⊨ Fs → witness M v1 rest (ηs ++ γs) ξ → witness M v0 (v1 :: rest) (α::γs) ξ

theorem existsWitnessPath {M : KripkeModel W} δ v :
    (M,v) ⊨ (~ Formula.boxes δ ξ) ↔ ∃ π, witness M v π δ ξ := by
  induction δ generalizing v
  case nil =>
    simp [modelCanSemImplyForm, witness]
    constructor
    · intro nvXi
      use []
      apply witness.nil
      simp only [modelCanSemImplyForm, evaluatePoint, evaluate]
      exact nvXi
    · rintro ⟨π, wit⟩
      cases wit
      simp only [modelCanSemImplyForm, evaluatePoint, evaluate] at *
      assumption
  case cons d δ IH =>
    simp only [Formula.boxes]
    constructor
    · simp [modelCanSemImplyForm, evaluatePoint, evaluate, not_forall, exists_prop, forall_exists_index, and_imp] at *
      intro w v_d_w not_w_
      rw [IH] at not_w_
      clear IH
      rcases not_w_ with ⟨π, wit⟩
      cases d -- Distinguish cases by the first program `d` in the path `d :: δ`.
      all_goals simp only [relate] at v_d_w
      case atom_prog a =>
        exact ⟨w :: π, witness.consAtom v_d_w wit⟩
      case test φ =>
        rcases v_d_w with ⟨v_is_w, v_φ⟩
        subst v_is_w
        use π
        apply witness.consEmpty [φ] (by simp [H]) (by simp [modelCanSemImplyList]; exact v_φ) wit
      -- NEXT: in all remaining cases, use witness.consComp
      -- QUESTION: Do we need IHs/recursion now? What if δ becomes longer in the recursive call?
      case sequence α β =>
        sorry
      case union α β =>
        sorry
      case star α =>
        sorry
    ·
      sorry
