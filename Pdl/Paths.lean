import Pdl.Unfold

def atomRel {W} (M : KripkeModel W) (v w : W) := ∃ a, relate M (·a) v w

abbrev WorldPath {W} (M : KripkeModel W) := Subtype $ List.Chain' (atomRel M)

@[simp]
def WorldPath.tail (π : WorldPath M) : WorldPath M := ⟨π.1.tail, π.2.tail⟩

/-- A path starting at `v0` to witness `¬□(δ,ξ)`. -/
-- NOTE: Not using `WorldPath` any more, atom relation is built in here.
inductive witness : KripkeModel W → (v0 : W) → (δ : List Program) → (ξ : Formula) → Type
 -- Case |π| = 0:
| nil : evaluate M v0 (~ξ) → witness M v0 [] ξ
 -- Case |π| > 0:
| consAtom {a} {v1} {γs} :
    (v0_a_v1 : M.Rel a v0 v1)
      → witness M v1 γs ξ
      → witness M v0 ((·a) :: γs) ξ
| consEmpty Fs :
    (⟨Fs, ε⟩ ∈ H α)
      → evaluate M v0 (Con Fs)
      → witness M v0 γs ξ
      → witness M v0 (α::γs) ξ
| consComp :
    M.Rel a v0 v1
      → (⟨Fs, (·a : Program) :: ηs⟩ ∈ H α)
      → evaluate M v0 (Con Fs)
      → witness M v1 (ηs ++ γs) ξ
      → witness M v0 (α::γs) ξ

def witness.length : witness M v δ ξ → Nat
| nil _ => 0
| consAtom _ wit => 1 + wit.length
| consEmpty _ _ _ wit => 1 + wit.length
| consComp _ _ _ wit => 1 + wit.length

theorem existsWitnessPath_rtl (M : KripkeModel W) (n : Nat) :
    ∀ v δ ξ (wit : witness M v δ ξ),
      wit.length = n → evaluate M v (~ Formula.boxes δ ξ) := by
  induction n
  case zero =>
    intro v δ ξ wit def_n
    subst_eqs
    cases wit
    case nil =>
      subst_eqs
      simp [Formula.boxes, evaluate] at *
      assumption
    all_goals
      exfalso
      simp [witness.length] at *
  case succ n IH =>
    intro v δ ξ wit def_n
    subst_eqs
    cases wit
    case nil =>
      exfalso
      subst_eqs
    case consAtom a v1 γs v0_a_v1 wit_v1_γs =>
      simp only [evaluate, witness.length, Formula.boxes, relate, not_forall, exists_prop] at *
      refine ⟨v1, v0_a_v1, IH v1 γs ξ wit_v1_γs ?_⟩
      linarith
    case consEmpty α γs Fs Fε_in_Hα v_Fs wit_γs =>
      simp only [evaluate, witness.length, Formula.boxes, relate, not_forall, exists_prop] at *
      use v -- no real step
      constructor
      · -- need Lemma about H here?
        sorry
      · apply IH v γs ξ wit_γs
        linarith
    case consComp α Fs v1 ηs γs a Fsaηs_in_Hα v_a_v1 four wit_v1_ηγs =>
      simp only [evaluate, witness.length, Formula.boxes, relate, not_forall, exists_prop] at *
      use v1 -- DO a real step here, true??
      constructor
      ·
        -- need Lemma about H here?
        -- Note α vs a.
        sorry
      · specialize IH v1 (ηs++γs) ξ wit_v1_ηγs ?_
        ·
          -- PROBLEM: ηs++γs is too long, longer than n. try `induction wit` instead?
          sorry

        · -- need Lemma about H here?
          sorry


/-
theorem existsWitnessPath {M : KripkeModel W} δ v :
    (M,v) ⊨ (~ Formula.boxes δ ξ) ↔ ∃ π, witness M v π δ ξ := by
  induction δ generalizing v
  case nil =>
    simp [modelCanSemImplyForm, witness]
    constructor
    · intro nvXi
      use []
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
      rcases not_w_ with ⟨π, w_π_δ_wit⟩
      cases d -- Distinguish cases by the first program `d` in the path `d :: δ`.
      all_goals simp only [relate] at v_d_w
      case atom_prog a =>
        exact ⟨w :: π, witness.consAtom v_d_w w_π_δ_wit⟩
      case test φ =>
        rcases v_d_w with ⟨v_is_w, v_φ⟩
        subst v_is_w
        use π
        exact witness.consEmpty [φ] (by simp [H]) (by simp [modelCanSemImplyList]; exact v_φ) w_π_δ_wit
      -- NEXT: in all remaining cases, use witness.consComp
      -- QUESTION: Do we need IHs/recursion now? What if δ becomes longer in the recursive call?
      case sequence α β =>
        rcases v_d_w with ⟨u, v_α_u, u_β_w⟩

        sorry
      case union α β =>
        sorry
      case star α =>
        sorry
    ·
      sorry
-/
