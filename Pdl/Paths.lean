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

theorem existsWitnessPath_ltr (M : KripkeModel W) v δ ξ :
    evaluate M v (~ Formula.boxes δ ξ) → Nonempty (witness M v δ ξ) := by
  induction δ generalizing v
  case nil =>
    intro v_ξ
    constructor
    apply witness.nil
    simp at *
    exact v_ξ
  case cons α γs IH =>
    intro v_
    simp at *
    rcases v_ with ⟨w, v_α_w, w_⟩
    rcases IH w w_ with ⟨w_wit⟩
    cases α -- do this before `constructor`.
    case atom_prog a =>
      simp at v_α_w
      constructor
      apply witness.consAtom v_α_w w_wit
    -- TODO: in remaining cases, when do we use which one?
    -- apply withess.consEmpty
    -- apply witness.consComp
    case sequence α β =>
      simp at *
      rcases v_α_w with ⟨u, v_u, u_w⟩
      rcases IH w w_ with ⟨w_wit⟩
      constructor
      -- ?
      sorry
    case union α β =>
      -- ?
      constructor
      sorry
    case test τ =>
      -- ?
      constructor
      sorry
    case star β =>
      -- ?
      constructor
      sorry

theorem existsWitnessPath {M : KripkeModel W} δ v :
    (M,v) ⊨ (~ Formula.boxes δ ξ) ↔ Nonempty (witness M v δ ξ) := by
  constructor
  · simp [modelCanSemImplyForm, evaluatePoint] at *
    have := existsWitnessPath_ltr M v δ ξ
    simp_all
  · rintro ⟨wit⟩
    simp [modelCanSemImplyForm, evaluatePoint] at *
    have := existsWitnessPath_rtl M wit.length v δ ξ wit --  or remove wit.length later?
    simp_all
