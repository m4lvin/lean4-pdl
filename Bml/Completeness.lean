-- COMPLETENESS
import Syntax
import Tableau
import Soundness

#align_import completeness

-- import modelgraphs
-- import modelgraphs
open HasSat

-- Each local rule preserves truth "upwards"
theorem localRuleTruth {W : Type} {M : KripkeModel W} {w : W} {X : Finset Formula}
    {B : Finset (Finset Formula)} : LocalRule X B → (∃ Y ∈ B, (M, w)⊨Y) → (M, w)⊨X :=
  by
  intro r
  cases r
  case bot => simp
  case not => simp
  case neg a f notnotf_in_a =>
    intro hyp
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩
    intro phi phi_in_a
    have b_is_af : b = insert f (a \ {~~f}) := by simp at *; subst b_in_B
    have phi_in_b_or_is_f : phi ∈ b ∨ phi = ~~f :=
      by
      rw [b_is_af]
      simp
      finish
    cases' phi_in_b_or_is_f with phi_in_b phi_is_notnotf
    · apply w_sat_b
      exact phi_in_b
    · rw [phi_is_notnotf]
      unfold Evaluate at *
      simp
      -- this removes double negation
      apply w_sat_b
      rw [b_is_af]
      simp at *
  case con a f g fandg_in_a =>
    intro hyp
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩
    intro phi phi_in_a
    simp at b_in_B 
    have b_is_fga : b = insert f (insert g (a \ {f⋏g})) := by subst b_in_B; ext1; simp
    have phi_in_b_or_is_fandg : phi ∈ b ∨ phi = f⋏g :=
      by
      rw [b_is_fga]
      simp
      finish
    cases' phi_in_b_or_is_fandg with phi_in_b phi_is_fandg
    · apply w_sat_b
      exact phi_in_b
    · rw [phi_is_fandg]
      unfold Evaluate at *
      constructor
      · apply w_sat_b; rw [b_is_fga]; simp
      · apply w_sat_b; rw [b_is_fga]; simp
  case nCo a f g not_fandg_in_a =>
    intro hyp
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩
    intro phi phi_in_a
    simp at *
    have phi_in_b_or_is_notfandg : phi ∈ b ∨ phi = ~(f⋏g) := by
      cases b_in_B <;> · rw [b_in_B]; simp; finish
    cases b_in_B
    · -- b contains ~f
      cases' phi_in_b_or_is_notfandg with phi_in_b phi_def
      · exact w_sat_b phi phi_in_b
      · rw [phi_def]
        unfold Evaluate
        rw [b_in_B] at w_sat_b 
        specialize w_sat_b (~f)
        rw [not_and_or]
        left
        unfold Evaluate at w_sat_b 
        apply w_sat_b
        finish
    · -- b contains ~g
      cases' phi_in_b_or_is_notfandg with phi_in_b phi_def
      · exact w_sat_b phi phi_in_b
      · rw [phi_def]
        unfold Evaluate
        rw [b_in_B] at w_sat_b 
        specialize w_sat_b (~g)
        rw [not_and_or]
        right
        unfold Evaluate at w_sat_b 
        apply w_sat_b
        finish
#align localRuleTruth localRuleTruth

-- Each local rule is "complete", i.e. preserves satisfiability "upwards"
theorem localRuleCompleteness {X : Finset Formula} {B : Finset (Finset Formula)} :
    LocalRule X B → (∃ Y ∈ B, Satisfiable Y) → Satisfiable X :=
  by
  intro lr
  intro sat_B
  rcases sat_B with ⟨Y, Y_in_B, sat_Y⟩
  unfold satisfiable at *
  rcases sat_Y with ⟨W, M, w, w_sat_Y⟩
  use W, M, w
  apply localRuleTruth lr
  tauto
#align localRuleCompleteness localRuleCompleteness

-- Lemma 11 (but rephrased to be about local tableau!?)
theorem inconsUpwards {X} {ltX : LocalTableau X} :
    (∀ en ∈ endNodesOf ⟨X, ltX⟩, Inconsistent en) → Inconsistent X :=
  by
  intro lhs
  unfold Inconsistent at *
  let leafTableaus : ∀ en ∈ endNodesOf ⟨X, ltX⟩, ClosedTableau en := fun Y YinEnds =>
    (lhs Y YinEnds).some
  constructor
  exact ClosedTableau.loc ltX leafTableaus
#align inconsUpwards inconsUpwards

-- Converse of Lemma 11
theorem consToEndNodes {X} {ltX : LocalTableau X} :
    Consistent X → ∃ en ∈ endNodesOf ⟨X, ltX⟩, Consistent en :=
  by
  intro consX
  unfold Consistent at *
  have claim := Not.imp consX (@inconsUpwards X ltX)
  simp at claim 
  tauto
#align consToEndNodes consToEndNodes

def projOfConsSimpIsCons :
    ∀ {X ϕ}, Consistent X → Simple X → ~(□ϕ) ∈ X → Consistent (projection X ∪ {~ϕ}) :=
  by
  intro X ϕ consX simpX notBoxPhi_in_X
  unfold Consistent at *
  unfold Inconsistent at *
  by_contra h
  simp at *
  cases' h with ctProj
  have ctX : ClosedTableau X :=
    by
    apply ClosedTableau.atm notBoxPhi_in_X simpX
    simp; exact ctProj
  cases consX; tauto
#align projOfConsSimpIsCons projOfConsSimpIsCons

theorem locTabEndSatThenSat {X Y} (ltX : LocalTableau X) (Y_endOf_X : Y ∈ endNodesOf ⟨X, ltX⟩) :
    Satisfiable Y → Satisfiable X := by
  intro satY
  induction ltX
  case byLocalRule X B lr next IH =>
    apply localRuleCompleteness lr
    cases lr
    case bot W bot_in_W =>
      simp at *
      exact Y_endOf_X
    case not _ ϕ h =>
      simp at *
      exact Y_endOf_X
    case neg Z ϕ notNotPhi_inX =>
      simp at *
      specialize IH (insert ϕ (Z.erase (~~ϕ)))
      simp at IH 
      apply IH
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩
      subst W_def
      exact Y_endOf_W
    case con Z ϕ ψ _ =>
      simp at *
      specialize IH (insert ϕ (insert ψ (Z.erase (ϕ⋏ψ))))
      simp at IH 
      apply IH
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩
      subst W_def
      exact Y_endOf_W
    case nCo Z ϕ ψ _ =>
      simp at *
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩
      cases W_def
      all_goals subst W_def
      · specialize IH (insert (~ϕ) (Z.erase (~(ϕ⋏ψ))))
        simp at IH 
        use insert (~ϕ) (Z.erase (~(ϕ⋏ψ)))
        constructor
        · left; rfl
        · apply IH; exact Y_endOf_W
      · specialize IH (insert (~ψ) (Z.erase (~(ϕ⋏ψ))))
        simp at IH 
        use insert (~ψ) (Z.erase (~(ϕ⋏ψ)))
        constructor
        · right; rfl
        · apply IH; exact Y_endOf_W
  case sim X simpX => finish
#align locTabEndSatThenSat locTabEndSatThenSat

theorem almostCompleteness : ∀ n X, lengthOfSet X = n → Consistent X → Satisfiable X :=
  by
  intro n
  apply Nat.strong_induction_on n
  intro n IH
  intro X lX_is_n consX
  refine' if simpX : Simple X then _ else _
  -- CASE 1: X is simple
  rw [Lemma1_simple_sat_iff_all_projections_sat simpX]
  constructor
  · -- show that X is not closed
    by_contra h
    unfold Consistent at consX 
    unfold Inconsistent at consX 
    simp at consX 
    cases consX; apply consX
    unfold Closed at h 
    refine' if botInX : ⊥ ∈ X then _ else _
    · apply ClosedTableau.loc; rotate_left; apply LocalTableau.byLocalRule
      exact LocalRule.bot botInX
      intro Y YinEmpty; cases YinEmpty
      rw [botNoEndNodes]; intro Y YinEmpty; cases YinEmpty
    · have f1 : ∃ (f : Formula) (H : f ∈ X), ~f ∈ X := by tauto
      have : Nonempty (ClosedTableau X) :=
        by
        rcases f1 with ⟨f, f_in_X, notf_in_X⟩
        fconstructor
        apply ClosedTableau.loc; rotate_left; apply LocalTableau.byLocalRule
        apply LocalRule.not ⟨f_in_X, notf_in_X⟩
        intro Y YinEmpty; cases YinEmpty
        rw [notNoEndNodes]; intro Y YinEmpty; cases YinEmpty
      exact Classical.choice this
  · -- show that all projections are sat
    intro R notBoxR_in_X
    apply IH (lengthOfSet (projection X ∪ {~R}))
    · -- projection decreases lengthOfSet
      subst lX_is_n
      exact atmRuleDecreasesLength notBoxR_in_X
    · rfl
    · exact projOfConsSimpIsCons consX simpX notBoxR_in_X
  -- CASE 2: X is not simple
  rename' simpX => notSimpX
  rcases notSimpleThenLocalRule notSimpX with ⟨B, lrExists⟩
  have lr := Classical.choice lrExists
  have rest : ∀ Y : Finset Formula, Y ∈ B → LocalTableau Y :=
    by
    intro Y Y_in_B
    set N := HasLength.lengthOf Y
    exact Classical.choice (existsLocalTableauFor N Y (by rfl))
  rcases@consToEndNodes X (LocalTableau.byLocalRule lr rest) consX with ⟨E, E_endOf_X, consE⟩
  have satE : satisfiable E := by
    apply IH (lengthOfSet E)
    · -- end Node of local rule is LT
      subst lX_is_n
      apply endNodesOfLocalRuleLT E_endOf_X
    · rfl
    · exact consE
  exact locTabEndSatThenSat (LocalTableau.byLocalRule lr rest) E_endOf_X satE
#align almostCompleteness almostCompleteness

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    let n := lengthOfSet X
    apply almostCompleteness n X (by rfl) X_is_consistent
  -- use Theorem 2:
  exact correctness X
#align completeness completeness

theorem singletonCompleteness : ∀ φ, Consistent {φ} ↔ Satisfiable φ :=
  by
  intro f
  have := completeness {f}
  simp only [singletonSat_iff_sat] at *
  tauto
#align singletonCompleteness singletonCompleteness
