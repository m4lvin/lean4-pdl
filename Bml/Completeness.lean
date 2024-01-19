-- COMPLETENESS

import Bml.Syntax
import Bml.Tableau
import Bml.Soundness

open HasSat

-- Each local rule preserves truth "upwards"
theorem localRuleTruth {W : Type} {M : KripkeModel W} {w : W} {X : Finset Formula}
    {B : Finset (Finset Formula)} : LocalRule X B → (∃ Y ∈ B, (M, w)⊨Y) → (M, w)⊨X :=
  by
  intro r
  cases r
  case bot => simp
  case Not => simp
  case neg f notnotf_in_a =>
    intro hyp
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩
    intro phi phi_in_a
    have b_is_af : b = insert f (X \ {~~f}) := by simp at *; subst b_in_B; tauto
    have phi_in_b_or_is_f : phi ∈ b ∨ phi = ~~f :=
      by
      rw [b_is_af]
      simp
      tauto
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
  case Con f g fandg_in_a =>
    intro hyp
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩
    intro phi phi_in_a
    simp at b_in_B 
    have b_is_fga : b = insert f (insert g (X \ {f⋀g})) := by subst b_in_B; ext1; simp
    have phi_in_b_or_is_fandg : phi ∈ b ∨ phi = f⋀g :=
      by
      rw [b_is_fga]
      simp
      tauto
    cases' phi_in_b_or_is_fandg with phi_in_b phi_is_fandg
    · apply w_sat_b
      exact phi_in_b
    · rw [phi_is_fandg]
      unfold Evaluate at *
      constructor
      · apply w_sat_b; rw [b_is_fga]; simp
      · apply w_sat_b; rw [b_is_fga]; simp
  case nCo f g not_fandg_in_a =>
    intro hyp
    rcases hyp with ⟨b, b_in_B, w_sat_b⟩
    intro phi phi_in_a
    simp at *
    have phi_in_b_or_is_notfandg : phi ∈ b ∨ phi = ~(f⋀g) := by
      cases b_in_B
      case inl b_in_B => rw [b_in_B]; simp; tauto
      case inr b_in_B => rw [b_in_B]; simp; tauto
    cases b_in_B
    case inl b_in_B => -- b contains ~f
      cases' phi_in_b_or_is_notfandg with phi_in_b phi_def
      · exact w_sat_b phi phi_in_b
      · rw [phi_def]
        unfold Evaluate
        rw [b_in_B] at w_sat_b 
        specialize w_sat_b (~f)
        aesop
    case inr b_in_B => -- b contains ~g
      cases' phi_in_b_or_is_notfandg with phi_in_b phi_def
      · exact w_sat_b phi phi_in_b
      · rw [phi_def]
        unfold Evaluate
        rw [b_in_B] at w_sat_b 
        specialize w_sat_b (~g)
        aesop

-- Each local rule is "complete", i.e. preserves satisfiability "upwards"
theorem localRuleCompleteness {X : Finset Formula} {B : Finset (Finset Formula)} :
    LocalRule X B → (∃ Y ∈ B, Satisfiable Y) → Satisfiable X :=
  by
  intro lr
  intro sat_B
  rcases sat_B with ⟨Y, Y_in_B, sat_Y⟩
  unfold Satisfiable at *
  rcases sat_Y with ⟨W, M, w, w_sat_Y⟩
  use W, M, w
  apply localRuleTruth lr
  tauto

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

-- Converse of Lemma 11
theorem consToEndNodes {X} {ltX : LocalTableau X} :
    Consistent X → ∃ en ∈ endNodesOf ⟨X, ltX⟩, Consistent en :=
  by
  intro consX
  unfold Consistent at *
  have claim := Not.imp consX (@inconsUpwards X ltX)
  simp at claim 
  tauto

def projOfConsSimpIsCons :
    ∀ {X ϕ}, Consistent X → SimpleSetDepr X → ~(□ϕ) ∈ X → Consistent (projection X ∪ {~ϕ}) :=
  by
  intro X ϕ consX simpX notBoxPhi_in_X
  unfold Consistent at *
  unfold Inconsistent at *
  contrapose consX
  simp at *
  cases' consX with ctProj
  constructor
  apply ClosedTableau.atm notBoxPhi_in_X simpX
  simp
  exact ctProj

theorem locTabEndSatThenSat {X Y} (ltX : LocalTableau X) (Y_endOf_X : Y ∈ endNodesOf ⟨X, ltX⟩) :
    Satisfiable Y → Satisfiable X := by
  intro satY
  induction ltX
  case byLocalRule X B lr next IH =>
    apply localRuleCompleteness lr
    cases lr
    case bot W bot_in_W =>
      simp at *
    case Not ϕ h =>
      simp at *
    case neg ϕ notNotPhi_inX =>
      simp at *
      specialize IH (insert ϕ (X.erase (~~ϕ)))
      simp at IH
      apply IH
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩
      subst W_def
      exact Y_endOf_W
    case Con ϕ ψ _ =>
      simp at *
      specialize IH (insert ϕ (insert ψ (X.erase (ϕ⋀ψ))))
      simp at IH 
      apply IH
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩
      subst W_def
      exact Y_endOf_W
    case nCo ϕ ψ _ =>
      rw [nCoEndNodes, Finset.mem_union] at Y_endOf_X
      cases Y_endOf_X
      case inl Y_endOf_X =>
        specialize IH (X \ {~(ϕ⋀ψ)} ∪ {~ϕ})
        use X \ {~(ϕ⋀ψ)} ∪ {~ϕ}
        constructor
        · simp
        · apply IH
          convert Y_endOf_X;
      case inr Y_endOf_X =>
        specialize IH (X \ {~(ϕ⋀ψ)} ∪ {~ψ})
        use X \ {~(ϕ⋀ψ)} ∪ {~ψ}
        constructor
        · simp
        · apply IH
          convert Y_endOf_X;
  case sim X simpX => aesop

theorem almostCompleteness : (X : Finset Formula) → Consistent X → Satisfiable X :=
  by
  intro X consX
  refine' if simpX : SimpleSetDepr X then _ else _
  -- CASE 1: X is simple
  rw [Lemma1_simple_sat_iff_all_projections_sat simpX]
  constructor
  · -- show that X is not closed
    by_contra h
    unfold Consistent at consX 
    unfold Inconsistent at consX 
    simp at consX 
    cases' consX with myfalse
    apply myfalse
    unfold Closed at h 
    refine' if botInX : ⊥ ∈ X then _ else _
    · apply ClosedTableau.loc; rotate_left; apply LocalTableau.byLocalRule
      exact LocalRule.bot botInX
      intro Y YinEmpty; exfalso; cases YinEmpty
      rw [botNoEndNodes]; intro Y YinEmpty; exfalso; cases YinEmpty
    · have f1 : ∃ (f : Formula) (_ : f ∈ X), ~f ∈ X := by tauto
      have : Nonempty (ClosedTableau X) :=
        by
        rcases f1 with ⟨f, f_in_X, notf_in_X⟩
        fconstructor
        apply ClosedTableau.loc; rotate_left; apply LocalTableau.byLocalRule
        apply LocalRule.Not ⟨f_in_X, notf_in_X⟩
        intro Y YinEmpty; exfalso; cases YinEmpty
        rw [notNoEndNodes]; intro Y YinEmpty; exfalso; cases YinEmpty
      exact Classical.choice this
  · -- show that all projections are sat
    intro R notBoxR_in_X
    have : Finset.sum (insert (~R) (projection X)) lengthOfFormula < Finset.sum X lengthOfFormula := by
      convert atmRuleDecreasesLength notBoxR_in_X
      simp
    exact almostCompleteness (projection X ∪ {~R}) (projOfConsSimpIsCons consX simpX notBoxR_in_X)
  -- CASE 2: X is not simple
  rename' simpX => notSimpX
  rcases notSimpleThenLocalRule notSimpX with ⟨B, lrExists⟩
  have lr := Classical.choice lrExists
  have rest : ∀ Y : Finset Formula, Y ∈ B → LocalTableau Y :=
    by
    intro Y _
    exact Classical.choice (existsLocalTableauFor Y)
  rcases@consToEndNodes X (LocalTableau.byLocalRule lr rest) consX with ⟨E, E_endOf_X, consE⟩
  have satE : Satisfiable E := by
    have := endNodesOfLocalRuleLT E_endOf_X
    exact almostCompleteness E consE
  exact locTabEndSatThenSat (LocalTableau.byLocalRule lr rest) E_endOf_X satE
termination_by
  almostCompleteness X _ => lengthOfSet X

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    apply almostCompleteness X X_is_consistent
  -- use Theorem 2:
  exact correctness X

theorem singletonCompleteness : ∀ φ, Consistent {φ} ↔ Satisfiable φ :=
  by
  intro f
  have := completeness {f}
  simp only [singletonSat_iff_sat] at *
  tauto
