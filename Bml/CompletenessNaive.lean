-- COMPLETENESS

-- NOTE: This file is broken and obsolete.
-- See instead "CompletenessViaPaths.lean".

import Bml.Soundness

open HasSat

instance modelCanSemImplyTNode {W : Type} : VDash (KripkeModel W × W) TNode := ⟨fun Mw X => ∀ f ∈ X.1 ∪ X.2, @Evaluate W Mw f⟩

-- Each local rule preserves truth "upwards"
theorem localRuleInvert
    (rule : LocalRule (Lcond, Rcond) ress)
    (M : KripkeModel W)
    (w : W)
    (Δ : Finset Formula) :
    (∃res ∈ ress, (M, w) ⊨ (Δ ∪ res.1 ∪ res.2)) → (M, w) ⊨ (Δ ∪ Lcond ∪ Rcond) :=
  by
    intro satLR
    cases rule
    all_goals
      simp at *
    all_goals
      rename_i siderule
      cases siderule
      all_goals simp at *
      case neg φ =>
        aesop
      case con φ ψ =>
        aesop
      case ncon φ ψ =>
        intro f f_in
        cases f_in
        · aesop
        case inr f_def =>
          subst f_def
          cases satLR
          case inl hyp =>
            specialize hyp (~φ)
            aesop
          case inr hyp =>
            specialize hyp (~ψ)
            aesop

-- Each local rule is "complete", i.e. preserves satisfiability "upwards"
theorem localRuleCompleteness {X : TNode} {B : List TNode} :
    LocalRuleApp X B → (∃ Y ∈ B, Satisfiable Y) → Satisfiable X :=
  by
  intro lrApp
  intro sat_B
  rcases sat_B with ⟨Y, Y_in_B, sat_Y⟩
  unfold Satisfiable at sat_Y
  rcases sat_Y with ⟨W, M, w, w_sat_Y⟩
  use W, M, w
  let ⟨ress, Lcond, Rcond, rule, preconProof⟩ := lrApp
  have := localRuleInvert rule M w
  sorry

-- Lemma 11 (but rephrased to be about local tableau!?)
theorem inconsUpwards {X} {ltX : LocalTableau X} :
    (∀ en ∈ endNodesOf ⟨X, ltX⟩, Inconsistent en) → Inconsistent X :=
  by
  intro lhs
  unfold Inconsistent at *
  let leafTableaus : ∀ en ∈ endNodesOf ⟨X, ltX⟩, ClosedTableau en := fun Y YinEnds =>
    (lhs Y YinEnds).some
  constructor
  apply ClosedTableau.loc _
  · intro Y Y_in
    apply leafTableaus Y
    convert Y_in

-- Converse of Lemma 11
theorem consToEndNodes {X} {ltX : LocalTableau X} :
    Consistent X → ∃ en ∈ endNodesOf ⟨X, ltX⟩, Consistent en :=
  by
  intro consX
  unfold Consistent at *
  have claim := Not.imp consX (@inconsUpwards X ltX)
  simp at claim 
  tauto

-- maybe too atmL-specific?
def projOfConsSimpIsCons :
    ∀ {X ϕ}, Consistent X → Simple X → ~(□ϕ) ∈ X.1 ∪ X.2 → Consistent (diamondProjectTNode (Sum.inl ϕ) X) :=
  by
  intro X ϕ consX simpX notBoxPhi_in_X
  unfold Consistent at *
  unfold Inconsistent at *
  contrapose consX
  simp at *
  cases' consX with ctProj
  constructor
  sorry
  -- apply ClosedTableau.atm notBoxPhi_in_X simpX
  -- simp
  -- exact ctProj

theorem locTabEndSatThenSat {X Y} (ltX : LocalTableau X) (Y_endOf_X : Y ∈ endNodesOf ⟨X, ltX⟩) :
    Satisfiable Y → Satisfiable X := by
  intro satY
  induction ltX
  case fromRule X B lrApp next IH =>
    apply localRuleCompleteness lrApp

    rcases lrApp with ⟨ress,Lcond,Rcond,lr,Lsub,Rsub⟩
    cases lr
    all_goals sorry
    /-
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
     -/
  case fromSimple X simpX => aesop

theorem almostCompleteness : (X : TNode) → Consistent X → Satisfiable X :=
  by
  intro X consX
  sorry
  /-
  refine' if simpX : Simple X then _ else _
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
  -/

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    apply almostCompleteness X X_is_consistent
  -- use Theorem 2:
  exact correctness X

theorem singletonCompleteness : ∀ φ, Consistent ({φ},{}) ↔ Satisfiable φ :=
  by
  intro f
  have := completeness ({f},{})
  simp only [singletonSat_iff_sat] at *
  simp [Satisfiable] at *
  tauto
