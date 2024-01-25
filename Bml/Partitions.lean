-- PARTITIONS

import Bml.Syntax
import Bml.Tableau
import Bml.Semantics
import Bml.Soundness
import Bml.Vocabulary
import Bml.bigConDis

open HasVocabulary HasSat

def Partition :=
  Finset Formula × Finset Formula

-- Definition 24

def PartInterpolant (LR : TNode) (θ : Formula) :=
  voc θ ⊆ jvoc LR ∧ ¬Satisfiable (LR.1 ∪ {~θ}) ∧ ¬Satisfiable (LR.2 ∪ {θ})

-- choice_property_in_image: slightly problematic
-- use let x : t := mapImageProp X
-- complains unless you specify all implicit arguments
-- for now: use x := mapImageProp, provide t in a comment
lemma choice_property_in_image {f : α → β }{l : List α} {p : β → Prop} (p_in_image: ∃y ∈ (List.map f l), p y) : ∃x ∈ l, p (f x) :=
  by simp at p_in_image; assumption

theorem InterpolantInductionStep
  (L R : Finset Formula)
  (tab : AppLocalTableau (L,R) C)
  (subInterpolants : Π cLR ∈ C, Formula)
  (hsubInterpolants : Π cLRP ∈ C.attach, PartInterpolant cLRP.val (subInterpolants cLRP.val cLRP.property))
  : (∃θ : Formula, PartInterpolant (L,R) θ) :=
  by
    -- UNPACKING TERMS
    match v : tab with
    | @AppLocalTableau.mk _ _ C ruleA subTabs =>
    match def_ruleA : ruleA with
    | @LocalRuleApp.mk _ _ _ ress Lcond Rcond rule hC preproof =>

    -- DISTINCTION ON LOCALRULE USED
    cases def_rule : rule with

    -- ONESIDED L
    | oneSidedL orule =>
      let interList :=  (C.attach).map $ λcInC => subInterpolants cInC.1 cInC.2
      use bigDis interList
      constructor
      · intro ℓ ℓ_in_inter
        have ℓ_in_subinter :  ∃θ ∈ interList, ℓ ∈ voc θ := vocOfBigDis ℓ_in_inter
        have ℓ_in_child's_inter := choice_property_in_image ℓ_in_subinter
        have ℓ_in_child : ∃c ∈ C, ℓ ∈ jvoc c :=
          Exists.elim ℓ_in_child's_inter <| λ⟨c, cinC⟩ ⟨inCattach, linvocInter ⟩ =>
            Exists.intro c ⟨cinC, hsubInterpolants ⟨c, cinC⟩ inCattach |> And.left <| linvocInter⟩
        exact Exists.elim ℓ_in_child <| λcLR ⟨inC, injvoc⟩ => localRuleApp_does_not_increase_vocab ruleA cLR inC <| injvoc
      · constructor
        · intro L_and_nθ_sat
          rw[negBigDis_eq_bigConNeg] at L_and_nθ_sat
          have L_and_nθi_sat : ∃c ∈ C.attach, Satisfiable (c.1.1 ∪ {~~(bigCon <| interList.map (~·))}) :=
            oneSidedRule_implies_child_sat_L def_ruleA def_rule L_and_nθ_sat
          have L_and_nθi_sat : ∃c ∈ C.attach, Satisfiable (c.1.1 ∪ {(bigCon <| interList.map (~·))}) :=
            Exists.elim L_and_nθi_sat <| λ⟨c, cinC⟩ ⟨inCattach, csat⟩ =>
              Exists.intro ⟨c, cinC⟩ ⟨inCattach, ((sat_double_neq_invariant (bigCon <| interList.map (~·))).mp csat)⟩
          exact Exists.elim L_and_nθi_sat <| λ⟨c, cinC⟩ ⟨inCattach, csat⟩ =>
            have csat2 : Satisfiable <| c.1 ∪ {~ subInterpolants c cinC} :=
              bigConNeg_union_sat_down csat (subInterpolants c cinC) (by simp; use c, cinC)
            hsubInterpolants ⟨c, cinC⟩ inCattach |> And.right |> And.left <| csat2
        . intro R_and_θ_sat
          have R_and_θi_sat : ∃θi ∈ interList, Satisfiable <| R ∪ {θi} := bigDis_union_sat_down R_and_θ_sat
          have R_and_child's_inter_sat := choice_property_in_image R_and_θi_sat
          exact Exists.elim R_and_child's_inter_sat <| λ⟨c, cinC⟩ ⟨inCattach, csat ⟩ =>
            have R_inv_to_leftrule : c.2 = R := (oneSidedRule_preserves_other_side_L def_ruleA def_rule) c cinC
            have csat2 : Satisfiable <| c.2 ∪ {subInterpolants c cinC} := by rw[←R_inv_to_leftrule] at csat; assumption
            hsubInterpolants ⟨c, cinC⟩ inCattach |> And.right |> And.right <| csat2

    -- ONESIDED R: dual to the onesided L case except for dealing with ~'s in L_and_θi_Sat
    | oneSidedR orule =>
      let interList :=  (C.attach).map $ λcInC => subInterpolants cInC.1 cInC.2
      use bigCon interList
      constructor
      · intro ℓ ℓ_in_inter
        have ℓ_in_subinter :  ∃θ ∈ interList, ℓ ∈ voc θ := vocOfBigCon ℓ_in_inter
        have ℓ_in_child's_inter := choice_property_in_image ℓ_in_subinter
        have ℓ_in_child : ∃c ∈ C, ℓ ∈ jvoc c :=
          Exists.elim ℓ_in_child's_inter <| λ⟨c, cinC⟩ ⟨inCattach, linvocInter ⟩ =>
            Exists.intro c ⟨cinC, hsubInterpolants ⟨c, cinC⟩ inCattach |> And.left <| linvocInter⟩
        exact Exists.elim ℓ_in_child <| λcLR ⟨inC, injvoc⟩ => localRuleApp_does_not_increase_vocab ruleA cLR inC <| injvoc
      · constructor
        · intro L_and_nθ_sat
          rw[negBigCon_eq_bigDisNeg] at L_and_nθ_sat
          have L_and_θi_Sat : ∃nθi ∈ interList.map (~·), Satisfiable <| L ∪ {nθi} := bigDis_union_sat_down L_and_nθ_sat
          have L_and_child's_inter_sat := choice_property_in_image <| choice_property_in_image L_and_θi_Sat
          exact Exists.elim L_and_child's_inter_sat <| λ⟨c, cinC⟩ ⟨inCattach, csat ⟩ =>
            have L_inv_to_rightrule : c.1 = L := (oneSidedRule_preserves_other_side_R def_ruleA def_rule) c cinC
            have csat2 : Satisfiable <| c.1 ∪ {~subInterpolants c cinC} := by rw[←L_inv_to_rightrule] at csat; assumption
            hsubInterpolants ⟨c, cinC⟩ inCattach |> And.right |> And.left <| csat2
        · intro R_and_θ_sat
          have R_and_θi_sat : ∃c ∈ C.attach, Satisfiable (c.1.2 ∪ {bigCon interList}) :=
            oneSidedRule_implies_child_sat_R def_ruleA def_rule R_and_θ_sat
          exact Exists.elim R_and_θi_sat <| λ⟨c, cinC⟩ ⟨inCattach, csat⟩ =>
            have csat2 : Satisfiable <| c.2 ∪ {subInterpolants c cinC} :=
              bigCon_union_sat_down csat (subInterpolants c cinC) (by simp; use c, cinC)
            hsubInterpolants ⟨c, cinC⟩ inCattach |> And.right |> And.right <| csat2

    -- LRNEG L
    | LRnegL φ =>
      use φ
      constructor
      · intro ℓ ℓinφ
        simp at ℓinφ; simp
        constructor
        · use  φ; constructor <;> aesop
        · use ~φ; constructor <;> aesop
      · constructor <;> apply negation_not_cosatisfiable φ <;> aesop

    -- LRNEG R: perfectly dual to LRNEG l
    | LRnegR φ =>
      use ~φ
      constructor
      · intro ℓ ℓinφ
        simp at ℓinφ; simp
        constructor
        · use ~φ; constructor <;> aesop
        · use  φ; constructor <;> aesop
      · constructor
        · apply negation_not_cosatisfiable (~φ) <;> aesop
        . apply negation_not_cosatisfiable (φ)  <;> aesop




theorem vocProj (X) : voc (projection X) ⊆ voc X :=
  by
  simp
  intro ϕ phi_in_proj
  rw [proj] at phi_in_proj
  intro a aInVocPhi
  simp
  tauto

theorem projUnion {X Y} : projection (X ∪ Y) = projection X ∪ projection Y :=
  by
  ext1
  rw [proj]
  simp
  rw [proj]
  rw [proj]

open HasLength

-- tableau interpolation -- IDEA: similar to almostCompleteness
-- part of this is part of Lemma 15
theorem tabToInt {X} (ctX : ClosedTableau X) : ∃ θ, PartInterpolant X θ :=
  by
  induction ctX
  case loc C LR ltX next IH =>
    have nextLtAndInter :
      ∃ ltX : LocalTableau X,
        ∀ Y ∈ endNodesOf ⟨X, ltX⟩, ∃ θ, PartInterpolant Y θ :=
      by
      sorry
      /-
      use ltX
      intro Y1 Y2 y_is_endOfX
      specialize next (Y1 ∪ Y2) y_is_endOfX
      exact IH (Y1 ∪ Y2) y_is_endOfX Y1 Y2 (refl _)
      -/
    sorry -- exact localTabToInt _ X (refl _) defX nextLtAndInter
  case atmL X ϕ notBoxPhi_in_X simpleX ctProjNotPhi IH =>
      simp at *
      sorry
      /-
      let newX1 := projection X1 ∪ {~ϕ}
      let newX2 := projection X2
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ} := by rw [projUnion]; ext1; simp
      rw [← yclaim] at ctProjNotPhi
      have nextInt : ∃ θ, PartInterpolant newX1 newX2 θ := IH newX1 newX2 (by rw [yclaim]; simp)
      rcases nextInt with ⟨θ, vocSub, unsat1, unsat2⟩
      use~(□~θ)
      repeat' constructor
      -- it remains to show the three properties of the interpolant
      · change voc θ ⊆ voc X1 ∩ voc X2
        have inc1 : voc newX1 ⊆ voc X1 := by
          intro a aIn; simp at *
          cases' aIn with a_in_vocPhi other
          · use~(□ϕ); tauto
          · rcases other with ⟨ψ, psi_in_projX1, _⟩
            use□ψ; change □ψ ∈ X1 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        have inc2 : voc newX2 ⊆ voc X2 := by
          intro a aIn; simp at *
          rcases aIn with ⟨ψ, psi_in_projX2⟩
          · use□ψ; change □ψ ∈ X2 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        rw [Finset.subset_inter_iff] at vocSub
        rcases vocSub with ⟨vocTh_in_X1, vocTh_in_X2⟩
        rw [Finset.subset_inter_iff]
        tauto
      all_goals unfold Satisfiable at *
      case left notBoxPhi_in_X =>
        by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat1
        use W, M
        --- we use ~□ϕ to get a different world:
        let othersat := sat (~(□ϕ)) (by simp; apply notBoxPhi_in_X)
        unfold Evaluate at othersat
        simp at othersat
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX1
        simp at psi_in_newX1
        cases psi_in_newX1
        case inl psi_in_newX1 =>
          subst psi_in_newX1; specialize sat (~~(□~θ)); simp at *;
          exact v_not_phi
        case inr psi_in_newX1 =>
          cases' psi_in_newX1 with psi_in_newX1 psi_in
          · rw [psi_in_newX1]
            specialize sat (~(~(□(~θ))))
            simp at sat
            simp
            exact sat v rel_w_v
          · rw [proj] at psi_in
            specialize sat (□ψ) (by simp; exact psi_in)
            simp at sat
            exact sat v rel_w_v
      · by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat2
        use W, M
        --- we use ~□~θ to get a different world:
        let othersat := sat (~(□~θ)) (by simp)
        unfold Evaluate at othersat
        simp at othersat
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX2
        simp at psi_in_newX2
        cases' psi_in_newX2 with psi_is_theta psi_in_projX2
        · subst psi_is_theta; assumption
        · rw [proj] at psi_in_projX2 ; specialize sat (□ψ); apply sat; simp; assumption; assumption
        -/
  case atmR X ϕ notBoxPhi_in_X simpleX ctProjNotPhi IH =>
      sorry
      /-
      -- case ~□ϕ ∈ X2
      let newX1 := projection X1
      let newX2 := projection X2 ∪ {~ϕ}
      ---- what follows is *based* on copying the previous case ----
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ} := by rw [projUnion]; ext1; simp
      rw [← yclaim] at ctProjNotPhi
      have nextInt : ∃ θ, PartInterpolant newX1 newX2 θ := IH newX1 newX2 (by rw [yclaim]; simp)
      rcases nextInt with ⟨θ, vocSub, unsat1, unsat2⟩
      use□θ
      -- !!
      repeat' constructor
      -- it remains to show the three properties of the interpolant
      · change voc θ ⊆ voc X1 ∩ voc X2
        have inc1 : voc newX2 ⊆ voc X2 := by
          intro a aIn; simp at *
          cases' aIn with a_in_vocPhi other
          · use~(□ϕ); tauto
          · rcases other with ⟨ψ, psi_in_projX2, _⟩
            use□ψ; change □ψ ∈ X2 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        have inc2 : voc newX1 ⊆ voc X1 := by
          intro a aIn; simp at *
          rcases aIn with ⟨ψ, psi_in_projX1⟩
          · use□ψ; change □ψ ∈ X1 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        rw [Finset.subset_inter_iff] at vocSub
        rcases vocSub with ⟨vocTh_in_X1, vocTh_in_X2⟩
        rw [Finset.subset_inter_iff]
        tauto
      all_goals unfold Satisfiable at *
      · by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat1
        use W, M
        --- we use ~□θ to get a different world:
        let othersat := sat (~(□θ)) (by simp)
        unfold Evaluate at othersat
        simp at othersat
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX1
        simp at psi_in_newX1
        cases' psi_in_newX1 with psi_in_newX1 psi_in_newX1
        · subst psi_in_newX1; specialize sat (~(□θ)); simp at sat; tauto
        · rw [proj] at psi_in_newX1 ; specialize sat (□ψ); apply sat; simp; assumption; assumption
      · by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat2
        use W, M
        --- we use ~□ϕ to get a different world:
        let othersat := sat (~(□ϕ)) (by simp; assumption)
        unfold Evaluate at othersat
        simp at othersat
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX2
        simp at psi_in_newX2
        cases' psi_in_newX2 with psi_is_notPhi psi_in_newX2
        · subst psi_is_notPhi; simp; assumption
        cases' psi_in_newX2
        case inl psi_is_theta =>
          subst psi_is_theta
          specialize sat (□ψ) (by simp)
          simp at sat
          exact sat v rel_w_v
        case inr psi_in_newX2 =>
          rw [proj] at psi_in_newX2 ; specialize sat (□ψ); simp at sat
          apply sat; right; assumption; assumption
      -/
