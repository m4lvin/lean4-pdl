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

def isPartInterpolant (LR : TNode) (θ : Formula) :=
  voc θ ⊆ jvoc LR ∧ ¬Satisfiable (LR.1 ∪ {~θ}) ∧ ¬Satisfiable (LR.2 ∪ {θ})

def PartInterpolant (LR : TNode) := Subtype <| isPartInterpolant LR

-- choice_property_in_image: slightly problematic
-- use let x : t := mapImageProp X
-- complains unless you specify all implicit arguments
-- for now: use x := mapImageProp, provide t in a comment
theorem choice_property_in_image {f : α → β }{l : List α} {p : β → Prop} (p_in_image: ∃y ∈ (List.map f l), p y) : ∃x ∈ l, p (f x) :=
  by simp at p_in_image; assumption

theorem InterpolantInductionStep
  (L R : Finset Formula)
  (ruleA : LocalRuleApp (L,R) C)
  (subθs : Π c ∈ C, PartInterpolant c)
  : PartInterpolant (L,R) :=
  by
    -- UNPACKING TERMS
    match def_ruleA : ruleA with
    | @LocalRuleApp.mk _ _ _ ress Lcond Rcond rule hC preproof =>

    -- DISTINCTION ON LOCALRULE USED
    cases def_rule : rule with

    -- ONESIDED L
    | oneSidedL orule =>
      let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
      use bigDis interList
      constructor
      · intro ℓ ℓ_in_inter
        let ⟨⟨c,c_in_C⟩, _, ℓ_in_c'θ⟩ := choice_property_in_image <| vocOfBigDis ℓ_in_inter
        have ℓ_in_c : ℓ ∈ jvoc c := (subθs c c_in_C).2 |> And.left <| ℓ_in_c'θ
        exact localRuleApp_does_not_increase_vocab ruleA c c_in_C <| ℓ_in_c

      · constructor
        · intro L_and_nθ_sat
          have L_and_bigC_sat : Satisfiable ((L, R).1 ∪ {(~~bigCon (List.map (fun x => ~x) interList))}) := by
            rcases L_and_nθ_sat with ⟨W, M, w, MWsat⟩
            have evalDis : Evaluate (M, w) (~bigDis interList) := MWsat (~bigDis interList) (by simp)
            rw [eval_neg_BigDis_iff_eval_bigConNeg] at evalDis
            use W, M, w
            simp
            constructor
            · simp at evalDis; apply evalDis
            · intro φ φ_in_L; apply MWsat; simp[φ_in_L]
          let ⟨⟨c,c_in_C⟩, _, sat_c_nnθ⟩ := oneSidedRule_implies_child_sat_L def_ruleA def_rule L_and_bigC_sat
          have sat_c_θ : Satisfiable (c.1 ∪ {(bigCon <| interList.map (~·))}) :=
             (sat_double_neq_invariant (bigCon <| interList.map (~·))).mp sat_c_nnθ
          have sat_c_c'sθ : Satisfiable <| c.1 ∪ {~ (subθs c c_in_C).1} :=
            bigConNeg_union_sat_down sat_c_θ (subθs c c_in_C).1 (by simp; use c, c_in_C)
          exact (subθs c c_in_C).2 |> And.right |> And.left <| sat_c_c'sθ

        . intro R_and_θ_sat
          have ⟨⟨c,c_in_C⟩, _, sat_cθ⟩ := choice_property_in_image <| bigDis_union_sat_down R_and_θ_sat
          have cR_eq_R : c.2 = R := (oneSidedRule_preserves_other_side_L def_ruleA def_rule) c c_in_C
          rw[←cR_eq_R] at sat_cθ
          exact (subθs c c_in_C).2 |> And.right |> And.right <| sat_cθ

    -- ONESIDED R: dual to ONESIDED L
    | oneSidedR orule =>
      let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
      use bigCon interList
      constructor
      · intro ℓ ℓ_in_inter
        let ⟨⟨c,c_in_C⟩, _, ℓ_in_c'θ⟩ := choice_property_in_image <| vocOfBigCon ℓ_in_inter
        have ℓ_in_c : ℓ ∈ jvoc c := (subθs c c_in_C).2 |> And.left <| ℓ_in_c'θ
        exact localRuleApp_does_not_increase_vocab ruleA c c_in_C <| ℓ_in_c

      · constructor
        · intro L_and_nθ_sat
          have L_and_bigD_sat : Satisfiable ((L, R).1 ∪ {(bigDis (List.map (fun x => ~x) interList))}) := by
            rcases L_and_nθ_sat with ⟨W, M, w, MWsat⟩
            have evalCon : Evaluate (M, w) (~(bigCon interList)) := MWsat (~bigCon interList) (by simp)
            rw [eval_negBigCon_iff_eval_bigDisNeg] at evalCon
            use W, M, w
            simp
            constructor
            · simp at evalCon; apply evalCon
            · intro φ φ_in_L; apply MWsat; simp[φ_in_L]
          let ⟨⟨c,c_in_C⟩,_,sat_c'sθ⟩ := choice_property_in_image <| choice_property_in_image <| bigDis_union_sat_down L_and_bigD_sat
          have L_inv_to_rightrule : c.1 = L := (oneSidedRule_preserves_other_side_R def_ruleA def_rule) c c_in_C
          rw[←L_inv_to_rightrule] at sat_c'sθ
          exact (subθs c c_in_C).2 |> And.right |> And.left <| sat_c'sθ

        · intro R_and_θ_sat
          let ⟨⟨c,c_in_C⟩,_,sat_c_θ⟩ := oneSidedRule_implies_child_sat_R def_ruleA def_rule R_and_θ_sat
          have sat_c'sθ : Satisfiable <| c.2 ∪ {(subθs c c_in_C).1} :=
              bigCon_union_sat_down sat_c_θ ((subθs c c_in_C).1) (by simp; use c, c_in_C)
          exact (subθs c c_in_C).2 |> And.right |> And.right <| sat_c'sθ

    -- LRNEG L
    | LRnegL φ =>
      use φ
      constructor
      · intro ℓ ℓinφ
        simp at ℓinφ; simp
        constructor
        · use  φ; constructor
          · exact preproof.left <| Finset.mem_singleton.mpr rfl
          . exact ℓinφ
        · use ~φ; constructor
          · exact preproof.right <| Finset.mem_singleton.mpr rfl
          . exact ℓinφ

      · constructor <;> apply negation_not_cosatisfiable φ <;> simp
        · apply Or.intro_right; exact preproof.left <| Finset.mem_singleton.mpr rfl
        · exact preproof.right <| Finset.mem_singleton.mpr rfl

    -- LRNEG R: dual to LRNEG l
    | LRnegR φ =>
      use ~φ
      constructor
      · intro ℓ ℓinφ
        simp at ℓinφ; simp
        constructor
        · use  ~φ; constructor
          · exact preproof.left <| Finset.mem_singleton.mpr rfl
          . exact ℓinφ
        · use φ; constructor
          · exact preproof.right <| Finset.mem_singleton.mpr rfl
          . exact ℓinφ

      · constructor
        · apply negation_not_cosatisfiable (~φ) <;> simp
          apply Or.intro_right; exact preproof.left <| Finset.mem_singleton.mpr rfl
        · apply negation_not_cosatisfiable φ <;> simp
          apply Or.intro_right; exact preproof.right <| Finset.mem_singleton.mpr rfl

-- Four (annoyingly similar) helper theorems for the modal cases in tabToInt.

theorem projection_reflects_unsat_L_L
    {LR : TNode} {φ : Formula}
    (nBoxφ_in_L : ~(□φ) ∈ LR.1)
    (notSatNotTheta : ¬Satisfiable ((diamondProjectTNode (Sum.inl φ) LR).1 ∪ {~θ}))
    : ¬Satisfiable (LR.1 ∪ {□~θ}) :=
  by
  rintro ⟨W,M,w,sat⟩
  have := sat (~(□φ)) (by simp; tauto)
  simp at this
  rcases this with ⟨v,w_v,v_nPhi⟩
  absurd notSatNotTheta
  use W, M, v
  intro f f_in
  simp at f_in
  cases f_in
  case inl => aesop
  case inr f_in =>
    have := sat (□f)
    let (L, R) := LR
    simp [diamondProjectTNode] at f_in
    cases f_in
    case inl => aesop
    case inr hyp => rw [proj] at hyp; aesop

theorem projection_reflects_unsat_L_R
    {LR : TNode} {φ : Formula}
    (nBoxφ_in_L : ~(□φ) ∈ LR.1)
    (notSatNotTheta : ¬Satisfiable ((diamondProjectTNode (Sum.inl φ) LR).2 ∪ {θ}))
    : ¬Satisfiable (LR.2 ∪ {~(□~θ)}) :=
  by
  rintro ⟨W,M,w,sat⟩
  have := sat (~(□~θ)) (by simp)
  simp at this
  rcases this with ⟨v,w_v,v_nPhi⟩
  absurd notSatNotTheta
  use W, M, v
  intro f f_in
  simp at f_in
  cases f_in
  case inl => aesop
  case inr f_in =>
    have := sat (□f)
    let (L, R) := LR
    simp [diamondProjectTNode] at f_in
    rw [proj] at f_in; aesop

theorem projection_reflects_unsat_R_L
    {LR : TNode} {φ : Formula}
    (nBoxφ_in_R : ~(□φ) ∈ LR.2)
    (notSatNotTheta : ¬Satisfiable ((diamondProjectTNode (Sum.inr φ) LR).1 ∪ {~θ}))
    : ¬Satisfiable (LR.1 ∪ {~(□θ)}) :=
  by
  rintro ⟨W,M,w,sat⟩
  have := sat (~(□θ)) (by simp)
  simp at this
  rcases this with ⟨v,w_v,v_nPhi⟩
  absurd notSatNotTheta
  use W, M, v
  intro f f_in
  simp at f_in
  cases f_in
  case inl => aesop
  case inr f_in =>
    have := sat (□f)
    let (L, R) := LR
    simp [diamondProjectTNode] at f_in
    rw [proj] at f_in
    aesop

theorem projection_reflects_unsat_R_R
    {LR : TNode} {φ : Formula}
    (nBoxφ_in_R : ~(□φ) ∈ LR.2)
    (notSatNotTheta : ¬Satisfiable ((diamondProjectTNode (Sum.inr φ) LR).2 ∪ {θ}))
    : ¬Satisfiable (LR.2 ∪ {□θ}) :=
  by
  rintro ⟨W,M,w,sat⟩
  have := sat (~(□φ)) (by simp; tauto)
  simp at this
  rcases this with ⟨v,w_v,v_nPhi⟩
  absurd notSatNotTheta
  use W, M, v
  intro f f_in
  simp at f_in
  cases f_in
  case inl => aesop
  case inr f_in =>
    have := sat (□f)
    let (L, R) := LR
    simp [diamondProjectTNode] at f_in
    rw [proj] at f_in
    cases f_in
    case inl hyp => subst hyp; simp; exact v_nPhi
    case inr => simp at this; apply this (by right; assumption) v w_v

theorem tabToInt {LR : TNode} (tab : ClosedTableau LR)
: PartInterpolant LR := by
  induction tab
  case loc LR lt next nextθs =>
    -- Term-mode version below was broken after removal of AppLocalTableau.
    induction lt
    case fromRule WhatIsThis LR C lrApp subTabs IH =>
      apply InterpolantInductionStep LR.1 LR.2 lrApp
      intro cLR c_in_C
      apply IH cLR c_in_C
      · intro eLR e_in_end
        apply next
        aesop
      · intro Y Y_in
        apply nextθs
        aesop
    case fromSimple =>
      aesop

  case atmL LR φ nBoxφ_in_L simple_LR cTabProj pθ =>
    use ~(□~pθ.val) -- modal rule on the right: use diamond of interpolant!
    constructor
    · -- voc property
      intro ℓ ℓ_in_θ
      exact diamondproj_does_not_increase_vocab_L nBoxφ_in_L (pθ.property.left ℓ_in_θ)
    · constructor -- implication property
      · rw [sat_double_neq_invariant]
        exact projection_reflects_unsat_L_L nBoxφ_in_L pθ.2.2.1
      · exact projection_reflects_unsat_L_R nBoxφ_in_L pθ.2.2.2

  -- dual to atmL
  case atmR LR φ nBoxφ_in_R simple_LR cTabProj pθ =>
    use (□pθ.val) -- modal rule on the right: use box of interpolant!
    constructor
    · -- voc property
      intro ℓ ℓ_in_θ
      exact diamondproj_does_not_increase_vocab_R nBoxφ_in_R (pθ.property.left ℓ_in_θ)
    · constructor -- implication property
      · exact projection_reflects_unsat_R_L nBoxφ_in_R pθ.2.2.1
      · exact projection_reflects_unsat_R_R nBoxφ_in_R pθ.2.2.2
