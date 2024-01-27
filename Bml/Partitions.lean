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
lemma choice_property_in_image {f : α → β }{l : List α} {p : β → Prop} (p_in_image: ∃y ∈ (List.map f l), p y) : ∃x ∈ l, p (f x) :=
  by simp at p_in_image; assumption

theorem InterpolantInductionStep
  (L R : Finset Formula)
  (tab : AppLocalTableau (L,R) C)
  (subθs : ΠcLR ∈ C, PartInterpolant cLR)
  : PartInterpolant (L,R) :=
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
      let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
      use bigDis interList
      constructor
      · intro ℓ ℓ_in_inter
        have ℓ_in_subinter :  ∃θ ∈ interList, ℓ ∈ voc θ := vocOfBigDis ℓ_in_inter
        have ℓ_in_child's_inter := choice_property_in_image ℓ_in_subinter
        have ℓ_in_child : ∃c ∈ C, ℓ ∈ jvoc c :=
          Exists.elim ℓ_in_child's_inter <| λ⟨c, cinC⟩ ⟨_, linvocInter ⟩ =>
            Exists.intro c ⟨cinC, (subθs c cinC).2 |> And.left <| linvocInter⟩
        exact Exists.elim ℓ_in_child <| λcLR ⟨inC, injvoc⟩ => localRuleApp_does_not_increase_vocab ruleA cLR inC <| injvoc
      · constructor
        · intro L_and_nθ_sat
          have L_and_bigC_sat : Satisfiable ((L, R).1 ∪ {(~~bigCon (List.map (fun x => ~x) interList))}) :=
            by
              rcases L_and_nθ_sat with ⟨W, M, w, sat⟩
              have evalDis : Evaluate (M, w) (~bigDis interList) := by aesop
              rw [eval_neg_BigDis_iff_eval_bigConNeg] at evalDis
              aesop
          have L_and_nθi_sat : ∃c ∈ C.attach, Satisfiable (c.1.1 ∪ {~~(bigCon <| interList.map (~·))}) :=
            oneSidedRule_implies_child_sat_L def_ruleA def_rule L_and_bigC_sat
          have L_and_nθi_sat : ∃c ∈ C.attach, Satisfiable (c.1.1 ∪ {(bigCon <| interList.map (~·))}) :=
            Exists.elim L_and_nθi_sat <| λ⟨c, cinC⟩ ⟨inCattach, csat⟩ =>
              Exists.intro ⟨c, cinC⟩ ⟨inCattach, ((sat_double_neq_invariant (bigCon <| interList.map (~·))).mp csat)⟩
          exact Exists.elim L_and_nθi_sat <| λ⟨c, cinC⟩ ⟨_, csat⟩ =>
            have csat2 : Satisfiable <| c.1 ∪ {~ (subθs c cinC).1} :=
              bigConNeg_union_sat_down csat (subθs c cinC).1 (by simp; use c, cinC)
           (subθs c cinC).2 |> And.right |> And.left <| csat2
        . intro R_and_θ_sat
          have R_and_θi_sat : ∃θi ∈ interList, Satisfiable <| R ∪ {θi} := bigDis_union_sat_down R_and_θ_sat
          have R_and_child's_inter_sat := choice_property_in_image R_and_θi_sat
          exact Exists.elim R_and_child's_inter_sat <| λ⟨c, cinC⟩ ⟨_, csat ⟩ =>
            have R_inv_to_leftrule : c.2 = R := (oneSidedRule_preserves_other_side_L def_ruleA def_rule) c cinC
            have csat2 : Satisfiable <| c.2 ∪ {(subθs c cinC).1} := by rw[←R_inv_to_leftrule] at csat; assumption
            (subθs c cinC).2 |> And.right |> And.right <| csat2

    -- ONESIDED R: dual to the onesided L case except for dealing with ~'s in L_and_θi_Sat
    | oneSidedR orule =>
      let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
      use bigCon interList
      constructor
      · intro ℓ ℓ_in_inter
        have ℓ_in_subinter :  ∃θ ∈ interList, ℓ ∈ voc θ := vocOfBigCon ℓ_in_inter
        have ℓ_in_child's_inter := choice_property_in_image ℓ_in_subinter
        have ℓ_in_child : ∃c ∈ C, ℓ ∈ jvoc c :=
          Exists.elim ℓ_in_child's_inter <| λ⟨c, cinC⟩ ⟨_, linvocInter ⟩ =>
            Exists.intro c ⟨cinC, (subθs c cinC).2 |> And.left <| linvocInter⟩
        exact Exists.elim ℓ_in_child <| λcLR ⟨inC, injvoc⟩ => localRuleApp_does_not_increase_vocab ruleA cLR inC <| injvoc
      · constructor
        · intro L_and_nθ_sat
          have L_and_bigD_sat : Satisfiable ((L, R).1 ∪ {(bigDis (List.map (fun x => ~x) interList))}) :=
            by
              rcases L_and_nθ_sat with ⟨W, M, w, sat⟩
              have evalCon : Evaluate (M, w) (~(bigCon interList)) := by aesop
              rw [eval_negBigCon_iff_eval_bigDisNeg] at evalCon
              use W; use M; use w
              intro φ hyp
              rw [Finset.mem_union] at hyp
              cases' hyp with left right
              · apply sat; aesop
              · rw [Finset.mem_singleton] at right
                rw [right]
                assumption
          have L_and_θi_Sat : ∃nθi ∈ interList.map (~·), Satisfiable <| L ∪ {nθi} := bigDis_union_sat_down L_and_bigD_sat
          have L_and_child's_inter_sat := choice_property_in_image <| choice_property_in_image L_and_θi_Sat
          exact Exists.elim L_and_child's_inter_sat <| λ⟨c, cinC⟩ ⟨_, csat ⟩ =>
            have L_inv_to_rightrule : c.1 = L := (oneSidedRule_preserves_other_side_R def_ruleA def_rule) c cinC
            have csat2 : Satisfiable <| c.1 ∪ {~(subθs c cinC).1} := by rw[←L_inv_to_rightrule] at csat; assumption
            (subθs c cinC).2 |> And.right |> And.left <| csat2
        · intro R_and_θ_sat
          have R_and_θi_sat : ∃c ∈ C.attach, Satisfiable (c.1.2 ∪ {bigCon interList}) :=
            oneSidedRule_implies_child_sat_R def_ruleA def_rule R_and_θ_sat
          exact Exists.elim R_and_θi_sat <| λ⟨c, cinC⟩ ⟨_, csat⟩ =>
            have csat2 : Satisfiable <| c.2 ∪ {(subθs c cinC).1} :=
              bigCon_union_sat_down csat ((subθs c cinC).1) (by simp; use c, cinC)
            (subθs c cinC).2 |> And.right |> And.right <| csat2

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
  case loc C LR appTab _ endθs => exact (
    @AppLocalTableau.recOn
    (λLR C appTab => (∀E ∈ endNodesOf ⟨LR, LocalTableau.fromRule appTab⟩, PartInterpolant E) → PartInterpolant LR)
    (λLR locTab   => (∀E ∈ endNodesOf ⟨LR, locTab⟩                      , PartInterpolant E) → PartInterpolant LR)
    LR C appTab
    (by --mk (can be done by aesop but then it complains about metavariables)
      intro L R C ruleA subTabs ih endθs
      apply InterpolantInductionStep L R (AppLocalTableau.mk ruleA subTabs)
      intro cLR c_in_C
      apply ih cLR c_in_C
      intro eLR e_in_end
      apply endθs
      aesop
    )
    (by aesop) --fromRule
    (by aesop) --fromSimple
    <| endθs
    )
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
