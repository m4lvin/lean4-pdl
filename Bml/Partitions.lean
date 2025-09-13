-- PARTITIONS

import Bml.Tableau
import Bml.Soundness
import Bml.bigConDis

open HasVocabulary HasSat

def Partition :=
  Finset Formula × Finset Formula

/-- MB Definition 24 -/
def isPartInterpolant (LR : TNode) (θ : Formula) :=
  voc θ ⊆ jvoc LR ∧ ¬Satisfiable (LR.1 ∪ {~θ}) ∧ ¬Satisfiable (LR.2 ∪ {θ})

def PartInterpolant (LR : TNode) := Subtype <| isPartInterpolant LR

-- choice_property_in_image: slightly problematic
-- use let x : t := mapImageProp X
-- complains unless you specify all implicit arguments
-- for now: use x := mapImageProp, provide t in a comment
theorem choice_property_in_image {f : α → β} {l : List α} {p : β → Prop}
    (p_in_image : ∃ y ∈ (l.map f), p y) : ∃ x ∈ l, p (f x) :=
  by simp at p_in_image; assumption

def InterpolantInductionStep
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
            bigConNeg_union_sat_down sat_c_θ (subθs c c_in_C).1 (by simp (config := {zetaDelta := true}); use c, c_in_C)
          exact (subθs c c_in_C).2 |> And.right |> And.left <| sat_c_c'sθ

        · intro R_and_θ_sat
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
              bigCon_union_sat_down sat_c_θ ((subθs c c_in_C).1) (by simp (config := {zetaDelta := true}); use c, c_in_C)
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
          · exact ℓinφ
        · use ~φ; constructor
          · exact preproof.right <| Finset.mem_singleton.mpr rfl
          · exact ℓinφ

      · constructor <;> apply negation_not_cosatisfiable φ <;> simp only [union_singleton_is_insert, Finset.mem_insert, true_or]
        · apply Or.intro_right; exact preproof.left <| Finset.mem_singleton.mpr rfl
        · apply Or.intro_right; exact preproof.right <| Finset.mem_singleton.mpr rfl

    -- LRNEG R: dual to LRNEG l
    | LRnegR φ =>
      use ~φ
      constructor
      · intro ℓ ℓinφ
        simp at ℓinφ; simp
        constructor
        · use  ~φ; constructor
          · exact preproof.left <| Finset.mem_singleton.mpr rfl
          · exact ℓinφ
        · use φ; constructor
          · exact preproof.right <| Finset.mem_singleton.mpr rfl
          · exact ℓinφ

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

open HasLength

def LocalTableau.length : LocalTableau LR → Nat
  | (@LocalTableau.fromRule _ C _ next) =>
      1 + (C.attach.map (fun ⟨c,c_in⟩ => (next c c_in).length )).sum
  | (LocalTableau.fromSimple _) => 1

def ClosedTableau.length : ClosedTableau LR → Nat
  | (ClosedTableau.loc lt next) =>
      1 + lt.length + ((endNodesOf ⟨LR, lt⟩).attach.map (fun ⟨c, c_in_ends⟩ => (next c c_in_ends).length)).sum
  | (@ClosedTableau.atmL LR _ _ _ cTabProj) => 1 + cTabProj.length
  | (@ClosedTableau.atmR LR _ _ _ cTabProj) => 1 + cTabProj.length

-- TODO: move to Tableau.lean
theorem endNodeOfChildIsEndNode
  lrApp
  (subTabs : (c : TNode) → c ∈ C → LocalTableau c)
  (E_in:  E ∈ endNodesOf ⟨x, subTabs x h⟩)
  : E ∈ endNodesOf ⟨LR, @LocalTableau.fromRule LR C lrApp subTabs⟩
  := by
  unfold endNodesOf
  simp_all only [List.mem_flatten, List.mem_map, List.mem_attach, true_and, Subtype.exists]
  refine ⟨endNodesOf ⟨x, subTabs x h⟩, ⟨x, h, by simp⟩ , E_in⟩

def childNext
  (subTabs : (c : TNode) → c ∈ C → LocalTableau c)
  (next : (Y : TNode) → Y ∈ endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩ → ClosedTableau Y)
  (cLR : TNode)
  (c_in_C : cLR ∈ C)
  :
  (Y : TNode) → Y ∈ endNodesOf ⟨cLR, subTabs cLR c_in_C⟩ → ClosedTableau Y := by
  intro Y Y_in
  exact next Y (endNodeOfChildIsEndNode lrApp subTabs Y_in)

theorem childNext_eq
  (subTabs : (c : TNode) → c ∈ C → LocalTableau c)
  (next : (Y : TNode) → Y ∈ endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩ → ClosedTableau Y)
  (cLR : TNode)
  (c_in_C : cLR ∈ C)
  Y
  (Y_in : Y ∈ endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩)
  (Y_in_child : Y ∈ endNodesOf ⟨cLR, subTabs cLR c_in_C⟩)
  : childNext subTabs next cLR c_in_C Y Y_in_child = next Y Y_in := by
  simp [childNext]

theorem elem_lt_map_sum {x : α} {l : List α}
    (h : x ∈ l) (f : α → Nat) : f x ≤ (l.map f).sum := by
  induction l
  · simp_all
  case cons k l IH =>
    simp_all
    cases h
    · simp_all
    case inr x_in =>
      specialize IH x_in
      linarith

theorem endNodesOfChildAreEndNodes
    (subTabs : (c : TNode) → c ∈ C → LocalTableau c)
    (c_in_C : cLR ∈ C)
    lrApp
    : (endNodesOf ⟨cLR, subTabs cLR c_in_C⟩)
    ⊆ (endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩) := by
  intro x x_in
  apply endNodeOfChildIsEndNode lrApp subTabs x_in

theorem endNodesOfChildSublistEndNodes
    (subTabs : (c : TNode) → c ∈ C → LocalTableau c)
    (c_in_C : cLR ∈ C)
    lrApp
    : (endNodesOf ⟨cLR, subTabs cLR c_in_C⟩).Sublist (endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩) := by
  simp_all only [lrEndNodes]
  apply List.sublist_flatten_of_mem
  simp_all only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  use cLR, c_in_C

open List

-- Thanks to Daniel Weber on Zulip!
lemma Sublist.pmap {α β : Type*} {p p2 : α → Prop}
    {f : (a : α) → p a → β} {g : (a : α) → p2 a → β}
    {xs ys : List α} {H : ∀ a ∈ xs, p a} {H2 : ∀ a ∈ ys, p2 a}
    (h : xs.Sublist ys)
    (agree : ∀ x, (h1 : p x) → (h2 : p2 x) → f x h1 = g x h2):
    (xs.pmap f H).Sublist (ys.pmap g H2) := by
  induction h with
  | slnil => simp
  | cons _ _ h =>
    apply Sublist.cons
    apply h
  | cons₂ _ _ h =>
    rw [pmap.eq_2, pmap.eq_2]
    convert Sublist.cons₂ ..
    apply (agree ..).symm
    apply h

theorem map_sum_le_map_sum
    (xs ys : List α)
    (h : xs.Sublist ys) -- NOTE: subset is not enough!
    (f : { x // x ∈ xs } → Nat)
    (g : { x // x ∈ ys } → Nat)
    (agree : ∀ x ∈ xs.attach, ∀ x_in_ys, f x = g ⟨x.1, x_in_ys⟩)
    : (List.map f xs.attach).sum ≤ (List.map g ys.attach).sum := by
  have : (List.map f xs.attach).Sublist (List.map g ys.attach) := by
    let ff := fun a ha => f ⟨a,ha⟩
    let gg := fun a ha => g ⟨a,ha⟩
    -- FIXME: There is probably a cleaner way to do this.
    have : (xs.pmap ff _).Sublist (ys.pmap gg _) :=
      @Sublist.pmap _ _ _ _ ff gg xs ys (by simp) (by simp) h (fun x h1 h2 => by unfold ff; unfold gg; simp_all)
    rw [List.pmap_eq_map_attach] at this
    rw [List.pmap_eq_map_attach] at this
    aesop
  apply List.Sublist.sum_le_sum
  · exact this
  · simp

theorem childNext_lt
    (subTabs : (c : TNode) → c ∈ C → LocalTableau c)
    (next : (Y : TNode) → Y ∈ endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩ → ClosedTableau Y)
    (cLR : TNode)
    (c_in_C : cLR ∈ C)
    :
    (ClosedTableau.loc (subTabs cLR c_in_C) (childNext subTabs next cLR c_in_C)).length
    <
    (ClosedTableau.loc (LocalTableau.fromRule lrApp subTabs) next).length := by
  have := childNext_eq subTabs next cLR c_in_C
  simp_all [ClosedTableau.length, LocalTableau.length]
  have : (subTabs cLR c_in_C).length ≤ (List.map (fun x => (subTabs x.1 x.2).length) C.attach).sum := by
    have := List.mem_attach _ ⟨_, c_in_C⟩
    have := elem_lt_map_sum this (fun x => (subTabs x.1 x.2).length)
    linarith
  have :
      (List.map (fun x => (childNext subTabs next cLR c_in_C x.1 x.2).length) (endNodesOf ⟨cLR, subTabs cLR c_in_C⟩).attach).sum
      ≤
      (List.map (fun x => (next x.1 x.2).length) (endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩).attach).sum := by
    apply map_sum_le_map_sum
      (endNodesOf ⟨cLR, subTabs cLR c_in_C⟩)
      (endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩)
      (endNodesOfChildSublistEndNodes subTabs c_in_C lrApp)
    intro _ _ _
    rw [childNext_eq]
  linarith

theorem simple_lt
  (isSimple : Simple LR)
  (next : (Y : TNode) → Y ∈ endNodesOf ⟨LR, LocalTableau.fromSimple isSimple⟩ → ClosedTableau Y)
  (h : cLR ∈ endNodesOf ⟨LR, LocalTableau.fromSimple isSimple⟩)
  :
  (next cLR h).length < (ClosedTableau.loc (LocalTableau.fromSimple isSimple) next).length :=  by
  simp_all [ClosedTableau.length, LocalTableau.length]
  have := List.mem_attach _ ⟨_, h⟩
  have := elem_lt_map_sum this (fun x => (next x.1 x.2).length)
  linarith

-- NOTE for doing this in PDL some day, it seems better to split things:
-- first do only the definition of the interpolant and then the proof that it is one.
def tabToInt {LR : TNode} (tab : ClosedTableau LR) : PartInterpolant LR :=
  match t_def : tab with
  | (ClosedTableau.loc lt next) => by
    match lt with
    | (@LocalTableau.fromRule _ C lrApp subTabs) =>
      apply InterpolantInductionStep LR.1 LR.2 lrApp
      intro cLR c_in_C
      refine tabToInt (ClosedTableau.loc (subTabs cLR c_in_C) (by apply childNext subTabs next cLR))
    | (LocalTableau.fromSimple isSimple) =>
      apply tabToInt (next LR (by simp)) -- termination??
  | (@ClosedTableau.atmL LR' φ nBoxφ_in_L _simple_LR' cTabProj) => by
    let pθ := tabToInt cTabProj
    use (~(□~pθ.val)) -- modal rule on the right: use diamond of interpolant!
    constructor
    · -- voc property
      intro ℓ ℓ_in_θ
      rcases LR' with ⟨L',R'⟩
      exact diamondproj_does_not_increase_vocab_L nBoxφ_in_L (pθ.property.left ℓ_in_θ)
    · constructor -- implication property
      · rw [sat_double_neq_invariant]
        exact projection_reflects_unsat_L_L nBoxφ_in_L pθ.2.2.1
      · exact projection_reflects_unsat_L_R nBoxφ_in_L pθ.2.2.2
  -- dual to atmL
  | (@ClosedTableau.atmR LR' φ nBoxφ_in_R _simple_LR' cTabProj) => by
    let pθ := tabToInt cTabProj
    use (□pθ.val) -- modal rule on the right: use box of interpolant!
    constructor
    · -- voc property
      intro ℓ ℓ_in_θ
      rcases LR' with ⟨L',R'⟩
      exact diamondproj_does_not_increase_vocab_R nBoxφ_in_R (pθ.property.left ℓ_in_θ)
    · constructor -- implication property
      · exact projection_reflects_unsat_R_L nBoxφ_in_R pθ.2.2.1
      · exact projection_reflects_unsat_R_R nBoxφ_in_R pθ.2.2.2
termination_by tab.length
decreasing_by
all_goals
  subst_eqs
  simp_wf
  simp [ClosedTableau.length]
· exact childNext_lt subTabs next cLR c_in_C
· apply simple_lt isSimple next
