-- TABLEAU

import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.PImage
import Mathlib.Logic.IsEmpty
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

import Bml.Semantics
import Bml.Setsimp
import Bml.Vocabulary

open Formula
open HasLength
open HasVocabulary

-- TNodes
@[simp]
instance : HasSubset (Finset Formula × Finset Formula) :=
  HasSubset.mk λ (L1, R1) (L2, R2) => L1 ⊆ L2 ∧ R1 ⊆ R2

@[simp]
instance : Union (Finset Formula × Finset Formula) :=
  ⟨λ (L1, R1) (L2, R2) => (L1 ∪ L2, R1 ∪ R2)⟩

def TNode := Finset Formula × Finset Formula
  deriving DecidableEq, HasSubset, Union

@[simp]
def lengthOfTNode : TNode → Nat
  | (L,R) => lengthOfSet L + lengthOfSet R

@[simp]
instance TNodeHasLength : HasLength TNode := ⟨lengthOfTNode⟩

@[simp]
instance TNodeHasSat: HasSat TNode := ⟨fun (L,R) => HasSat.Satisfiable (L ∪ R)⟩

@[simp]
def f_in_TNode (f : Formula) (LR : TNode) := f ∈ (LR.1 ∪ LR.2)




-- Definition 9, page 15
-- A set X is closed  iff  it contains ⊥ or contains a formula and its negation.
def Closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X

-- A set X is simple  iff  all P ∈ X are (negated) atoms or □φ or ¬□φ.
@[simp]
def SimpleForm : Formula → Prop
  | ⊥ => True  -- TODO remove / change to False? (covered by bot rule)
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | □_ => True
  | ~(□_) => True
  | _ => False

instance : Decidable (SimpleForm φ) :=
  match h : φ with
  | ⊥
  | ·_
  | □_  => Decidable.isTrue <| by aesop
  | _⋀_ => Decidable.isFalse <| by aesop
  | ~ψ  => match ψ with
    | ⊥
    | ·_
    | □_ => Decidable.isTrue <| by aesop
    | _⋀_
    | ~_ => Decidable.isFalse <| by aesop

def SimpleSet : Finset Formula → Prop
  | X => ∀ P ∈ X.attach, SimpleForm P.val

instance : Decidable (SimpleSet X) := Finset.decidableDforallFinset

structure notSimpleFormOf (X : Finset Formula) where
  φ : Formula
  φinX : φ ∈ X
  not_simple : ¬SimpleForm φ

noncomputable def notSimpleSetToForm {X : Finset Formula}: ¬SimpleSet X →
  notSimpleFormOf X := λnot_simple =>
  have h : ∃φ ∈ X, ¬ SimpleForm φ := by rw [SimpleSet] at not_simple; aesop
  let w := Classical.choose h
  notSimpleFormOf.mk w (Classical.choose_spec h).1 (Classical.choose_spec h).2

def Simple (LR : TNode) : Prop := SimpleSet LR.1 ∧ SimpleSet LR.2

instance : Decidable (Simple LR) :=
  if L_simple : SimpleSet LR.1
  then if R_simple : SimpleSet LR.2
       then Decidable.isTrue  <| by simp[Simple]; aesop
       else Decidable.isFalse <| by simp[Simple]; aesop
  else Decidable.isFalse      <| by simp[Simple]; aesop

-- Let X_A := { R | [A]R ∈ X }.
@[simp]
def formProjection : Formula → Option Formula
  | □f => some f
  | _ => none

def projection : Finset Formula → Finset Formula
  | X => X.biUnion fun x => (formProjection x).toFinset

@[simp]
def projectTNode : TNode → TNode
  | (L, R) => (projection L, projection R)

@[simp]
theorem projectionUnion: projection (X ∪ Y) = projection X ∪ projection Y := by
  unfold projection
  aesop

-- TODO @[simp]
theorem proj {g : Formula} {X : Finset Formula} : g ∈ projection X ↔ □g ∈ X :=
  by
  rw [projection]
  simp
  constructor
  · intro lhs
    rcases lhs with ⟨boxg, boxg_in_X, projboxg_is_g⟩
    cases boxg
    repeat' aesop
  · intro rhs
    use □g

theorem projSet {X : Finset Formula} : ↑(projection X) = {ϕ | □ϕ ∈ X} :=
  by
  ext1
  simp
  exact proj


theorem projection_length_leq : ∀ f, (projection {f}).sum lengthOfFormula ≤ lengthOfFormula f :=
  by
  intro f
  cases f
  · unfold projection; simp
  · unfold projection; simp
  · unfold projection; simp
  · unfold projection; simp
  case box f =>
    have subsubClaim : projection {□f} = {f} := by ext1; rw [proj]; simp
    rw [subsubClaim]
    simp

theorem projection_set_length_leq : ∀ X, lengthOfSet (projection X) ≤ lengthOfSet X :=
  by
  intro X
  induction X using Finset.induction_on
  · simp [projection]
  case insert f S f_not_in_S IH =>
    unfold lengthOfSet
    rw [Finset.sum_insert f_not_in_S]
    have insert_comm_proj : ∀ X f, projection (insert f X) = projection {f} ∪ projection X :=
      by
      intro X f
      unfold projection
      simp
    · calc
        (projection (insert f S)).sum lengthOfFormula
          = (projection {f} ∪ projection S).sum lengthOfFormula := by rw [insert_comm_proj S f]
        _ ≤ (projection {f}).sum lengthOfFormula + (projection S).sum lengthOfFormula := by
          apply sum_union_le
        _ ≤ lengthOfFormula f + (projection S).sum lengthOfFormula := by
          simp only [add_le_add_iff_right, projection_length_leq]
        _ ≤ lengthOfFormula f + S.sum lengthOfFormula := by simp; apply IH

inductive OneSidedLocalRule : Finset Formula → List (Finset Formula) → Type
  | bot                  : OneSidedLocalRule {⊥}      ∅
  | not  (φ   : Formula) : OneSidedLocalRule {φ, ~φ}  ∅
  | neg  (φ   : Formula) : OneSidedLocalRule {~~φ}    [{φ}]
  | con  (φ ψ : Formula) : OneSidedLocalRule {φ ⋀ ψ}  [{φ,ψ}]
  | ncon (φ ψ : Formula) : OneSidedLocalRule {~(φ⋀ψ)} [{~φ}, {~ψ}]

def SubPair := Finset Formula × Finset Formula
deriving DecidableEq

inductive LocalRule : SubPair → List SubPair → Type
  | oneSidedL (orule : OneSidedLocalRule precond ress) : LocalRule (precond,∅) $ ress.map $ λ res => (res,∅)
  | oneSidedR (orule : OneSidedLocalRule precond ress) : LocalRule (∅,precond) $ ress.map $ λ res => (∅,res)
  | LRnegL (ϕ : Formula) : LocalRule ({ϕ}, {~ϕ}) ∅ --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ({~ϕ}, {ϕ}) ∅ -- ~ϕ occurs on the left side,  ϕ on the right

@[simp]
def jvoc (LR: TNode) := voc LR.1 ∩ voc LR.2

@[simp]
def applyLocalRule (_ : LocalRule (Lcond, Rcond) ress) : TNode → List TNode
  | ⟨L,R⟩ => ress.map $ λc => (L \ Lcond ∪ c.1, R \ Rcond ∪ c.2)

inductive LocalRuleApp : TNode → List TNode → Type
  | mk {L R : Finset Formula}
       {C : List TNode}
       (ress : List SubPair)
       (Lcond Rcond : Finset Formula)
       (rule : LocalRule (Lcond,Rcond) ress)
       {hC : C = applyLocalRule rule (L,R)}
       (preconditionProof : Lcond ⊆ L ∧ Rcond ⊆ R)
       : LocalRuleApp (L,R) C

lemma oneSidedRule_preserves_other_side_L
  {ruleApp : LocalRuleApp (L, R) C}
  (hmyrule : ruleApp = (@LocalRuleApp.mk L R C (List.map (fun res => (res, ∅)) _) _ _ rule hC preproof))
  (rule_is_left : rule = LocalRule.oneSidedL orule )
  : ∀c ∈ C, c.2 = R := by aesop

lemma oneSidedRule_preserves_other_side_R
  {ruleApp : LocalRuleApp (L, R) C}
  (hmyrule : ruleApp = (@LocalRuleApp.mk L R C (List.map (fun res => (∅, res)) _) _ _ rule hC preproof))
  (rule_is_right : rule = LocalRule.oneSidedR orule )
  : ∀c ∈ C, c.1 = L := by aesop

lemma localRule_does_not_increase_vocab_L (rule : LocalRule (Lcond, Rcond) ress)
  : ∀res ∈ ress, voc res.1 ⊆ voc Lcond := by
  intro res ress_in_ress ℓ ℓ_in_res
  cases rule
  case oneSidedL ress orule => cases orule <;> aesop
  -- other cases are trivial
  all_goals aesop
-- dual
lemma localRule_does_not_increase_vocab_R (rule : LocalRule (Lcond, Rcond) ress)
  : ∀res ∈ ress, voc res.2 ⊆ voc Rcond := by
  intro res ress_in_ress ℓ ℓ_in_res
  cases rule
  case oneSidedR ress orule => cases orule <;> aesop
  -- other cases are trivial
  all_goals aesop

theorem localRuleApp_does_not_increase_vocab {L R : Finset Formula} (ruleA : LocalRuleApp (L,R) C)
  : ∀cLR ∈ C, jvoc cLR ⊆ jvoc (L,R) := by -- decidableMem
  match ruleA with
  | @LocalRuleApp.mk _ _ _ ress Lcond Rcond rule hC preproof =>
  intro c cinC ℓ ℓ_in_c
  simp at ℓ_in_c
  simp
  constructor
  · have ⟨Lφ,Lφ_in_cL, ℓ_in_Lφ⟩ := ℓ_in_c.left
    apply Or.elim (em (Lφ ∈ L))
    · intro Lφ_in_L; use Lφ
    · intro not_Lφ_in_L
      have Lφ_in_res : ∃res ∈ ress, Lφ ∈ res.1 := by aesop
      let ⟨res, res_in_ress, Lφ_in_res_L⟩ := Lφ_in_res
      have ℓ_in_ψ_in_Lcond : ∃ψ ∈ Lcond, ℓ ∈ voc ψ := by
        let voc_res_ss_Lcond := localRule_does_not_increase_vocab_L rule res res_in_ress
        simp at voc_res_ss_Lcond
        let ℓ_in_voc_Lcond := voc_res_ss_Lcond Lφ Lφ_in_res_L ℓ_in_Lφ
        simp at ℓ_in_voc_Lcond
        exact ℓ_in_voc_Lcond
      let ⟨ψ, ψ_in_Lcond, ℓ_in_ψ⟩ := ℓ_in_ψ_in_Lcond
      use ψ, (by aesop), ℓ_in_ψ
  -- dual
  · have ⟨Rφ,Rφ_in_cR, ℓ_in_Rφ⟩ := ℓ_in_c.right
    apply Or.elim (em (Rφ ∈ R))
    · intro Rφ_in_R; use Rφ
    · intro not_Rφ_in_R
      have Rφ_in_res : ∃res ∈ ress, Rφ ∈ res.2 := by aesop
      let ⟨res, res_in_ress, Rφ_in_res_R⟩ := Rφ_in_res
      have ℓ_in_ψ_in_Rcond : ∃ψ ∈ Rcond, ℓ ∈ voc ψ := by
        let voc_res_ss_Rcond := localRule_does_not_increase_vocab_R rule res res_in_ress
        simp at voc_res_ss_Rcond
        let ℓ_in_voc_Rcond := voc_res_ss_Rcond Rφ Rφ_in_res_R ℓ_in_Rφ
        simp at ℓ_in_voc_Rcond
        exact ℓ_in_voc_Rcond
      let ⟨ψ, ψ_in_Rcond, ℓ_in_ψ⟩ := ℓ_in_ψ_in_Rcond
      use ψ, (by aesop), ℓ_in_ψ

-- used in LocalRule_uniqueL
@[simp]
theorem not_notSelfContain : ~φ ≠ φ := fun.

-- If one local rule substituting some formula α by some set res applies to some node LR,
-- then all children of LR in any local tableau contain α or res
-- used to prove that paths are saturated
theorem LocalRuleUniqueL
  (α_in_L: α ∈ L)
  (lrApp: LocalRuleApp (L,R) C)
  (orule: OneSidedLocalRule precond ress)
  (precond_eq: precond = {α})
  : ∀ c ∈ C, α ∈ c.1 ∨ (∃ res ∈ ress, res ⊆ c.1) := by
  intro c c_in
  rcases lrApp with ⟨ress', Lcond', Rcond', lr', L_cond_in, R_cond_in⟩
  rename_i C_eq
  subst C_eq
  cases lr'
  case oneSidedL ress orule' =>
    cases orule
    case bot =>
      cases orule'
      all_goals aesop
    case not φ =>
      apply Finset.subset_of_eq at precond_eq
      rw [Finset.subset_singleton_iff'] at precond_eq
      simp_all
      rcases precond_eq with ⟨l,r⟩
      subst l
      aesop
    case neg φ =>
      cases orule'
      case neg φ' =>
        simp_all
        subst c_in
        subst precond_eq
        if φ = φ'
        then simp_all
        else simp_all
      all_goals aesop
    case con φ ψ =>
      cases orule'
      case con φ' ψ' =>
        simp_all
        subst c_in
        subst precond_eq
        if φ = φ' ∧ ψ = ψ'
        then
          apply Or.inr
          refine Finset.insert_subset_iff.mpr ?_
          aesop
        else aesop
      all_goals aesop
    case ncon φ ψ =>
      simp_all
      cases orule'
      case ncon φ' ψ' =>
        simp at c_in
        subst precond_eq
        cases c_in
        case inl c_eq =>
          subst c_eq
          if φ = φ'
          then simp_all
          else aesop
        case inr c_eq =>
          subst c_eq
          if ψ = ψ'
          then simp_all
          else aesop
      all_goals aesop
  case oneSidedR orule' =>
    apply Or.inl
    aesop
  -- in other cases C is empty
  all_goals simp_all

-- almost exactly the same as LocalRuleUniqueL
lemma LocalRuleUniqueR
  (α_in_R: α ∈ R)
  (lrApp: LocalRuleApp (L,R) C)
  (orule: OneSidedLocalRule precond ress)
  (precond_eq: precond = {α})
  : ∀ c ∈ C, α ∈ c.2 ∨ (∃ res ∈ ress, res ⊆ c.2) := by
  intro c c_in
  rcases lrApp with ⟨ress', Lcond', Rcond', lr', L_cond_in, R_cond_in⟩
  rename_i C_eq
  subst C_eq
  cases lr'
  case oneSidedR ress orule' =>
    cases orule
    case bot =>
      cases orule'
      all_goals aesop
    case not φ =>
      apply Finset.subset_of_eq at precond_eq
      rw [Finset.subset_singleton_iff'] at precond_eq
      simp_all
      rcases precond_eq with ⟨l,r⟩
      subst l
      aesop
    case neg φ =>
      cases orule'
      case neg φ' =>
        simp_all
        subst c_in
        subst precond_eq
        if φ = φ'
        then simp_all
        else simp_all
      all_goals aesop
    case con φ ψ =>
      cases orule'
      case con φ' ψ' =>
        simp_all
        subst c_in
        subst precond_eq
        if φ = φ' ∧ ψ = ψ'
        then
          apply Or.inr
          refine Finset.insert_subset_iff.mpr ?_
          aesop
        else aesop
      all_goals aesop
    case ncon φ ψ =>
      simp_all
      cases orule'
      case ncon φ' ψ' =>
        simp at c_in
        subst precond_eq
        cases c_in
        case inl c_eq =>
          subst c_eq
          if φ = φ'
          then simp_all
          else aesop
        case inr c_eq =>
          subst c_eq
          if ψ = ψ'
          then simp_all
          else aesop
      all_goals aesop
  case oneSidedL orule' =>
    apply Or.inl
    aesop
  -- in other cases C is empty
  all_goals simp_all

inductive LocalTableau : TNode → Type
  | fromRule
      {LR : TNode}
      {C : List TNode}
      (ruleA : LocalRuleApp LR C)
      (subTabs: (Π c ∈ C, LocalTableau c))
      : LocalTableau LR
  | fromSimple (isSimple : Simple LR) : LocalTableau LR

-- If X is not simple, then a local rule can be applied.
-- (page 13)

-- TODO custom tactic
noncomputable def notSimpleToRuleApp {L R : Finset Formula}: ¬Simple (L,R) →
  ΣC, LocalRuleApp (L,R) C := λnot_simple =>
  if simple_L : SimpleSet L
  then if simple_R : SimpleSet R
    then by exfalso; exact not_simple <| And.intro simple_L simple_R
    else by -- R not simple
      let vvv := notSimpleSetToForm simple_R
      match φdef : vvv.φ with
      | ⊥
      | ·_
      | □_  => exfalso; apply vvv.not_simple; aesop
      | ψ⋀χ => -- TODO: encapsulate in tactic
        let rule := LocalRule.oneSidedR (OneSidedLocalRule.con ψ χ)
        let C := applyLocalRule rule (L,R)
        exact ⟨C,(@LocalRuleApp.mk L R C
          (List.map (fun res => (∅, res)) [{ψ, χ}]) -- since DecidableEq cannot simplify this apparently
          ∅ {ψ⋀χ} rule (rfl)
          ⟨(Finset.empty_subset L), (by rw[← φdef]; simp [vvv.φinX])⟩
        )⟩

      | ~ψ  => match ψ with
        | ⊥
        | ·_
        | □_ => exfalso; apply vvv.not_simple; aesop
        | ψ⋀χ =>
          let rule := LocalRule.oneSidedR (OneSidedLocalRule.ncon ψ χ)
          let C := applyLocalRule rule (L,R)
          exact ⟨C,(@LocalRuleApp.mk L R C
            (List.map (fun res => (∅, res)) [{~ψ}, {~χ}]) -- since DecidableEq cannot simplify this apparently
            ∅ {~(ψ⋀χ)} rule (rfl)
            ⟨(Finset.empty_subset L), (by rw[← φdef]; simp [vvv.φinX])⟩
          )⟩
        | ~ψ =>
          let rule := LocalRule.oneSidedR (OneSidedLocalRule.neg ψ)
          let C := applyLocalRule rule (L,R)
          exact ⟨C,(@LocalRuleApp.mk L R C
            (List.map (fun res => (∅, res)) [{ψ}]) -- since DecidableEq cannot simplify this apparently
            ∅ {~~ψ} rule (rfl)
            ⟨(Finset.empty_subset L), (by rw[← φdef]; simp [vvv.φinX])⟩
          )⟩
  else by -- L not simple, dual
      let vvv := notSimpleSetToForm simple_L
      match φdef : vvv.φ with
      | ⊥
      | ·_
      | □_  => exfalso; apply vvv.not_simple; aesop
      | ψ⋀χ => -- TODO: encapsulate in tactic
        let rule := LocalRule.oneSidedL (OneSidedLocalRule.con ψ χ)
        let C := applyLocalRule rule (L,R)
        exact ⟨C,(@LocalRuleApp.mk L R C
          (List.map (fun res => (res,∅)) [{ψ, χ}]) -- since DecidableEq cannot simplify this apparently
          {ψ⋀χ} ∅ rule (rfl)
          ⟨(by rw[← φdef]; simp [vvv.φinX]), (Finset.empty_subset R)⟩
        )⟩

      | ~ψ  => match ψ with
        | ⊥
        | ·_
        | □_ => exfalso; apply vvv.not_simple; aesop
        | ψ⋀χ =>
          let rule := LocalRule.oneSidedL (OneSidedLocalRule.ncon ψ χ)
          let C := applyLocalRule rule (L,R)
          exact ⟨C,(@LocalRuleApp.mk L R C
            (List.map  (fun res => (res,∅)) [{~ψ}, {~χ}]) -- since DecidableEq cannot simplify this apparently
            {~(ψ⋀χ)} ∅  rule (rfl)
          ⟨(by rw[← φdef]; simp [vvv.φinX]), (Finset.empty_subset R)⟩
          )⟩
        | ~ψ =>
          let rule := LocalRule.oneSidedL (OneSidedLocalRule.neg ψ)
          let C := applyLocalRule rule (L,R)
          exact ⟨C,(@LocalRuleApp.mk L R C
            (List.map (fun res => (res,∅)) [{ψ}]) -- since DecidableEq cannot simplify this apparently
            {~~ψ} ∅  rule (rfl)
          ⟨(by rw[← φdef]; simp [vvv.φinX]), (Finset.empty_subset R)⟩
          )⟩

theorem notSimpleThenLocalRule {L R} : ¬Simple (L,R)
  → ∃ Lcond Rcond ress, ∃ _ : LocalRule (Lcond, Rcond) ress, Lcond ⊆ L ∧ Rcond ⊆ R := by
    intro not_simple
    let ⟨C, ruleA⟩ := notSimpleToRuleApp not_simple
    match ruleA with
    | @LocalRuleApp.mk _ _ _ ress Lcond Rcond rule _ pp => exact ⟨Lcond, Rcond, ress, rule, pp⟩


theorem conDecreasesLength {φ ψ : Formula} :
  (Finset.sum {φ, ψ} fun x => lengthOfFormula x) <
  1 + lengthOfFormula φ + lengthOfFormula ψ :=
  by
    cases' em (φ = ψ) with heq hneq
    · simp [heq] at *
    · simp [Finset.sum_pair hneq]

theorem localRuleDecreasesLengthSide (rule : LocalRule (Lcond, Rcond) ress) :
  ∀ res ∈ ress,
      (lengthOf res.1 < lengthOf Lcond ∧ res.2 = ∅)
    ∨ (lengthOf res.2 < lengthOf Rcond ∧ res.1 = ∅) :=
    by
    intro res in_ress
    cases rule <;>
    ( first
      | ( rename_i rule
          cases rule
          <;> (simp at *; try rw [in_ress])
          case neg φ => simp [←Nat.add_assoc]
          case con φ ψ => simp; exact conDecreasesLength
          case ncon φ ψ =>
            cases' in_ress with case_phi case_psi
            <;> ( first
                | simp [case_psi]
                | ( simp [case_phi]
                    rw [Nat.add_comm 1 (lengthOfFormula φ), Nat.add_assoc]
                    aesop)))
      | all_goals aesop)


-- These are used by aesop in `localRuleNoOverlap`.
@[simp]
theorem notnot_notSelfContain : ~~φ ≠ φ := fun.
@[simp]
theorem conNotSelfContainL : φ1 ⋀ φ2 ≠ φ1 := fun.
@[simp]
theorem conNotSelfContainR : φ1 ⋀ φ2 ≠ φ2 :=
  -- This should also just be "fun." but we have too much Mathlib imported.
  -- see https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20well-foundedness.20of.20my.20own.20inductive.3F/near/416990596
  by
  induction φ2
  all_goals simp
  intro hyp
  subst hyp
  tauto

-- Rules never re-insert the same formula(s).
theorem localRuleNoOverlap
  (rule : LocalRule (Lcond, Rcond) ress) :
  ∀ res ∈ ress, (Lcond ∩ res.1 = ∅) ∧ (Rcond ∩ res.2 = ∅) :=
  by
    intro res in_ress
    cases rule <;>
    ( rename_i rule
      cases rule
      all_goals aesop)


-- Some helper definitions for localRuleAppDecreasesLengthSide.
-- We switch from ℕ to ℤ here to have a reasonable "-" and use
-- theorems that only hold in rings.

@[simp]
def zlengthOf : Formula → Int := fun f => Coe.coe (lengthOfFormula f)

theorem zlengthOf.pos : 0 ≤ zlengthOf φ := Int.ofNat_nonneg (lengthOfFormula φ)

@[simp]
def zlengthOfSet : Finset Formula → Int := fun X => X.sum zlengthOf

theorem zlen_iff { X Y : Finset Formula }
    : lengthOf X < lengthOf Y ↔ zlengthOfSet X < zlengthOfSet Y :=
  by
  have : ∀ W, zlengthOfSet W = lengthOfSet W := by intro W; simp; rfl
  rw [this, this]
  zify
  simp

theorem zlengthOfSet.pos : zlengthOfSet X ≥ 0 := by
  apply Finset.sum_induction zlengthOf
  · intro a b a_ge b_ge; linarith
  · simp
  · intro f _; exact zlengthOf.pos

theorem localRuleAppDecreasesLengthSide
  (X Cond Res : Finset Formula)
  (hyp : lengthOf Res < lengthOf Cond)
  (precondProof : Cond ⊆ X) :
  lengthOf (X \ Cond ∪ Res) < lengthOf X :=
  by
    rw [zlen_iff]
    calc zlengthOfSet (X \ Cond ∪ Res)
        ≤ zlengthOfSet (X \ Cond) + zlengthOfSet Res := by
            have := @Finset.sum_union_inter _ _ (X \ Cond) Res zlengthOf _ _
            have : zlengthOfSet (X \ Cond ∩ Res) ≥ 0 := zlengthOfSet.pos
            simp_all
            linarith
      _ = zlengthOfSet X - zlengthOfSet Cond + zlengthOfSet Res := by
            simp only [zlengthOfSet]
            rw [Finset.sum_sdiff_eq_sub precondProof]
      _ < zlengthOfSet X := by
            have : zlengthOfSet Res < zlengthOfSet Cond := by
              rw [← zlen_iff]
              exact hyp
            linarith

theorem localRuleAppDecreasesLength
  {L R : Finset Formula}
  (lrApp : @LocalRuleApp (L,R) C) :
  ∀c ∈ C, lengthOfTNode c < lengthOfTNode (L,R) :=
  by
    intro c c_child
    let ⟨ress, Lcond, Rcond, rule, precondProofL, precondProofR⟩ := lrApp
    rename_i C_def
    subst C_def
    simp only [applyLocalRule, List.mem_map] at c_child
    rcases c_child with ⟨res, res_in_ress, def_c⟩
    have lS := localRuleDecreasesLengthSide rule res res_in_ress
    have := localRuleNoOverlap rule res res_in_ress
    cases lS
    case inl hyp =>
      calc lengthOfTNode c
      = lengthOfSet (L \ Lcond ∪ res.1) + lengthOfSet (R \ Rcond ∪ res.2) :=
          by subst def_c; simp
      _ ≤ lengthOfSet (L \ Lcond ∪ res.1) + lengthOfSet R :=
          by rw [hyp.2]; simp [Finset.sum_le_sum_of_subset]
      _ < lengthOfSet L + lengthOfSet R :=
          by have := localRuleAppDecreasesLengthSide L Lcond res.1 hyp.1 precondProofL; aesop
      _ = lengthOfTNode (L, R) := by simp
    case inr hyp =>
      calc lengthOfTNode c
      = lengthOfSet (L \ Lcond ∪ res.1) + lengthOfSet (R \ Rcond ∪ res.2) :=
          by subst def_c; simp
      _ ≤ lengthOfSet L + lengthOfSet (R \ Rcond ∪ res.2) :=
          by rw [hyp.2]; simp [Finset.sum_le_sum_of_subset]
      _ < lengthOfSet L + lengthOfSet R :=
          by have := localRuleAppDecreasesLengthSide R Rcond res.2 hyp.1 precondProofR; aesop
      _ = lengthOfTNode (L, R) := by simp

-- theorem AppLocalTableau.DecreasesLength
--   (appTab : AppLocalTableau LR C)
--   (c_in : c ∈ C) :
--   lengthOfTNode c < lengthOfTNode LR :=
--   by
--   rcases appTab with ⟨lrApp, next⟩
--   have := localRuleAppDecreasesLength lrApp
--   aesop

-- Lift definition of projection to TNodes, including the diamond formula left or right.
def diamondProjectTNode : Sum Formula Formula → TNode → TNode
| (Sum.inl φ), (L, R) => (projection L ∪ {~φ}, projection R)
| (Sum.inr φ), (L, R) => (projection L, projection R ∪ {~φ})

lemma proj_does_not_increase_vocab : voc (projection X) ⊆ voc X := by
  simp
  intro φ φ_in_proj ℓ ℓ_in_φ
  rw [proj] at φ_in_proj
  simp
  tauto

theorem vocProj (X) : voc (projection X) ⊆ voc X :=
  by
  simp
  intro ϕ phi_in_proj
  rw [proj] at phi_in_proj
  intro a aInVocPhi
  simp
  tauto

theorem diamondproj_does_not_increase_vocab_L (valid_proj : ~(□φ) ∈ L) : jvoc ((diamondProjectTNode (Sum.inl φ) (L,R))) ⊆ jvoc (L,R) := by
  intro ℓ ℓ_in_proj
  unfold jvoc at *
  apply Finset.mem_inter_of_mem
  · have ℓ_left := (Finset.mem_inter.mp ℓ_in_proj).left
    simp [diamondProjectTNode ] at ℓ_left;
    apply Or.elim ℓ_left
    · intro ℓ_in_φ; simp;
      use ~(□φ); constructor; exact valid_proj; aesop
    · intro ⟨ψ, ψ_in_proj, ℓ_in_ψ⟩
      apply proj_does_not_increase_vocab
      simp; use ψ
  · have ℓ_right := (Finset.mem_inter.mp ℓ_in_proj).right
    simp [diamondProjectTNode ] at ℓ_right;
    apply proj_does_not_increase_vocab
    simp; exact ℓ_right

theorem diamondproj_does_not_increase_vocab_R (valid_proj : ~(□φ) ∈ R) : jvoc ((diamondProjectTNode (Sum.inr φ) (L,R))) ⊆ jvoc (L,R) := by
  intro ℓ ℓ_in_proj
  unfold jvoc at *
  apply Finset.mem_inter_of_mem
  · have ℓ_left := (Finset.mem_inter.mp ℓ_in_proj).left
    simp [diamondProjectTNode ] at ℓ_left;
    apply proj_does_not_increase_vocab
    simp; exact ℓ_left
  · have ℓ_right := (Finset.mem_inter.mp ℓ_in_proj).right
    simp [diamondProjectTNode ] at ℓ_right;
    apply Or.elim ℓ_right
    · intro ℓ_in_φ; simp;
      use ~(□φ); constructor; exact valid_proj; aesop
    · intro ⟨ψ, ψ_in_proj, ℓ_in_ψ⟩
      apply proj_does_not_increase_vocab
      simp; use ψ

theorem projDecreasesLength {X : Finset Formula} {φ} :
  ~(□φ) ∈ X → lengthOfSet (projection X ∪ {~φ}) < lengthOfSet X :=
  by
    intro notBoxPhi_in_X
    have otherClaim : projection X = projection (X.erase (~(□φ))) :=
      by
      ext1 phi
      repeat rw [proj]
      simp
    · calc
        lengthOfSet (projection X ∪ {~φ}) ≤ lengthOfSet (projection X) + lengthOf (~φ)  :=
            by rw [union_singleton_is_insert]; exact lengthOf_insert_leq_plus
          _ = lengthOfSet (projection X) + lengthOf φ + 1   := by simp; ring
          _ < lengthOfSet (projection X) + lengthOf φ + 2   := by simp
          _ = lengthOfSet (projection X) + lengthOf (~(□φ)) := by simp; ring
          _ = lengthOfSet (projection (X.erase (~(□φ)))) + lengthOf (~(□φ)) := by rw [otherClaim]
          _ ≤ lengthOfSet (X.erase (~(□φ))) + lengthOf (~(□φ)) := by simp; apply projection_set_length_leq
          _ = lengthOfSet X := lengthRemove X (~(□φ)) notBoxPhi_in_X

theorem atmRuleLDecreasesLength {L R : Finset Formula} {φ} :
    ~(□φ) ∈ L → lengthOfTNode (diamondProjectTNode (Sum.inl φ) (L, R)) < lengthOfTNode (L, R) :=
  by
    intro notBoxPhi_in_L
    have lengthL := projDecreasesLength notBoxPhi_in_L
    · calc
        lengthOfTNode (diamondProjectTNode (Sum.inl φ) (L, R))
          = lengthOfSet (projection L ∪ {~φ}) + lengthOfSet (projection R) := by tauto
          _ ≤ lengthOfSet (projection L ∪ {~φ}) + lengthOfSet R := by
            have lengthR : lengthOfSet (projection R) ≤ lengthOfSet R :=
              by apply projection_set_length_leq
            apply Nat.add_le_add_left lengthR
          _ < lengthOfSet L + lengthOfSet R := by apply Nat.add_lt_add_right lengthL
          _ = lengthOfTNode (L, R) := by rw [lengthOfTNode]

theorem atmRuleRDecreasesLength {L R : Finset Formula} {φ} :
    ~(□φ) ∈ R → lengthOfTNode (diamondProjectTNode (Sum.inr φ) (L, R)) < lengthOfTNode (L, R) :=
  by
    intro notBoxPhi_in_R
    have lengthR := projDecreasesLength notBoxPhi_in_R
    · calc
        lengthOfTNode (diamondProjectTNode (Sum.inr φ) (L, R))
          = lengthOfSet (projection L) + lengthOfSet (projection R ∪ {~φ}) := by tauto
          _ ≤ lengthOfSet L + lengthOfSet (projection R ∪ {~φ}) := by
            have lengthL : lengthOfSet (projection L) ≤ lengthOfSet L :=
              by apply projection_set_length_leq
            apply Nat.add_le_add_right lengthL
          _ < lengthOfSet L + lengthOfSet R := by apply Nat.add_lt_add_left lengthR
          _ = lengthOfTNode (L, R) := by rw [lengthOfTNode]

open LocalTableau

-- needed for endNodesOf
instance localTableauHasLength : HasLength (Σ LR, LocalTableau LR) :=
  ⟨fun ⟨(L, R), _⟩ => lengthOfTNode (L, R)⟩

-- open end nodes of a given localTableau
def endNodesOf : (Σ LR, LocalTableau LR) → List TNode
  | ⟨LR, @LocalTableau.fromRule _ C ruleA subTabs⟩ =>
    (C.attach.map fun ⟨c, c_in⟩ =>
      have tc : LocalTableau c := subTabs c c_in
      have : lengthOfTNode c < lengthOfTNode LR := localRuleAppDecreasesLength ruleA c c_in
      endNodesOf ⟨c, tc⟩
      ).join
  | ⟨LR, LocalTableau.fromSimple _⟩ => [LR]
termination_by
  endNodesOf pair => lengthOf pair

@[simp]
theorem endNodesOfSimple : endNodesOf ⟨ LR, LocalTableau.fromSimple hyp ⟩ = [LR] :=
  by
  simp only [endNodesOf]

noncomputable def endNodeIsEndNodeOfChild (ruleA)
  (E_in: E ∈ endNodesOf ⟨LR, @LocalTableau.fromRule LR C ruleA subTabs⟩) :
  @Subtype TNode (fun x => ∃ h, E ∈ endNodesOf ⟨x, subTabs x h⟩) := by
  unfold endNodesOf at E_in
  simp_all!
  choose l h E_in using E_in
  choose c c_in l_eq using h
  subst l_eq
  use c
  use c_in

@[simp]
theorem lrEndNodes {LR : TNode} {C : List TNode} {ruleA} {subTabs} :
    endNodesOf ⟨LR, LocalTableau.fromRule ruleA subTabs⟩
    = (C.attach.map (fun ⟨c, c_in⟩ => endNodesOf ⟨c, subTabs c c_in⟩)).join :=
  by
  simp only [endNodesOf]

theorem endNodesOfLEQ {LR Z ltLR} : Z ∈ endNodesOf ⟨LR, ltLR⟩ → lengthOfTNode Z ≤ lengthOfTNode LR :=
  by
  cases ltLR
  case fromRule altLR subTabs lrApp =>
    intro Z_endOf_LR
    simp at Z_endOf_LR
    rcases Z_endOf_LR with ⟨ZS, ⟨c, c_in_C, endNodes_c_eq_ZS⟩, Z_in_ZS⟩
    subst endNodes_c_eq_ZS
    apply le_of_lt
    have := localRuleAppDecreasesLength lrApp c c_in_C -- for termination and below!
    · calc
        lengthOfTNode Z ≤ lengthOfTNode c := endNodesOfLEQ Z_in_ZS
        _ < lengthOfTNode LR := this
  case fromSimple LR_simp => intro Z_endOf_Y; aesop
termination_by
  endNodesOfLEQ LT   => lengthOfTNode LR

theorem endNodesOfLocalRuleLT :
    Z ∈ endNodesOf ⟨LR, LocalTableau.fromRule lrApp subTabs⟩ → lengthOfTNode Z < lengthOfTNode LR :=
  by
  intro Z_endOf_LR
  simp at Z_endOf_LR
  rcases Z_endOf_LR with ⟨ZS, ⟨c, c_in_C, endNodes_c_eq_ZS⟩, Z_in_ZS⟩
  subst endNodes_c_eq_ZS
  have := localRuleAppDecreasesLength lrApp c c_in_C -- for termination and below!
  · calc
      lengthOfTNode Z ≤ lengthOfTNode c := endNodesOfLEQ Z_in_ZS
      _ < lengthOfTNode LR := this

-- Definition 16, page 29
-- Notes:
-- - "loc" may actually make no progress (by using "LocalTableau.fromSimple"), but that seems okay.
-- - base case for simple tableaux is part of "atm" which can be applied to L or to R.
inductive ClosedTableau : TNode → Type
  | loc {LR} (lt : LocalTableau LR) : (next : ∀ Y ∈ endNodesOf ⟨LR, lt⟩, ClosedTableau Y) → ClosedTableau LR
  | atmL {LR ϕ} : ~(□ϕ) ∈ LR.1 → Simple LR → ClosedTableau (diamondProjectTNode (Sum.inl ϕ) LR) → ClosedTableau LR
  | atmR {LR ϕ} : ~(□ϕ) ∈ LR.2 → Simple LR → ClosedTableau (diamondProjectTNode (Sum.inr ϕ) LR) → ClosedTableau LR

def closedToLocal : ClosedTableau X → LocalTableau X
  | (ClosedTableau.loc lt _) => lt
  | (ClosedTableau.atmL _ SimpX _) => fromSimple SimpX
  | (ClosedTableau.atmR _ SimpX _) => fromSimple SimpX

inductive Provable : Formula → Prop
  | byTableau {φ : Formula} : ClosedTableau ({~φ},{}) → Provable φ

inductive ProvableImplication : Formula → Formula → Prop
  | byTableau : ClosedTableau ({φ},{~ψ}) → ProvableImplication φ ψ

-- Definition 17, page 30
def Inconsistent : TNode → Prop
  | LR => Nonempty (ClosedTableau LR)

def Consistent : TNode → Prop
  | LR => ¬Inconsistent LR

-- TODO: class Consistent to also allow sets instead fo TNodes

noncomputable def aLocalTableauFor (LR: TNode) : LocalTableau LR :=
  if h_simple : (Simple LR)
  then LocalTableau.fromSimple h_simple
  else
    let ⟨C, ruleA⟩ := notSimpleToRuleApp h_simple
    LocalTableau.fromRule ruleA <| (λc c_in_C =>
      have := localRuleAppDecreasesLength ruleA c c_in_C -- for termination
      aLocalTableauFor c)
  termination_by
    aLocalTableauFor LR => lengthOf LR
  decreasing_by
    simp_wf; assumption

instance : Nonempty (LocalTableau LR) := Nonempty.intro (aLocalTableauFor LR)

-- This is not used, because `aLocalTableauFor` already does the job.
theorem existsLocalTableauFor LR : Nonempty (LocalTableau LR) :=
  by
    cases em ¬(∃ Lcond Rcond C, Nonempty (LocalRule (Lcond, Rcond) C) ∧ Lcond ⊆ LR.1 ∧ Rcond ⊆ LR.2)
    case inl canApplyRule =>
      constructor
      apply LocalTableau.fromSimple
      by_contra hyp
      have := notSimpleThenLocalRule hyp
      aesop
    case inr canApplyRule =>
      rw [not_not] at canApplyRule
      rcases canApplyRule with ⟨LCond, RCond, C, lr_exists, preconL, preconR⟩
      cases' lr_exists with lr
      constructor
      apply LocalTableau.fromRule
      apply LocalRuleApp.mk C LCond RCond lr ⟨preconL, preconR⟩
      use applyLocalRule lr (LR.1, LR.2)
      rfl
      intro c c_in
      let ruleA := @LocalRuleApp.mk LR.1 LR.2 (applyLocalRule lr (LR.1, LR.2)) _ LCond RCond lr rfl ⟨preconL, preconR⟩
      have := localRuleAppDecreasesLength ruleA c c_in
      apply Classical.choice (existsLocalTableauFor c)
termination_by
  existsLocalTableauFor LR => lengthOf LR
