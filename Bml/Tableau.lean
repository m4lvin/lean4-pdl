-- TABLEAU

import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.PImage
import Mathlib.Logic.IsEmpty
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Ring

import Bml.Syntax
import Bml.Semantics
import Bml.Setsimp
import Bml.Vocabulary

open Formula

open HasLength

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def Closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X

-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
@[simp]
def SimpleForm : Formula → Bool
  | ⊥ => True  -- TODO remove / change to False? (covered by bot rule)
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | □_ => True
  | ~(□_) => True
  | _ => False

def Simple : Finset Formula → Bool
  | X => ∀ P ∈ X, SimpleForm P

-- Let X_A := { R | [A]R ∈ X }.
@[simp]
def formProjection : Formula → Option Formula
  | □f => some f
  | _ => none

def projection : Finset Formula → Finset Formula
  | X => X.biUnion fun x => (formProjection x).toFinset

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
    simp
    have insert_comm_proj : ∀ X f, projection (insert f X) = projection {f} ∪ projection X :=
      by
      intro X f
      unfold projection
      ext1 g
      simp
    · calc
        (projection (insert f S)).sum lengthOfFormula =
            (projection (insert f S)).sum lengthOfFormula :=
          refl _
        _ = (projection {f} ∪ projection S).sum lengthOfFormula := by rw [insert_comm_proj S f]
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

-- We have equality when types match
instance : DecidableEq (OneSidedLocalRule precond ress) := λ_ _ => Decidable.isTrue (sorry)

def SubPair := Finset Formula × Finset Formula
deriving DecidableEq


inductive LocalRule : SubPair → List SubPair → Type
  | oneSidedL (orule : OneSidedLocalRule precond ress) : LocalRule (precond,∅) $ ress.map $ λ res => (res,∅)
  | oneSidedR (orule : OneSidedLocalRule precond ress) : LocalRule (∅,precond) $ ress.map $ λ res => (∅,res)
  | LRnegL (ϕ : Formula) : LocalRule ({ϕ}, {~ϕ}) ∅ --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ({~ϕ}, {ϕ}) ∅ -- ~ϕ occurs on the left side,  ϕ on the right

-- We have equality when types match
instance : DecidableEq (LocalRule LRconds C) := λ_ _ => Decidable.isTrue (sorry)

def TNode := Finset Formula × Finset Formula
  deriving DecidableEq

open HasVocabulary
@[simp]
def jvoc (LR: TNode) := voc LR.1 ∩ voc LR.2

@[simp]
def applyLocalRule (_ : LocalRule (Lcond, Rcond) ress) : TNode → List TNode
  | ⟨L,R⟩ => ress.map $ λc => (L \ Lcond ∪ c.1, R \ Rcond ∪ c.2)

inductive LocalRuleApp : TNode → List TNode → Type
  | mk {L R : Finset Formula}
       {C : List TNode}
       {ress : List SubPair}
       (Lcond Rcond : Finset Formula)
       (rule : LocalRule (Lcond,Rcond) ress)
       {hC : C = applyLocalRule rule (L,R)}
       (preconditionProof : Lcond ⊆ L ∧ Rcond ⊆ R)
       : LocalRuleApp (L,R) C

-- We have equality when types match
instance : DecidableEq (LocalRuleApp LR C) := λ_ _ => Decidable.isTrue (sorry)

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

theorem localRuleAppDecreasesVocab (ruleA : LocalRuleApp LR C)
  : ∀cLR ∈ C, jvoc cLR ⊆ jvoc LR  := sorry


mutual
inductive AppLocalTableau : TNode → List TNode → Type
  | mk {L R : Finset Formula} {C : List TNode}
       (ruleA : LocalRuleApp (L,R) C)
       (subTabs: (Π c ∈ C, LocalTableau c))
       : AppLocalTableau (L, R) C

inductive LocalTableau : TNode → Type
  | fromRule {C : List TNode}  (appTab : AppLocalTableau LR C) : LocalTableau LR
  | fromSimple (isSimple : Simple (L ∪ R)) : LocalTableau (L,R)
end

def getTabRule : AppLocalTableau LR C → Σ Lcond Rcond C, LocalRule (Lcond,Rcond) C
  | AppLocalTableau.mk (ruleA : LocalRuleApp _ _) _ => match ruleA with
    | @LocalRuleApp.mk _ _ _ B Lcond Rcond rule _ _ => ⟨Lcond, Rcond, B, rule⟩

-- We have equality when types match
instance : DecidableEq (AppLocalTableau LR C) := λtab₁ tab₂ => match getTabRule tab₁ == getTabRule tab₂ with
  | true  => Decidable.isTrue  (sorry)
  | false => Decidable.isFalse (sorry)

def getTabChildren : AppLocalTableau LR C →  List TNode
  | @AppLocalTableau.mk _ _ C _ _ => C

@[simp]
def getSubTabs (tab : AppLocalTableau LR C)
  : (Π c ∈ C, LocalTableau c) :=
  match tab with
  | AppLocalTableau.mk _ subTabs => subTabs

-- If X is not simple, then a local rule can be applied.
-- (page 13)

-- write custom tactic later
theorem notSimpleThenLocalRule {L R} : ¬Simple (L ∪ R)
  → ∃ Lcond Rcond C, ∃ _ : LocalRule (Lcond, Rcond) C, Lcond ⊆ L ∧ Rcond ⊆ R :=
  by
  intro notSimple
  unfold Simple at notSimple
  simp at notSimple
  rcases notSimple with ⟨ϕ, ϕ_in_X, ϕ_not_simple⟩
  cases ϕ
  case bottom => tauto
  case atom_prop => tauto
  case neg ψ =>
    cases ψ
    case bottom => tauto
    case atom_prop => tauto
    case neg ψ =>
      cases ϕ_in_X
      · use {~~ψ}; use ∅; use (List.map (fun res => (res, ∅)) [{ψ}])
        use LocalRule.oneSidedL (OneSidedLocalRule.neg ψ)
        aesop
      · use ∅; use {~~ψ}; use (List.map (fun res => (∅, res)) [{ψ}])
        use LocalRule.oneSidedR (OneSidedLocalRule.neg ψ)
        aesop
    case And ψ₁ ψ₂ =>
      cases ϕ_in_X
      · use {~(ψ₁⋀ψ₂)}; use ∅; use (List.map (fun res => (res, ∅)) [{~ψ₁}, {~ψ₂}])
        use LocalRule.oneSidedL (OneSidedLocalRule.ncon ψ₁ ψ₂)
        aesop
      · use ∅; use {~(ψ₁⋀ψ₂)}; use (List.map (fun res => (∅, res)) [{~ψ₁}, {~ψ₂}])
        use LocalRule.oneSidedR (OneSidedLocalRule.ncon ψ₁ ψ₂)
        aesop
    case box => tauto
  case And ψ₁ ψ₂ =>
    cases ϕ_in_X
    · use {ψ₁⋀ψ₂}; use ∅; use (List.map (fun res => (res, ∅)) [{ψ₁, ψ₂}])
      use LocalRule.oneSidedL (OneSidedLocalRule.con ψ₁ ψ₂)
      aesop
    · use ∅; use {ψ₁⋀ψ₂}; use (List.map (fun res => (∅, res)) [{ψ₁, ψ₂}])
      use LocalRule.oneSidedR (OneSidedLocalRule.con ψ₁ ψ₂)
      aesop
  case box => tauto


/- Custom tactic for first two cases? (localruledecrlength)

macro "onesideddecreaseslength" : tactic =>
  `( tactic|
      ( all_goals simp at *
        <;> try rw [c_child]
        case neg φ => simp [←Nat.add_assoc]
        case con φ ψ =>
          simp
          calc
            Finset.sum ({φ, ψ}) (fun x => lengthOfFormula x)
            ≤ lengthOfFormula φ + lengthOfFormula ψ :=
              by
                cases' Classical.em (φ = ψ) with heq hneq
                · simp [heq] at *
                · simp [Finset.sum_pair hneq]
            _ < 1 + lengthOfFormula φ + lengthOfFormula ψ :=
              by aesop
        case ncon φ ψ =>
          cases' c_child with case_phi case_psi
          <;> (first
              | simp [case_psi]
              | ( simp [case_phi];
                  rw [Nat.add_comm 1 (lengthOfFormula φ), Nat.add_assoc];
                  aesop))))

macro "onesideddecreaseslength" : tactic =>
  `( tactic|
      ( all_goals simp at * <;>
        ( repeat'
            solve
            | rw [c_child]
            | simp [←Nat.add_assoc]
            | ( simp
                calc
                  Finset.sum ({φ, ψ}) (fun x => lengthOfFormula x)
                  ≤ lengthOfFormula φ + lengthOfFormula ψ :=
                    by
                      cases' Classical.em (φ = ψ) with heq hneq
                      · simp [heq] at *
                      · simp [Finset.sum_pair hneq]
                  _ < 1 + lengthOfFormula φ + lengthOfFormula ψ :=
                    by aesop)
            | ( cases' c_child with case_phi case_psi
                <;> (first
                    | simp [case_psi]
                    | ( simp [case_phi];
                        rw [Nat.add_comm 1 (lengthOfFormula φ), Nat.add_assoc];
                        aesop))))))

-/

theorem conDecreasesLength {φ ψ : Formula} :
  (Finset.sum {φ, ψ} fun x => lengthOfFormula x) <
    1 + lengthOfFormula φ + lengthOfFormula ψ :=
  by
    calc
      Finset.sum ({φ, ψ}) (fun x => lengthOfFormula x)
      ≤ lengthOfFormula φ + lengthOfFormula ψ :=
        by
          cases' Classical.em (φ = ψ) with heq hneq
          · simp [heq] at *
          · simp [Finset.sum_pair hneq]
      _ < 1 + lengthOfFormula φ + lengthOfFormula ψ :=
        by aesop

theorem localRuleDecreasesLength (rule : LocalRule (Lcond, Rcond) C) :
  ∀c ∈ C, lengthOfSet (c.1 ∪ c.2) < lengthOfSet (Lcond ∪ Rcond) :=
  by
    intro c c_child
    cases rule
    case oneSidedL ress lrule  =>    -- trying custom tactic
      cases lrule
      <;> simp at *
      <;> try rw [c_child]
      case neg φ => simp [←Nat.add_assoc]
      case con φ ψ => simp; exact conDecreasesLength
      case ncon φ ψ =>
        cases' c_child with case_phi case_psi
        <;> (first
            | simp [case_psi]
            | ( simp [case_phi];
                rw [Nat.add_comm 1 (lengthOfFormula φ), Nat.add_assoc];
                aesop))
    case oneSidedR ress rrule  =>
      cases rrule
      <;> simp at *
      <;> try rw [c_child]
      case neg φ => simp [←Nat.add_assoc]
      case con φ ψ => simp; exact conDecreasesLength
      case ncon φ ψ =>
        cases' c_child with case_phi case_psi
        <;> (first
            | simp [case_psi]
            | ( simp [case_phi];
                rw [Nat.add_comm 1 (lengthOfFormula φ), Nat.add_assoc];
                aesop))
    all_goals aesop

theorem localRuleAppDecreasesLength
  {L R : Finset Formula}
  (lrApp : @LocalRuleApp (L,R) C)
  :
  ∀c ∈ C, lengthOfSet (c.1 ∪ c.2) < lengthOfSet (L ∪ R) :=
  by
    intro c c_child
    let ⟨Lcond, Rcond, rule, preconditionProof⟩ := lrApp
    have conds_in_LR : (Lcond ∪ Rcond) ⊆ (L ∪ R) :=
      Finset.union_subset_union preconditionProof.left preconditionProof.right
    have rule_decr_len : lengthOfSet (c.1 ∪ c.2) < lengthOfSet (Lcond ∪ Rcond) := by
      apply localRuleDecreasesLength rule
      sorry
    sorry
    /-
    calc lengthOfSet ((c.1 ∪ c.2))
      ≤ lengthOfSet ((L ∪ R) \ (Lcond ∪ Rcond)) + lengthOfSet (c.1 ∪ c.2) :=
          by simp [sum_union_le]
      _ < lengthOfSet ((L ∪ R) \ (Lcond ∪ Rcond)) + lengthOfSet (Lcond ∪ Rcond) :=
          by apply Nat.add_le_add_left rule_decr_len
      _ = lengthOfSet (L ∪ R) :=
          lengthSetRemove (L ∪ R) (Lcond ∪ Rcond) conds_in_LR
    -/

theorem AppLocalTableau.DecreasesLength {LR : TNode} {C : List TNode} (appTab : AppLocalTableau LR C) {c : TNode}
  (c_in : c ∈ C) :
  lengthOfSet (c.1 ∪ c.2) < lengthOfSet (LR.1 ∪ LR.2) :=
  by
  rcases appTab with ⟨lrApp, next⟩
  have := localRuleAppDecreasesLength lrApp
  unfold applyLocalRule at * -- this actually gives the ... \ ... ∪ ... stuff.
  simp at *
  -- something is stuck or wrong here. Too many unnamed variables.
  sorry


theorem atmRuleDecreasesLength {L R : Finset Formula} {ϕ} :
    ~(□ϕ) ∈ (L ∪ R) → lengthOfSet (projection (L ∪ R) ∪ {~ϕ}) < lengthOfSet (L ∪ R) :=
  by
    let X := (L ∪ R)
    intro notBoxPhi_in_X
    simp
    have otherClaim : projection X = projection (X.erase (~(□ϕ))) :=
      by
      ext1 phi
      rw [proj]; rw [proj]
      simp
    · calc
        lengthOfSet (insert (~ϕ) (projection X)) ≤ lengthOfSet (projection X) + lengthOf (~ϕ) :=
          lengthOf_insert_leq_plus
        _ = lengthOfSet (projection X) + 1 + lengthOf ϕ := by simp; ring
        _ < lengthOfSet (projection X) + 1 + 1 + lengthOf ϕ := by simp
        _ = lengthOfSet (projection X) + lengthOf (~(□ϕ)) := by simp; ring
        _ = lengthOfSet (projection (X.erase (~(□ϕ)))) + lengthOf (~(□ϕ)) := by rw [otherClaim]
        _ ≤ lengthOfSet (X.erase (~(□ϕ))) + lengthOf (~(□ϕ)) := by simp; apply projection_set_length_leq
        _ = lengthOfSet X := lengthRemove X (~(□ϕ)) notBoxPhi_in_X

-- Definition 8, page 14
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau for X, must be maximal



-- Definition 8, page 14
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau for X, must be maximal

def existsLocalTableauFor LR : Nonempty (LocalTableau LR) :=
  by
    cases em ¬(∃ Lcond Rcond C, Nonempty (LocalRule (Lcond, Rcond) C))
    case inl canApplyRule =>
      constructor
      apply LocalTableau.fromSimple
      by_contra hyp
      have := notSimpleThenLocalRule hyp
      aesop
    case inr canApplyRule =>
      simp at canApplyRule
      cases' canApplyRule with B r_exists
      cases' r_exists with r
      cases r
      sorry
      -- case bot h =>
      --   use (LocalTableau.byLocalRule (LocalRule.bot h) ?_)
      --   intro Y; intro Y_in_empty; tauto
      -- case Not h =>
      --   use (LocalTableau.byLocalRule (LocalRule.Not h) ?_)
      --   intro Y; intro Y_in_empty; tauto
      -- case neg f h =>
      --   use (LocalTableau.byLocalRule (LocalRule.neg h) ?_)
      --   intro Y Y_def
      --   have := localRulesDecreaseLength (LocalRule.neg h) Y Y_def
      --   apply Classical.choice (existsLocalTableauFor Y)
      -- case Con f g h =>
      --   use (LocalTableau.byLocalRule (LocalRule.Con h) ?_)
      --   intro Y Y_def
      --   have := localRulesDecreaseLength (LocalRule.Con h) Y Y_def
      --   apply Classical.choice (existsLocalTableauFor Y)
      -- case nCo f g h =>
      --   use (LocalTableau.byLocalRule (LocalRule.nCo h) ?_)
      --   intro Y Y_def
      --   have := localRulesDecreaseLength (LocalRule.nCo h) Y Y_def
      --   apply Classical.choice (existsLocalTableauFor Y)

    -- termination_by
    --   existsLocalTableauFor α => lengthOf α


open LocalTableau

-- needed for endNodesOf
instance localTableauHasLength : HasLength (Σ LR, LocalTableau LR) :=
  ⟨fun ⟨(L, R), _⟩ => lengthOfSet (L ∪ R)⟩

-- open end nodes of a given localTableau
def endNodesOf : (Σ LR, LocalTableau LR) → List TNode
  | ⟨LR, @LocalTableau.fromRule _ C (appTab : AppLocalTableau LR C)⟩ =>
    (C.attach.map fun ⟨c, c_in⟩ =>
      have tc : LocalTableau c := getSubTabs appTab c c_in
      have : lengthOfSet (c.1 ∪ c.2) < lengthOfSet (LR.1 ∪ LR.2) := AppLocalTableau.DecreasesLength appTab c_in
      endNodesOf ⟨c, tc⟩
      ).join
  | ⟨LR, LocalTableau.fromSimple _⟩ => [LR]
termination_by
  endNodesOf pair => lengthOf pair

@[simp]
theorem endNodesOfSimple : endNodesOf ⟨ LR, LocalTableau.fromSimple hyp ⟩ = [LR] := by
  sorry

-- can't we just combine all these functions and say
-- that the end nodes of a tableau = end nodes of all its children
-- also I'm not sure we even use these
@[simp]
theorem lrEndNodes {LR C subtabs lrApp} :   -- fewer arguments = error
    endNodesOf ⟨LR, LocalTableau.fromRule
    (@AppLocalTableau.mk LR.1 LR.2 C lrApp subtabs)⟩ = (C.attach.map (fun ⟨c, c_in⟩  =>
      endNodesOf ⟨c, subtabs c c_in⟩) ).join :=
  by
  rcases lrApp with ⟨_, _, rule, _⟩
  simp
  sorry

theorem endNodesOfLEQ {LR Z ltLR} : Z ∈ endNodesOf ⟨LR, ltLR⟩ → lengthOf (Z.1 ∪ Z.2) ≤ lengthOf (LR.1 ∪ LR.2) :=
  by
  cases ltLR   -- mutually inductive type problem, I remember this from the chat?
  case fromRule altLR =>
    intro Z_endOf_LR
    let ⟨lrApp, next⟩ := altLR
    simp at Z_endOf_LR
    rcases Z_endOf_LR with ⟨ZS, ⟨c, c_in_C, endNodes_c_eq_ZS⟩, Z_in_ZS⟩
    subst endNodes_c_eq_ZS
    apply le_of_lt
    have := localRuleAppDecreasesLength lrApp c c_in_C -- for termination and below!
    · calc
        lengthOf (Z.1 ∪ Z.2) ≤ lengthOf (c.1 ∪ c.2) := endNodesOfLEQ Z_in_ZS
        _ < lengthOf (LR.1 ∪ LR.2) := this
  case fromSimple LR_simp =>
    intro Z_endOf_Y
    simp at Z_endOf_Y
    aesop
termination_by
  endNodesOfLEQ LT   => lengthOfSet (LR.1 ∪ LR.2)

theorem endNodesOfLocalRuleLT {LR Z appTab} :
    Z ∈ endNodesOf ⟨LR, LocalTableau.fromRule appTab⟩ → lengthOf (Z.1 ∪ Z.2) < lengthOf (LR.1 ∪ LR.2) :=
  by
  intro Z_endOf_LR
  cases' appTab with L R _ lrApp next
  simp at Z_endOf_LR
  rcases Z_endOf_LR with ⟨ZS, ⟨c, c_in_C, endNodes_c_eq_ZS⟩, Z_in_ZS⟩
  subst endNodes_c_eq_ZS
  have := localRuleAppDecreasesLength lrApp c c_in_C -- for termination and below!
  · calc
      lengthOf (Z.1 ∪ Z.2) ≤ lengthOf (c.1 ∪ c.2) := endNodesOfLEQ Z_in_ZS
      _ < lengthOf (L ∪ R) := this


-- Definition 16, page 29
-- prob need to change def of projection s.t. it goes TNode → TNode
-- is the base case missing for simple tableaux?
inductive ClosedTableau : TNode → Type
  | loc {LR} {appTab : AppLocalTableau LR} (lt : LocalTableau.fromRule appTab) : (∀ Y ∈ endNodesOf ⟨LR, lt⟩, ClosedTableau Y) → ClosedTableau LR
  | atm {LR ϕ} : ~(□ϕ) ∈ (L ∪ R) → Simple (L ∪ R) → ClosedTableau (projection (L ∪ R) ∪ {~ϕ}) → ClosedTableau X

inductive Provable : Formula → Prop   -- this doesn't work anymore with TNodes
  | byTableau {φ : Formula} : ClosedTableau {~φ} → Provable φ

-- Definition 17, page 30
def Inconsistent : TNode → Prop
  | LR => Nonempty (ClosedTableau LR)

def Consistent : TNode → Prop      -- invalid occurrence of universe level 'u_1' at 'Consistent'?
  | LR => ¬Inconsistent LR



/-   pretty sure this is all old stuff


-- A tableau may be open.
-- But if it's open, then it comes with proofs that it cannot be closed.
inductive Tableau : Finset Formula → Type
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, Tableau Y) → Tableau X
  | atm {X ϕ} : ~(□ϕ) ∈ X → Simple X → Tableau (projection X ∪ {~ϕ}) → Tableau X
  | opn {X} : Simple X → (∀ φ, ~(□φ) ∈ X → IsEmpty (ClosedTableau (projection X ∪ {~φ}))) → Tableau X

def isOpen : Tableau X → Prop
  | (Tableau.loc lt next) => ∃ Y, ∃ h : Y ∈ endNodesOf ⟨X, lt⟩, isOpen (next Y h) -- mwah?!
  | (Tableau.atm _ _ t_proj) => isOpen t_proj
  | (Tableau.opn _ _) => True

def isClosed : Tableau X → Prop
  | (Tableau.loc lt next) => ∀ Y, ∀ h : Y ∈ endNodesOf ⟨X, lt⟩, isClosed (next Y h) -- mwah?!
  | (Tableau.atm _ _ t_proj) => isClosed t_proj
  | (Tableau.opn _ _) => False

theorem open_iff_notClosed {X} {t : Tableau X} : isOpen t ↔ ¬ isClosed t :=
  by
  induction t
  all_goals
    simp [isOpen, isClosed]
    try assumption
  case loc Y ltY next IH  =>
    constructor
    · rintro ⟨Z, Z_in, Z_isOp⟩
      specialize IH Z Z_in
      use Z, Z_in
      rw [← IH]
      exact Z_isOp
    · rintro ⟨Z, Z_in, Z_notClosed⟩
      specialize IH Z Z_in
      use Z, Z_in
      rw [IH]
      exact Z_notClosed

def OpenTableau (X : Finset Formula) : Type := { t : Tableau X // isOpen t }

def injectTab : ClosedTableau X → Tableau X
  | (ClosedTableau.loc lt ends) => Tableau.loc lt (λ _ Y_in => injectTab (ends _ Y_in))
  | (ClosedTableau.atm nB_in_X simX ctProj) => Tableau.atm nB_in_X simX (injectTab ctProj)

def existsTableauFor α : Nonempty (Tableau α) :=
  by
  cases em (∃ B, Nonempty (LocalRule α B))
  case inl canApplyRule =>
    rcases canApplyRule with ⟨YS, has_lr⟩
    cases' has_lr with lr
    constructor
    apply Tableau.loc (LocalTableau.byLocalRule lr _) _
    · intro Y _
      exact Classical.choice (existsLocalTableauFor Y)
    · intro Y Y_in_ends
      apply Classical.choice
      have : lengthOf Y < lengthOf α := endNodesOfLocalRuleLT Y_in_ends
      exact existsTableauFor _
  case inr canNotApplyRule =>
    have is_simp : Simple α := by
      by_contra hyp
      have := @notSimpleThenLocalRule α hyp
      absurd canNotApplyRule
      exact this
    cases em (∀ φ, ~(□φ) ∈ α → IsEmpty (ClosedTableau (projection α ∪ {~φ})))
    case inl hasNoClosedDiamonds => exact ⟨Tableau.opn is_simp hasNoClosedDiamonds⟩
    case inr hasClosedDiamond =>
      simp only [not_forall, not_isEmpty_iff, exists_prop] at hasClosedDiamond
      rcases hasClosedDiamond with ⟨f, nBf_in_a, ⟨ct_notf⟩⟩
      exact ⟨Tableau.atm nBf_in_a is_simp (injectTab ct_notf)⟩
termination_by
  existsTableauFor α => lengthOf α
-/
