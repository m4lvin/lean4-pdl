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

def TNode := Finset Formula × Finset Formula
  deriving DecidableEq

def Simple : TNode → Bool
  | ⟨L,R⟩ => ∀ P ∈ L ∪ R, SimpleForm P

-- Let X_A := { R | [A]R ∈ X }.
@[simp]
def formProjection : Formula → Option Formula
  | □f => some f
  | _ => none

def projection : Finset Formula → Finset Formula
  | X => X.biUnion fun x => (formProjection x).toFinset

def projectTNode : TNode → TNode
  | (L, R) => (projection L, projection R)

@[simp]
def f_in_TNode (f : Formula) (LR : TNode) := f ∈ (LR.1 ∪ LR.2)

@[simp]
instance TNodeHasSat : HasSat TNode :=
  HasSat.mk fun LR => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ, f_in_TNode φ (LR) → Evaluate (M, w) φ

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

open HasVocabulary
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
  deriving DecidableEq -- also works, delete the instance below?

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
  | fromSimple (isSimple : Simple (L, R)) : LocalTableau (L,R)
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
theorem notSimpleThenLocalRule {L R} : ¬Simple (L, R)
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

@[simp]
def lengthOfTNode : TNode → Nat
  | (L,R) => lengthOfSet L + lengthOfSet R

-- needed for endNodesOf
@[simp]
instance TNodeHasLength : HasLength TNode := ⟨lengthOfTNode⟩

theorem localRuleDecreasesLengthSide (rule : LocalRule (Lcond, Rcond) ress) :
  ∀ res ∈ ress,
      (lengthOf res.1 < lengthOf Lcond ∧ res.2 = ∅)
    ∨ (lengthOf res.2 < lengthOf Rcond ∧ res.1 = ∅) :=
    by
    intro res in_ress
    cases rule
    case oneSidedL _ lrule  =>    -- trying custom tactic
      cases lrule
      <;> simp at *
      <;> try rw [in_ress]
      case neg φ => simp [←Nat.add_assoc]
      case con φ ψ => simp; exact conDecreasesLength
      case ncon φ ψ =>
        cases' in_ress with case_phi case_psi
        <;> (first
            | simp [case_psi]
            | ( simp [case_phi];
                rw [Nat.add_comm 1 (lengthOfFormula φ), Nat.add_assoc];
                aesop))
    case oneSidedR _ rrule  =>
      cases rrule
      <;> simp at *
      <;> try rw [in_ress]
      case neg φ => simp [←Nat.add_assoc]
      case con φ ψ => simp; exact conDecreasesLength
      case ncon φ ψ =>
        cases' in_ress with case_phi case_psi
        <;> (first
            | simp [case_psi]
            | ( simp [case_phi];
                rw [Nat.add_comm 1 (lengthOfFormula φ), Nat.add_assoc];
                aesop))
    all_goals aesop

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
    have := localRuleDecreasesLengthSide rule res res_in_ress
    cases this
    case inl hyp =>
      calc lengthOfTNode c
      = lengthOfSet (L \ Lcond ∪ res.1) + lengthOfSet (R \ Rcond ∪ res.2) :=
          by subst def_c; simp
      _ ≤ lengthOfSet (L \ Lcond ∪ res.1) + lengthOfSet R :=
          by rw [hyp.2]; simp [Finset.sum_le_sum_of_subset]
      _ < lengthOfSet L + lengthOfSet R :=
          by simp at hyp; simp; sorry -- should be easy, use hyp?
      _ = lengthOfTNode (L, R) := by simp
    case inr hyp =>
      calc lengthOfTNode c
      = lengthOfSet (L \ Lcond ∪ res.1) + lengthOfSet (R \ Rcond ∪ res.2) :=
          by subst def_c; simp
      _ ≤ lengthOfSet L + lengthOfSet (R \ Rcond ∪ res.2) :=
          by rw [hyp.2]; simp [Finset.sum_le_sum_of_subset]
      _ < lengthOfSet L + lengthOfSet R :=
          by simp at hyp; simp; sorry -- should be easy, use hyp?
      _ = lengthOfTNode (L, R) := by simp

theorem AppLocalTableau.DecreasesLength
  (appTab : AppLocalTableau LR C)
  (c_in : c ∈ C) :
  lengthOfTNode c < lengthOfTNode LR :=
  by
  rcases appTab with ⟨lrApp, next⟩
  have := localRuleAppDecreasesLength lrApp
  aesop

-- Lift definition of projection to TNodes, including the diamond formula left or right.
def diamondProjectTNode : Sum Formula Formula → TNode → TNode
| (Sum.inl φ), (L, R) => (projection L ∪ {φ}, projection R)
| (Sum.inr φ), (L, R) => (projection L, projection R ∪ {φ})

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
        lengthOfSet (projection X ∪ {~φ}) ≤ lengthOfSet (projection X) + lengthOf (~φ) :=
            by rw [union_singleton_is_insert]; exact lengthOf_insert_leq_plus
          _ = lengthOfSet (projection X) + 1 + lengthOf φ := by simp; ring
          _ < lengthOfSet (projection X) + 1 + 1 + lengthOf φ := by simp
          _ = lengthOfSet (projection X) + lengthOf (~(□φ)) := by simp; ring
          _ = lengthOfSet (projection (X.erase (~(□φ)))) + lengthOf (~(□φ)) := by rw [otherClaim]
          _ ≤ lengthOfSet (X.erase (~(□φ))) + lengthOf (~(□φ)) := by simp; apply projection_set_length_leq
          _ = lengthOfSet X := lengthRemove X (~(□φ)) notBoxPhi_in_X

theorem atmRuleLDecreasesLength {L R : Finset Formula} {φ} :
    ~(□φ) ∈ L → lengthOfTNode (diamondProjectTNode (Sum.inl (~φ)) (L, R)) < lengthOfTNode (L, R) :=
  by
    intro notBoxPhi_in_L
    have lengthL : lengthOfSet (projection L ∪ {~φ}) < lengthOfSet L := projDecreasesLength notBoxPhi_in_L
    · calc
        lengthOfTNode (diamondProjectTNode (Sum.inl (~φ)) (L, R))
          = lengthOfSet (projection L ∪ {~φ}) + lengthOfSet (projection R) := by tauto
          _ ≤ lengthOfSet (projection L ∪ {~φ}) + lengthOfSet R := by
            have lengthR : lengthOfSet (projection R) ≤ lengthOfSet R :=
              by apply projection_set_length_leq
            apply Nat.add_le_add_left lengthR
          _ < lengthOfSet L + lengthOfSet R := by apply Nat.add_lt_add_right lengthL
          _ = lengthOfTNode (L, R) := by rw [lengthOfTNode]

theorem atmRuleRDecreasesLength {L R : Finset Formula} {φ} :
    ~(□φ) ∈ R → lengthOfTNode (diamondProjectTNode (Sum.inr (~φ)) (L, R)) < lengthOfTNode (L, R) :=
  by
    intro notBoxPhi_in_R
    have lengthR : lengthOfSet (projection R ∪ {~φ}) < lengthOfSet R := projDecreasesLength notBoxPhi_in_R
    · calc
        lengthOfTNode (diamondProjectTNode (Sum.inr (~φ)) (L, R))
          = lengthOfSet (projection L) + lengthOfSet (projection R ∪ {~φ}) := by tauto
          _ ≤ lengthOfSet L + lengthOfSet (projection R ∪ {~φ}) := by
            have lengthL : lengthOfSet (projection L) ≤ lengthOfSet L :=
              by apply projection_set_length_leq
            apply Nat.add_le_add_right lengthL
          _ < lengthOfSet L + lengthOfSet R := by apply Nat.add_lt_add_left lengthR
          _ = lengthOfTNode (L, R) := by rw [lengthOfTNode]


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
  ⟨fun ⟨(L, R), _⟩ => lengthOfTNode (L, R)⟩

-- open end nodes of a given localTableau
def endNodesOf : (Σ LR, LocalTableau LR) → List TNode
  | ⟨LR, @LocalTableau.fromRule _ C (appTab : AppLocalTableau LR C)⟩ =>
    (C.attach.map fun ⟨c, c_in⟩ =>
      have tc : LocalTableau c := getSubTabs appTab c c_in
      have : lengthOfTNode c < lengthOfTNode LR := AppLocalTableau.DecreasesLength appTab c_in
      endNodesOf ⟨c, tc⟩
      ).join
  | ⟨LR, LocalTableau.fromSimple _⟩ => [LR]
termination_by
  endNodesOf pair => lengthOf pair

@[simp]
theorem endNodesOfSimple : endNodesOf ⟨ LR, LocalTableau.fromSimple hyp ⟩ = [LR] := by
  sorry

@[simp]
theorem lrEndNodes {LR C subtabs lrApp} :
    endNodesOf ⟨LR, LocalTableau.fromRule
    (@AppLocalTableau.mk LR.1 LR.2 C lrApp subtabs)⟩ = (C.attach.map (fun ⟨c, c_in⟩  =>
      endNodesOf ⟨c, subtabs c c_in⟩) ).join :=
    by sorry

theorem endNodesOfLEQ {LR Z ltLR} : Z ∈ endNodesOf ⟨LR, ltLR⟩ → lengthOfTNode Z ≤ lengthOfTNode LR :=
  by
  cases ltLR
  case fromRule altLR =>
    intro Z_endOf_LR
    let ⟨lrApp, next⟩ := altLR
    simp at Z_endOf_LR
    rcases Z_endOf_LR with ⟨ZS, ⟨c, c_in_C, endNodes_c_eq_ZS⟩, Z_in_ZS⟩
    subst endNodes_c_eq_ZS
    apply le_of_lt
    have := localRuleAppDecreasesLength lrApp c c_in_C -- for termination and below!
    · calc
        lengthOfTNode Z ≤ lengthOfTNode c := endNodesOfLEQ Z_in_ZS
        _ < lengthOfTNode LR := this
  case fromSimple LR_simp =>
    intro Z_endOf_Y
    simp at Z_endOf_Y
    aesop
termination_by
  endNodesOfLEQ LT   => lengthOfTNode LR

theorem endNodesOfLocalRuleLT {LR Z} {appTab : AppLocalTableau LR C} :
    Z ∈ endNodesOf ⟨LR, LocalTableau.fromRule appTab⟩ → lengthOfTNode Z < lengthOfTNode LR :=
  by
  intro Z_endOf_LR
  cases' appTab with L R _ lrApp next
  simp at Z_endOf_LR
  rcases Z_endOf_LR with ⟨ZS, ⟨c, c_in_C, endNodes_c_eq_ZS⟩, Z_in_ZS⟩
  subst endNodes_c_eq_ZS
  have := localRuleAppDecreasesLength lrApp c c_in_C -- for termination and below!
  · calc
      lengthOfTNode Z ≤ lengthOfTNode c := endNodesOfLEQ Z_in_ZS
      _ < lengthOfTNode (L,R) := this

-- Definition 16, page 29
-- Note that the base case for simple tableaux is part of the
-- atomic rule "atm" which can be applied to L or to R.
inductive ClosedTableau : TNode → Type
  | loc {LR} {appTab : AppLocalTableau LR C} (lt : LocalTableau LR) : (∀ Y ∈ endNodesOf ⟨LR, lt⟩, ClosedTableau Y) → ClosedTableau LR
  | atmL {LR ϕ} : ~(□ϕ) ∈ L → Simple (L, R) → ClosedTableau (diamondProjectTNode (Sum.inl (~ϕ)) LR) → ClosedTableau LR
  | atmR {LR ϕ} : ~(□ϕ) ∈ R → Simple (L, R) → ClosedTableau (diamondProjectTNode (Sum.inr (~ϕ)) LR) → ClosedTableau LR

inductive Provable : Formula → Prop
  | byTableau {φ : Formula} : ClosedTableau ({~φ},{}) → Provable φ

inductive ProvableImplication : Formula → Formula → Prop
  | byTableau : ClosedTableau ({φ},{~ψ}) → ProvableImplication φ ψ

-- Definition 17, page 30
def Inconsistent : TNode → Prop
  | LR => Nonempty (ClosedTableau LR)

def Consistent : TNode → Prop      -- invalid occurrence of universe level 'u_1' at 'Consistent'?
  | LR => ¬Inconsistent LR


/- TODO: old stuff about open tableaux, will be needed for BetterCompleteness


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
