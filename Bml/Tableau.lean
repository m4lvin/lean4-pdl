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
import Bml.Vocabulary -- TODO remove

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

inductive OneSidedLocalRule
  | bot
  | not  (ϕ   : Formula)
  | neg  (ϕ   : Formula)
  | con  (ϕ ψ : Formula)
  | ncon (ϕ ψ : Formula)

inductive LocalRule where
  | oneSidedL (orule : OneSidedLocalRule) : LocalRule
  | oneSidedR (orule : OneSidedLocalRule) : LocalRule
  | LRnegL (ϕ : Formula) --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) -- ~ϕ occurs on the left side,  ϕ on the right

deriving instance DecidableEq for OneSidedLocalRule
deriving instance DecidableEq for LocalRule


@[simp]
def OneSidedLocalRuleToPrecondition (orule : OneSidedLocalRule) : (Finset Formula → Prop) :=
  match orule with
  | OneSidedLocalRule.bot      => λX => ⊥ ∈ X
  | OneSidedLocalRule.not  ϕ   => λX => ϕ ∈ X ∧ ¬ϕ ∈ X
  | OneSidedLocalRule.neg  ϕ   => λX =>   ~~ϕ  ∈ X
  | OneSidedLocalRule.con  ϕ ψ => λX =>   ϕ⋀ψ  ∈ X
  | OneSidedLocalRule.ncon ϕ ψ => λX => ~(ϕ⋀ψ) ∈ X

@[simp]
def LocalRuleToPrecondition (rule : LocalRule) : (Finset Formula → Finset Formula → Prop) :=
  match rule with
  | LocalRule.oneSidedL orule => λL _ => OneSidedLocalRuleToPrecondition orule L
  | LocalRule.oneSidedR orule => λ_ R => OneSidedLocalRuleToPrecondition orule R
  | LocalRule.LRnegL ϕ => λL R =>  ϕ ∈ L ∧ ~ϕ ∈ R
  | LocalRule.LRnegR ϕ => λL R => ~ϕ ∈ L ∧  ϕ ∈ R

@[simp]
def OneSidedLocalRuleToChildren  (orule : OneSidedLocalRule) : Finset Formula → Finset (Finset Formula) :=
  match orule with
  | OneSidedLocalRule.bot      => λ_ => ∅
  | OneSidedLocalRule.not  _   => λ_ => ∅
  | OneSidedLocalRule.neg  ϕ   => λX => {X \ {~~ϕ} ∪ {ϕ}}
  | OneSidedLocalRule.con  ϕ ψ => λX => {X \ {ϕ⋀ψ} ∪ {ϕ, ψ}}
  | OneSidedLocalRule.ncon ϕ ψ => λX => {X \ {~(ϕ⋀ψ)} ∪ {~ϕ}, X \ {~(ϕ⋀ψ)} ∪ {~ψ}}

@[simp]
def LocalRuleToChildren (rule : LocalRule) (L R : Finset Formula) : Finset (Finset Formula × Finset Formula) :=
  match rule with
  | LocalRule.oneSidedL orule => (OneSidedLocalRuleToChildren orule L).image (λL₂ => (L₂,R))
  | LocalRule.oneSidedR orule => (OneSidedLocalRuleToChildren orule R).image (λR₂ => (L,R₂))
  | LocalRule.LRnegL _ => ∅
  | LocalRule.LRnegR _ => ∅

inductive LocalTableau : Finset Formula → Finset Formula → Type
  | mk {L R : Finset Formula}
       (rule : LocalRule)
       (preconditionProof : LocalRuleToPrecondition rule L R)
       (children: (Π childLR ∈ LocalRuleToChildren rule L R, LocalTableau childLR.fst childLR.snd))
       : LocalTableau L R

def tabToRule : LocalTableau L R → LocalRule
  | LocalTableau.mk rule _ _ => rule

def tabToChildrenTypes (tab : LocalTableau L R)
  : Finset (Finset Formula × Finset Formula)
  := LocalRuleToChildren (tabToRule tab) L R

def tabToChildrenTabs (tab : LocalTableau L R)
  : (Π childLR ∈ tabToChildrenTypes tab, LocalTableau childLR.fst childLR.snd) :=
  match tab with
  | LocalTableau.mk _ _ children => children

inductive AggregationType
  | Constant (ϕ : Formula)
  | Conjunction
  | Disjunction

open AggregationType

def localRuleToAggregationType : LocalRule -> AggregationType
  | LocalRule.oneSidedL _ => Disjunction
  | LocalRule.oneSidedR _ => Conjunction
  | LocalRule.LRnegL ϕ => Constant   ϕ
  | LocalRule.LRnegR ϕ => Constant (~ϕ)

noncomputable def aggregationTypeToFunction (atype : AggregationType)
  : Finset Formula → Formula := match atype with
  | Constant ϕ  => λ_ => ϕ
  | Conjunction => BigConjunction
  | Disjunction => BigDisjunction


--BEGIN move to proper files
-- included to indicate types for parts of Partitions; Soundness; Completeness
-- and to enable typechecking for so long as Tableau does not compile yet
-- should in the end be moved back to their respective files
open HasVocabulary HasSat

def PartInterpolant (X1 X2 : Finset Formula) (θ : Formula) :=
  voc θ ⊆ voc X1 ∩ voc X2 ∧ ¬Satisfiable (X1 ∪ {~θ}) ∧ ¬Satisfiable (X2 ∪ {θ})

theorem localRuleCompleteness (rule : LocalRule) (L R : Finset Formula)
  : ∃LR ∈ LocalRuleToChildren rule L R, Satisfiable (LR.fst ∪ LR.snd) → Satisfiable (L ∪ R) := sorry

theorem localRuleDecreasesVocab (rule : LocalRule) (L R : Finset Formula)
  : ∀LR ∈ LocalRuleToChildren rule L R, voc LR.fst ⊆ voc L ∧ voc LR.snd ⊆ voc R := sorry

theorem InterpolantInductionStep
  (L R : Finset Formula)
  (tab : LocalTableau L R)
  (subInterpolants : tabToChildrenTypes tab → Formula)
  (hsubInterpolants : Π cLRP ∈ (tabToChildrenTypes tab).attach, PartInterpolant cLRP.val.fst cLRP.val.snd (subInterpolants cLRP))
  : (∃θ : Formula, PartInterpolant L R θ) :=
  by
    let aggregationType := localRuleToAggregationType $ tabToRule tab
    let interpolant     := aggregationTypeToFunction aggregationType ((tabToChildrenTypes tab).attach.image subInterpolants)
    use interpolant
    constructor
    --voc property
    · cases aggregationType
      -- case constant ϕ: use that ϕ appears in both sides
      · sorry
      -- other cases: use that p ∈ ⋀θ_i → ∃θ_i, p ∈ θ_i → p ∈ L by localRuleDecreasesVocab , and ismilar
      · sorry
      · sorry
    --implication property
    · cases aggregationType
      -- case constant ϕ: use the tab preconditionProof
      · sorry
      -- other cases: result follows directly from localRuleSoundness and IH's
      · sorry
      · sorry

-- END move to proper files

-- If X is not simple, then a local rule can be applied.
-- (page 13)
theorem notSimpleThenLocalRule {X} : ¬Simple X → ∃ B, Nonempty (LocalRule X B) :=
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
      use{X \ {~~ψ} ∪ {ψ}}
      use LocalRule.neg ϕ_in_X
    case And ψ1 ψ2 =>
      use{X \ {~(ψ1⋀ψ2)} ∪ {~ψ1}, X \ {~(ψ1⋀ψ2)} ∪ {~ψ2}}
      use LocalRule.nCo ϕ_in_X
    case box => tauto
  case And ψ1 ψ2 =>
    use{X \ {ψ1⋀ψ2} ∪ {ψ1, ψ2}}
    use LocalRule.Con ϕ_in_X
  case box => tauto

theorem localRulesDecreaseLength {X : Finset Formula} {B : Finset (Finset Formula)}
    (r : LocalRule X B) : ∀ Y ∈ B, lengthOfSet Y < lengthOfSet X :=
  by
  cases r
  all_goals intro β inB; simp at *
  case neg ϕ notnot_in_X =>
    subst inB
    · calc
        lengthOfSet (insert ϕ (X.erase (~~ϕ))) ≤ lengthOfSet (X.erase (~~ϕ)) + lengthOf ϕ := by
          apply lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~~ϕ)) + lengthOf ϕ + 2 := by simp
        _ = lengthOfSet (X.erase (~~ϕ)) + lengthOf (~~ϕ) := by simp; ring
        _ = lengthOfSet X := lengthRemove X (~~ϕ) notnot_in_X
  case Con ϕ ψ in_X =>
    subst inB
    · calc
        lengthOf (insert ϕ (insert ψ (X.erase (ϕ⋀ψ)))) ≤
            lengthOf (insert ψ (X.erase (ϕ⋀ψ))) + lengthOf ϕ :=
          by apply lengthOf_insert_leq_plus
        _ ≤ lengthOf (X.erase (ϕ⋀ψ)) + lengthOf ψ + lengthOf ϕ := by simp; apply lengthOf_insert_leq_plus
        _ = lengthOf (X.erase (ϕ⋀ψ)) + lengthOf ϕ + lengthOf ψ := by ring
        _ < lengthOf (X.erase (ϕ⋀ψ)) + lengthOf ϕ + lengthOf ψ + 1 := by simp
        _ = lengthOf (X.erase (ϕ⋀ψ)) + lengthOf (ϕ⋀ψ) := by simp; ring
        _ = lengthOfSet X := lengthRemove X (ϕ⋀ψ) in_X
  case nCo ϕ ψ in_X =>
    cases inB
    -- splitting rule!
    case inl inB => -- f
      subst inB
      calc  lengthOfSet (insert (~ϕ) (X.erase (~(ϕ⋀ψ))))
          ≤ lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~ϕ) := lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~(ϕ⋀ψ))) + 1 + (1 + lengthOf ϕ) := by simp
        _ ≤ lengthOfSet (X.erase (~(ϕ⋀ψ))) + 1 + (1 + lengthOf ϕ) + lengthOf ψ := by simp
        _ = lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~(ϕ⋀ψ)) := by simp; ring
        _ = lengthOfSet X := lengthRemove X (~(ϕ⋀ψ)) in_X
    case inr inB => -- g
      subst inB
      calc  lengthOfSet (insert (~ψ) (X.erase (~(ϕ⋀ψ))))
          ≤ lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~ψ) := lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~(ϕ⋀ψ))) + 1 + (1 + lengthOf ψ) := by simp
        _ ≤ lengthOfSet (X.erase (~(ϕ⋀ψ))) + 1 + lengthOf ϕ + (1 + lengthOf ψ) := by simp
        _ = lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~(ϕ⋀ψ)) := by simp; ring
        _ = lengthOfSet X := lengthRemove X (~(ϕ⋀ψ)) in_X

theorem atmRuleDecreasesLength {X : Finset Formula} {ϕ} :
    ~(□ϕ) ∈ X → lengthOfSet (projection X ∪ {~ϕ}) < lengthOfSet X :=
  by
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


def existsLocalTableauFor α : Nonempty (LocalTableau α) :=
  by
  cases em ¬∃ B, Nonempty (LocalRule α B)
  case inl canApplyRule =>
    constructor
    apply LocalTableau.sim
    by_contra hyp
    have := notSimpleThenLocalRule hyp
    tauto
  case inr canApplyRule =>
    simp at canApplyRule
    cases' canApplyRule with B r_exists
    cases' r_exists with r
    cases r
    case bot h =>
      use (LocalTableau.byLocalRule (LocalRule.bot h) ?_)
      intro Y; intro Y_in_empty; tauto
    case Not h =>
      use (LocalTableau.byLocalRule (LocalRule.Not h) ?_)
      intro Y; intro Y_in_empty; tauto
    case neg f h =>
      use (LocalTableau.byLocalRule (LocalRule.neg h) ?_)
      intro Y Y_def
      have := localRulesDecreaseLength (LocalRule.neg h) Y Y_def
      apply Classical.choice (existsLocalTableauFor Y)
    case Con f g h =>
      use (LocalTableau.byLocalRule (LocalRule.Con h) ?_)
      intro Y Y_def
      have := localRulesDecreaseLength (LocalRule.Con h) Y Y_def
      apply Classical.choice (existsLocalTableauFor Y)
    case nCo f g h =>
      use (LocalTableau.byLocalRule (LocalRule.nCo h) ?_)
      intro Y Y_def
      have := localRulesDecreaseLength (LocalRule.nCo h) Y Y_def
      apply Classical.choice (existsLocalTableauFor Y)
termination_by
  existsLocalTableauFor α => lengthOf α

open LocalTableau

-- needed for endNodesOf
instance localTableauHasSizeof : SizeOf (Σ X, LocalTableau X) :=
  ⟨fun ⟨X, _⟩ => lengthOfSet X⟩

-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, LocalTableau X) → Finset (Finset Formula)
  | ⟨X, @byLocalRule _ B lr next⟩ =>
    B.attach.biUnion fun ⟨Y, h⟩ =>
      have : lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h
      endNodesOf ⟨Y, next Y h⟩
  | ⟨X, sim _⟩ => {X}

@[simp]
theorem botNoEndNodes {X h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.bot X h) n⟩ = ∅ := by unfold endNodesOf; simp

@[simp]
theorem notNoEndNodes {X h ϕ n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.Not X h ϕ) n⟩ = ∅ := by unfold endNodesOf; simp

theorem negEndNodes {X ϕ h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.neg X ϕ h) n⟩ =
      endNodesOf ⟨X \ {~~ϕ} ∪ {ϕ}, n (X \ {~~ϕ} ∪ {ϕ}) (by simp)⟩ :=
  by
  ext1
  simp only [endNodesOf, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_attach,
    exists_true_left, Subtype.exists]
  constructor
  · intro lhs; rcases lhs with ⟨b, bDef, bIn⟩; subst bDef; simp at *; exact bIn
  · intro rhs; use X \ {~~ϕ} ∪ {ϕ}; constructor; simp at *; exact rhs; rfl

theorem conEndNodes {X ϕ ψ h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.Con X ϕ ψ h) n⟩ =
      endNodesOf ⟨X \ {ϕ⋀ψ} ∪ {ϕ, ψ}, n (X \ {ϕ⋀ψ} ∪ {ϕ, ψ}) (by simp)⟩ :=
  by
  ext1
  simp only [endNodesOf, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_attach,
    exists_true_left, Subtype.exists]
  constructor
  · intro lhs; rcases lhs with ⟨b, bDef, bIn⟩; subst bDef; simp at *; exact bIn
  · intro rhs; use X \ {ϕ⋀ψ} ∪ {ϕ, ψ}; constructor; simp at *; exact rhs; rfl

theorem nCoEndNodes {X ϕ ψ h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.nCo X ϕ ψ h) n⟩ =
      endNodesOf ⟨X \ {~(ϕ⋀ψ)} ∪ {~ϕ}, n (X \ {~(ϕ⋀ψ)} ∪ {~ϕ}) (by simp)⟩ ∪
        endNodesOf ⟨X \ {~(ϕ⋀ψ)} ∪ {~ψ}, n (X \ {~(ϕ⋀ψ)} ∪ {~ψ}) (by simp)⟩ :=
  by
  ext1
  simp only [endNodesOf, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_attach,
    exists_true_left, Subtype.exists]
  constructor
  · intro lhs; rcases lhs with ⟨b, bDef, bIn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at bDef ; cases' bDef with bD1 bD2
    · subst bD1; simp; left; simp at *; exact bIn
    · subst bD2; simp; right; simp at *; exact bIn
  · intro rhs; rw [Finset.mem_union] at rhs ; cases rhs
    · use X \ {~(ϕ⋀ψ)} ∪ {~ϕ}; aesop
    · use X \ {~(ϕ⋀ψ)} ∪ {~ψ}; aesop

theorem endNodesOfLEQ {X Z ltX} : Z ∈ endNodesOf ⟨X, ltX⟩ → lengthOf Z ≤ lengthOf X :=
  by
  induction ltX
  case byLocalRule Y B lr next IH =>
    intro Z_endOf_Y
    unfold endNodesOf at Z_endOf_Y
    simp at Z_endOf_Y
    rcases Z_endOf_Y with ⟨W, W_in_B, Z_endOf_W⟩
    apply le_of_lt
    ·
      calc
        lengthOf Z ≤ lengthOf W := IH W W_in_B Z_endOf_W
        _ < lengthOf Y := localRulesDecreaseLength lr W W_in_B
  case sim a b =>
    intro Z_endOf_Y
    unfold endNodesOf at Z_endOf_Y
    aesop

theorem endNodesOfLocalRuleLT {X Z B next lr} :
    Z ∈ endNodesOf ⟨X, @LocalTableau.byLocalRule _ B lr next⟩ → lengthOf Z < lengthOf X :=
  by
  intro ZisEndNode
  rw [endNodesOf] at ZisEndNode
  simp at ZisEndNode
  rcases ZisEndNode with ⟨a, a_in_WS, Z_endOf_a⟩
  change Z ∈ endNodesOf ⟨a, next a a_in_WS⟩ at Z_endOf_a
  · calc
      lengthOf Z ≤ lengthOf a := endNodesOfLEQ Z_endOf_a
      _ < lengthOfSet X := localRulesDecreaseLength lr a a_in_WS

-- Definition 16, page 29
inductive ClosedTableau : Finset Formula → Type
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, ClosedTableau Y) → ClosedTableau X
  | atm {X ϕ} : ~(□ϕ) ∈ X → Simple X → ClosedTableau (projection X ∪ {~ϕ}) → ClosedTableau X

inductive Provable : Formula → Prop
  | byTableau {φ : Formula} : ClosedTableau {~φ} → Provable φ

-- Definition 17, page 30
def Inconsistent : Finset Formula → Prop
  | X => Nonempty (ClosedTableau X)

def Consistent : Finset Formula → Prop
  | X => ¬Inconsistent X


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
