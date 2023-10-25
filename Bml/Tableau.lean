-- TABLEAU

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.PImage
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Order.WellFoundedSet

import Bml.Syntax
import Bml.Semantics
import Bml.Setsimp

open Formula

open HasLength

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def Closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X

-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
def SimpleForm : Formula → Bool
  | ⊥ => True
  | ~⊥ => True
  |-- added!
    ·_ =>
    True
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
  · sorry -- omega
  · sorry -- exact by decide
  · sorry -- exact by decide
  · sorry -- exact by decide
  case box f =>
    have subsubClaim : projection {□f} = {f} := by ext1; rw [proj]; simp
    rw [subsubClaim]
    simp

theorem projection_set_length_leq : ∀ X, lengthOfSet (projection X) ≤ lengthOfSet X :=
  by
  intro X
  induction X using Finset.induction_on
  · simp
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
    ·
      calc
        (projection (insert f S)).sum lengthOfFormula =
            (projection (insert f S)).sum lengthOfFormula :=
          refl _
        _ = (projection {f} ∪ projection S).sum lengthOfFormula := by rw [insert_comm_proj S f]
        _ ≤ (projection {f}).sum lengthOfFormula + (projection S).sum lengthOfFormula := by
          apply sum_union_le
        _ ≤ lengthOfFormula f + (projection S).sum lengthOfFormula := by
          simp only [add_le_add_iff_right, projection_length_leq]
        _ ≤ lengthOfFormula f + S.sum lengthOfFormula := by simp; apply IH

-- local rules: given this set, we get these sets as child nodes
inductive LocalRule : Finset Formula → Finset (Finset Formula) → Type-- closing rules:

  | bot {X} (h : ⊥ ∈ X) : LocalRule X ∅
  | Not {X ϕ} (h : ϕ ∈ X ∧ ~ϕ ∈ X) : LocalRule X ∅-- one-child rules:

  | neg {X ϕ} (h : ~~ϕ ∈ X) : LocalRule X {X \ {~~ϕ} ∪ {ϕ}}
  | Con {X ϕ ψ} (h : ϕ⋀ψ ∈ X) : LocalRule X {X \ {ϕ⋀ψ} ∪ {ϕ, ψ}}-- splitting rule:

  | nCo {X ϕ ψ} (h : ~(ϕ⋀ψ) ∈ X) : LocalRule X {X \ {~(ϕ⋀ψ)} ∪ {~ϕ}, X \ {~(ϕ⋀ψ)} ∪ {~ψ}}

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
      unfold SimpleForm at *
      use{X \ {~(ψ1⋀ψ2)} ∪ {~ψ1}, X \ {~(ψ1⋀ψ2)} ∪ {~ψ2}}
      use LocalRule.nCo ϕ_in_X
    case box => unfold SimpleForm at *; tauto
  case And ψ1 ψ2 =>
    unfold SimpleForm at *
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
    ·
      calc
        lengthOfSet (insert ϕ (X.erase (~~ϕ))) ≤ lengthOfSet (X.erase (~~ϕ)) + lengthOf ϕ := by
          apply lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~~ϕ)) + lengthOf ϕ + 2 := by simp
        _ = lengthOfSet (X.erase (~~ϕ)) + lengthOf (~~ϕ) := by sorry
        _ = lengthOfSet X := lengthRemove X (~~ϕ) notnot_in_X
  case Con ϕ ψ in_X =>
    subst inB
    ·
      calc
        lengthOf (insert ϕ (insert ψ (X.erase (ϕ⋀ψ)))) ≤
            lengthOf (insert ψ (X.erase (ϕ⋀ψ))) + lengthOf ϕ :=
          by apply lengthOf_insert_leq_plus
        _ ≤ lengthOf (X.erase (ϕ⋀ψ)) + lengthOf ψ + lengthOf ϕ := by simp; apply lengthOf_insert_leq_plus
        _ = lengthOf (X.erase (ϕ⋀ψ)) + lengthOf ϕ + lengthOf ψ := by sorry
        _ < lengthOf (X.erase (ϕ⋀ψ)) + lengthOf ϕ + lengthOf ψ + 1 := by unfold lengthOf; simp
        _ = lengthOf (X.erase (ϕ⋀ψ)) + lengthOf (ϕ⋀ψ) := by unfold lengthOf; sorry
        _ = lengthOfSet X := lengthRemove X (ϕ⋀ψ) in_X
  case nCo ϕ ψ in_X =>
    cases inB
    -- splitting rule!
    case inl inB => -- f
      subst inB
      calc
        lengthOfSet (insert (~ϕ) (X.erase (~(ϕ⋀ψ)))) ≤
            lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~ϕ) :=
          lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~(ϕ⋀ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ := by unfold lengthOf; sorry
        _ = lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~(ϕ⋀ψ)) := by unfold lengthOf; sorry
        _ = lengthOfSet X := lengthRemove X (~(ϕ⋀ψ)) in_X
    case inr inB => -- g
      subst inB
      calc
        lengthOfSet (insert (~ψ) (X.erase (~(ϕ⋀ψ)))) ≤
            lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~ψ) :=
          lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~(ϕ⋀ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ := by unfold lengthOf; sorry
        _ = lengthOfSet (X.erase (~(ϕ⋀ψ))) + lengthOf (~(ϕ⋀ψ)) := by unfold lengthOf; sorry
        _ = lengthOfSet X := lengthRemove X (~(ϕ⋀ψ)) in_X

theorem atmRuleDecreasesLength {X : Finset Formula} {ϕ} :
    ~(□ϕ) ∈ X → lengthOfSet (projection X ∪ {~ϕ}) < lengthOfSet X :=
  by
  intro notBoxPhi_in_X
  simp
  have proj_form_lt : ∀ f g, some g = formProjection f → lengthOfFormula g < lengthOfFormula f := by
    intro f g g_is_fP_f; cases f; all_goals aesop
  have lengthSingleton : ∀ f, lengthOfFormula f = lengthOfSet {f} := by intro f; unfold lengthOfSet; simp
  have otherClaim : projection X = projection (X.erase (~(□ϕ))) :=
    by
    ext1 phi
    rw [proj]; rw [proj]
    simp
  ·
    calc
      lengthOfSet (insert (~ϕ) (projection X)) ≤ lengthOfSet (projection X) + lengthOf (~ϕ) :=
        lengthOf_insert_leq_plus
      _ = lengthOfSet (projection X) + 1 + lengthOf ϕ := by unfold lengthOf; simp; unfold lengthOfFormula; sorry
      _ < lengthOfSet (projection X) + 1 + 1 + lengthOf ϕ := by simp
      _ = lengthOfSet (projection X) + lengthOf (~(□ϕ)) := by unfold lengthOf; simp; unfold lengthOfFormula; sorry
      _ = lengthOfSet (projection (X.erase (~(□ϕ)))) + lengthOf (~(□ϕ)) := by rw [otherClaim]
      _ ≤ lengthOfSet (X.erase (~(□ϕ))) + lengthOf (~(□ϕ)) := by simp; apply projection_set_length_leq
      _ = lengthOfSet X := lengthRemove X (~(□ϕ)) notBoxPhi_in_X

-- Definition 8, page 14
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau for X, must be maximal
inductive LocalTableau : Finset Formula → Type
  | byLocalRule {X B} (_ : LocalRule X B) (next : ∀ Y ∈ B, LocalTableau Y) : LocalTableau X
  | sim {X} : Simple X → LocalTableau X

open LocalTableau

-- needed for endNodesOf
instance localTableauHasSizeof : SizeOf (Σ X, LocalTableau X) :=
  ⟨fun ⟨X, T⟩ => lengthOfSet X⟩

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
    · use X \ {~(ϕ⋀ψ)} ∪ {~ϕ}; sorry
    · use X \ {~(ϕ⋀ψ)} ∪ {~ψ}; sorry

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

def existsLocalTableauFor : ∀ N α, N = lengthOf α → Nonempty (LocalTableau α) :=
  by
  intro N
  induction N using Nat.strong_induction_on
  case h n IH =>
  intro α nDef
  have canApplyRule := em ¬∃ B, Nonempty (LocalRule α B)
  cases canApplyRule
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
      have t := LocalTableau.byLocalRule (LocalRule.bot h) ?_; use t
      intro Y; intro Y_in_empty; tauto
    case Not h =>
      have t := LocalTableau.byLocalRule (LocalRule.Not h) ?_; use t
      intro Y; intro Y_in_empty; tauto
    case neg f h =>
      have t := LocalTableau.byLocalRule (LocalRule.neg h) ?_; use t
      intro Y Y_def
      have rDec := localRulesDecreaseLength (LocalRule.neg h) Y Y_def
      subst nDef
      specialize IH (lengthOf Y) rDec Y (refl _)
      apply Classical.choice IH
    case Con f g h =>
      have t := LocalTableau.byLocalRule (LocalRule.Con h) ?_; use t
      intro Y Y_def
      have rDec := localRulesDecreaseLength (LocalRule.Con h) Y Y_def
      subst nDef
      specialize IH (lengthOf Y) rDec Y (refl _)
      apply Classical.choice IH
    case nCo f g h =>
      have t := LocalTableau.byLocalRule (LocalRule.nCo h) ?_; use t
      intro Y Y_def
      have rDec := localRulesDecreaseLength (LocalRule.nCo h) Y Y_def
      subst nDef
      specialize IH (lengthOf Y) rDec Y (refl _)
      apply Classical.choice IH

theorem endNodesOfLEQ {X Z ltX} : Z ∈ endNodesOf ⟨X, ltX⟩ → lengthOf Z ≤ lengthOf X :=
  by
  induction ltX
  case byLocalRule Y B lr next IH =>
    intro Z_endOf_Y
    have foo := localRulesDecreaseLength lr Y
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
  simp only [Finset.mem_biUnion, Finset.mem_attach, exists_true_left, Subtype.exists] at ZisEndNode 
  rcases ZisEndNode with ⟨a, a_in_WS, Z_endOf_a⟩
  sorry
  /-
  change Z ∈ endNodesOf ⟨a, next a a_in_WS⟩ at Z_endOf_a
  ·
    calc
      lengthOf Z ≤ lengthOf a := endNodesOfLEQ Z_endOf_a
      _ < lengthOfSet X := localRulesDecreaseLength lr a a_in_WS
  -/
