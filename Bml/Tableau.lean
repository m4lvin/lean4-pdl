-- TABLEAU
import Data.Finset.Basic
import Data.Finset.Pimage
import Algebra.BigOperators.Order
import Mathbin.Tactic.Default
import Order.WellFoundedSet
import Syntax
import Semantics
import Setsimp

#align_import tableau

open Formula

open HasLength

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def Closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X
#align closed Closed

-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
def SimpleForm : Formula → Prop
  | ⊥ => True
  | ~⊥ => True
  |-- added!
    ·_ =>
    True
  | ~·_ => True
  | □_ => True
  | ~(□_) => True
  | _ => False
#align simpleForm SimpleForm

instance (ϕ) : Decidable (SimpleForm ϕ) := by
  cases ϕ
  case bottom => apply Decidable.isTrue; tauto
  case atom_prop => apply Decidable.isTrue; tauto
  case neg =>
    cases ϕ
    case bottom => apply Decidable.isTrue; tauto
    case atom_prop => apply Decidable.isTrue; tauto
    case neg => apply Decidable.isFalse; tauto
    case and => apply Decidable.isFalse; tauto
    case box => apply Decidable.isTrue; tauto
  case and => apply Decidable.isFalse; tauto
  case box => apply Decidable.isTrue; tauto

def Simple : Finset Formula → Prop
  | X => ∀ P ∈ X, SimpleForm P
deriving Decidable
#align simple Simple

-- Let X_A := { R | [A]R ∈ X }.
@[simp]
def formProjection : Formula → Option Formula
  | □f => some f
  | _ => none
#align formProjection formProjection

def projection : Finset Formula → Finset Formula
  | X => X.biUnion fun x => (formProjection x).toFinset
#align projection projection

theorem proj {g : Formula} {X : Finset Formula} : g ∈ projection X ↔ □g ∈ X :=
  by
  unfold projection
  simp
  constructor
  · intro lhs
    rcases lhs with ⟨boxg, boxg_in_X, projboxg_is_g⟩
    cases boxg
    repeat' finish
  · intro rhs
    use□g
    constructor
    exact rhs
    simp
#align proj proj

theorem projSet {X : Finset Formula} : ↑(projection X) = {ϕ | □ϕ ∈ X} :=
  by
  ext1
  unfold_coes
  simp
  exact proj
#align projSet projSet

theorem projection_length_leq : ∀ f, (projection {f}).Sum lengthOfFormula ≤ lengthOfFormula f :=
  by
  intro f
  cases f
  · omega
  · exact by decide
  · exact by decide
  · exact by decide
  · have subsubClaim : projection {□f} = {f} := by ext1; rw [proj]; simp
    rw [subsubClaim]
    unfold lengthOfFormula; simp
#align projection_length_leq projection_length_leq

theorem projection_set_length_leq : ∀ X, lengthOfSet (projection X) ≤ lengthOfSet X :=
  by
  intro X
  apply Finset.induction_on X
  · unfold lengthOfSet; simp; intro f f_in_empty; cases f_in_empty
  · intro f S f_not_in_S IH
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
        (projection (insert f S)).Sum lengthOfFormula =
            (projection (insert f S)).Sum lengthOfFormula :=
          refl _
        _ = (projection {f} ∪ projection S).Sum lengthOfFormula := by rw [insert_comm_proj S f]
        _ ≤ (projection {f}).Sum lengthOfFormula + (projection S).Sum lengthOfFormula := by
          apply sum_union_le
        _ ≤ lengthOfFormula f + (projection S).Sum lengthOfFormula := by
          simp only [add_le_add_iff_right, projection_length_leq]
        _ ≤ lengthOfFormula f + S.sum lengthOfFormula := by simp; apply IH
#align projection_set_length_leq projection_set_length_leq

-- local rules: given this set, we get these sets as child nodes
inductive LocalRule : Finset Formula → Finset (Finset Formula) → Type-- closing rules:

  | bot {X} (h : ⊥ ∈ X) : LocalRule X ∅
  | Not {X ϕ} (h : ϕ ∈ X ∧ ~ϕ ∈ X) : LocalRule X ∅-- one-child rules:

  | neg {X ϕ} (h : ~~ϕ ∈ X) : LocalRule X {X \ {~~ϕ} ∪ {ϕ}}
  | Con {X ϕ ψ} (h : ϕ⋏ψ ∈ X) : LocalRule X {X \ {ϕ⋏ψ} ∪ {ϕ, ψ}}-- splitting rule:

  | nCo {X ϕ ψ} (h : ~(ϕ⋏ψ) ∈ X) : LocalRule X {X \ {~(ϕ⋏ψ)} ∪ {~ϕ}, X \ {~(ϕ⋏ψ)} ∪ {~ψ}}
#align localRule LocalRule

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
    case neg =>
      use{X \ {~~ψ} ∪ {ψ}}
      use LocalRule.neg ϕ_in_X
    case and ψ1 ψ2 =>
      unfold SimpleForm at *
      use{X \ {~(ψ1⋏ψ2)} ∪ {~ψ1}, X \ {~(ψ1⋏ψ2)} ∪ {~ψ2}}
      use LocalRule.nCo ϕ_in_X
    case box => unfold SimpleForm at *; tauto
  case and ψ1 ψ2 =>
    unfold SimpleForm at *
    use{X \ {ψ1⋏ψ2} ∪ {ψ1, ψ2}}
    use LocalRule.con ϕ_in_X
  case box => tauto
#align notSimpleThenLocalRule notSimpleThenLocalRule

theorem localRulesDecreaseLength {X : Finset Formula} {B : Finset (Finset Formula)}
    (r : LocalRule X B) : ∀ Y ∈ B, lengthOfSet Y < lengthOfSet X :=
  by
  cases r
  all_goals intro β inB; simp at *
  case bot => cases inB
  -- no premises
  case not => cases inB
  -- no premises
  case neg X ϕ notnot_in_X =>
    subst inB
    ·
      calc
        lengthOfSet (insert ϕ (X.erase (~~ϕ))) ≤ lengthOfSet (X.erase (~~ϕ)) + lengthOf ϕ := by
          apply lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~~ϕ)) + lengthOf ϕ + 2 := by simp
        _ = lengthOfSet (X.erase (~~ϕ)) + lengthOf (~~ϕ) := by unfold lengthOf;
          unfold lengthOfFormula; ring
        _ = lengthOfSet X := lengthRemove X (~~ϕ) notnot_in_X
  case con X ϕ ψ in_X =>
    subst inB
    ·
      calc
        lengthOf (insert ϕ (insert ψ (X.erase (ϕ⋏ψ)))) ≤
            lengthOf (insert ψ (X.erase (ϕ⋏ψ))) + lengthOf ϕ :=
          by apply lengthOf_insert_leq_plus
        _ ≤ lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ψ + lengthOf ϕ := by simp;
          apply lengthOf_insert_leq_plus
        _ = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ := by ring
        _ < lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ + 1 := by unfold lengthOf; simp
        _ = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf (ϕ⋏ψ) := by unfold lengthOf; unfold lengthOfFormula;
          ring
        _ = lengthOfSet X := lengthRemove X (ϕ⋏ψ) in_X
  case nCo X ϕ ψ in_X =>
    cases inB
    -- splitting rule!
    all_goals subst inB
    ·-- f
      calc
        lengthOfSet (insert (~ϕ) (X.erase (~(ϕ⋏ψ)))) ≤
            lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ϕ) :=
          lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ := by unfold lengthOf;
          unfold lengthOfFormula; ring_nf; simp
        _ = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) := by unfold lengthOf;
          unfold lengthOfFormula; ring
        _ = lengthOfSet X := lengthRemove X (~(ϕ⋏ψ)) in_X
    ·-- g
      calc
        lengthOfSet (insert (~ψ) (X.erase (~(ϕ⋏ψ)))) ≤
            lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ψ) :=
          lengthOf_insert_leq_plus
        _ < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ := by unfold lengthOf;
          unfold lengthOfFormula; ring_nf; simp
        _ = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) := by unfold lengthOf;
          unfold lengthOfFormula; ring
        _ = lengthOfSet X := lengthRemove X (~(ϕ⋏ψ)) in_X
#align localRulesDecreaseLength localRulesDecreaseLength

theorem atmRuleDecreasesLength {X : Finset Formula} {ϕ} :
    ~(□ϕ) ∈ X → lengthOfSet (projection X ∪ {~ϕ}) < lengthOfSet X :=
  by
  intro notBoxPhi_in_X
  simp
  have proj_form_lt : ∀ f g, some g = formProjection f → lengthOfFormula g < lengthOfFormula f := by
    intro f g g_is_fP_f; cases f; all_goals finish
  have lengthSingleton : ∀ f, lengthOfFormula f = lengthOfSet {f} := by intro f; unfold lengthOfSet;
    simp
  have otherClaim : projection X = projection (X.erase (~(□ϕ))) :=
    by
    ext1 phi
    rw [proj]; rw [proj]
    simp
  ·
    calc
      lengthOfSet (insert (~ϕ) (projection X)) ≤ lengthOfSet (projection X) + lengthOf (~ϕ) :=
        lengthOf_insert_leq_plus
      _ = lengthOfSet (projection X) + 1 + lengthOf ϕ := by unfold lengthOf; unfold lengthOfFormula;
        ring
      _ < lengthOfSet (projection X) + 1 + 1 + lengthOf ϕ := by simp
      _ = lengthOfSet (projection X) + lengthOf (~(□ϕ)) := by unfold lengthOf;
        unfold lengthOfFormula; ring
      _ = lengthOfSet (projection (X.erase (~(□ϕ)))) + lengthOf (~(□ϕ)) := by rw [otherClaim]
      _ ≤ lengthOfSet (X.erase (~(□ϕ))) + lengthOf (~(□ϕ)) := by simp;
        apply projection_set_length_leq
      _ = lengthOfSet X := lengthRemove X (~(□ϕ)) notBoxPhi_in_X
#align atmRuleDecreasesLength atmRuleDecreasesLength

-- Definition 8, page 14
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau for X, must be maximal
inductive LocalTableau : Finset Formula → Type
  | byLocalRule {X B} (_ : LocalRule X B) (next : ∀ Y ∈ B, LocalTableau Y) : LocalTableau X
  | sim {X} : Simple X → LocalTableau X
#align localTableau LocalTableau

open LocalTableau

-- needed for endNodesOf
instance localTableauHasSizeof : SizeOf (Σ X, LocalTableau X) :=
  ⟨fun ⟨X, T⟩ => lengthOfSet X⟩
#align localTableau_has_sizeof localTableauHasSizeof

-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, LocalTableau X) → Finset (Finset Formula)
  | ⟨X, @byLocalRule _ B lr next⟩ =>
    B.attach.biUnion fun ⟨Y, h⟩ =>
      have : lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h
      endNodesOf ⟨Y, next Y h⟩
  | ⟨X, sim _⟩ => {X}
#align endNodesOf endNodesOf

@[simp]
theorem botNoEndNodes {X h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.bot X h) n⟩ = ∅ := by unfold endNodesOf;
  simp
#align botNoEndNodes botNoEndNodes

@[simp]
theorem notNoEndNodes {X h ϕ n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.not X h ϕ) n⟩ = ∅ := by unfold endNodesOf;
  simp
#align notNoEndNodes notNoEndNodes

theorem negEndNodes {X ϕ h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.neg X ϕ h) n⟩ =
      endNodesOf ⟨X \ {~~ϕ} ∪ {ϕ}, n (X \ {~~ϕ} ∪ {ϕ}) (by simp)⟩ :=
  by
  ext1
  simp only [endNodesOf, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_attach,
    exists_true_left, Subtype.exists]
  constructor
  · intro lhs; rcases lhs with ⟨b, bDef, bIn⟩; subst bDef; exact bIn
  · intro rhs; use X \ {~~ϕ} ∪ {ϕ}; constructor; exact rhs; rfl
#align negEndNodes negEndNodes

theorem conEndNodes {X ϕ ψ h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.con X ϕ ψ h) n⟩ =
      endNodesOf ⟨X \ {ϕ⋏ψ} ∪ {ϕ, ψ}, n (X \ {ϕ⋏ψ} ∪ {ϕ, ψ}) (by simp)⟩ :=
  by
  ext1
  simp only [endNodesOf, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_attach,
    exists_true_left, Subtype.exists]
  constructor
  · intro lhs; rcases lhs with ⟨b, bDef, bIn⟩; subst bDef; exact bIn
  · intro rhs; use X \ {ϕ⋏ψ} ∪ {ϕ, ψ}; constructor; exact rhs; rfl
#align conEndNodes conEndNodes

theorem nCoEndNodes {X ϕ ψ h n} :
    endNodesOf ⟨X, LocalTableau.byLocalRule (@LocalRule.nCo X ϕ ψ h) n⟩ =
      endNodesOf ⟨X \ {~(ϕ⋏ψ)} ∪ {~ϕ}, n (X \ {~(ϕ⋏ψ)} ∪ {~ϕ}) (by simp)⟩ ∪
        endNodesOf ⟨X \ {~(ϕ⋏ψ)} ∪ {~ψ}, n (X \ {~(ϕ⋏ψ)} ∪ {~ψ}) (by simp)⟩ :=
  by
  ext1
  simp only [endNodesOf, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_attach,
    exists_true_left, Subtype.exists]
  constructor
  · intro lhs; rcases lhs with ⟨b, bDef, bIn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at bDef ; cases' bDef with bD1 bD2
    · subst bD1; simp; left; exact bIn
    · subst bD2; simp; right; exact bIn
  · intro rhs; rw [Finset.mem_union] at rhs ; cases rhs
    · use X \ {~(ϕ⋏ψ)} ∪ {~ϕ}; constructor; exact rhs; simp
    · use X \ {~(ϕ⋏ψ)} ∪ {~ψ}; constructor; exact rhs; simp
#align nCoEndNodes nCoEndNodes

-- Definition 16, page 29
inductive ClosedTableau : Finset Formula → Type
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, ClosedTableau Y) → ClosedTableau X
  | atm {X ϕ} : ~(□ϕ) ∈ X → Simple X → ClosedTableau (projection X ∪ {~ϕ}) → ClosedTableau X
#align closedTableau ClosedTableau

inductive Provable : Formula → Prop
  | byTableau {φ : Formula} : ClosedTableau {~φ} → Provable φ
#align provable Provable

-- Definition 17, page 30
def Inconsistent : Finset Formula → Prop
  | X => Nonempty (ClosedTableau X)
#align inconsistent Inconsistent

def Consistent : Finset Formula → Prop
  | X => ¬Inconsistent X
#align consistent Consistent

def existsLocalTableauFor : ∀ N α, N = lengthOf α → Nonempty (LocalTableau α) :=
  by
  intro N
  apply Nat.strong_induction_on N
  intro n IH α nDef
  have canApplyRule := em ¬∃ B, Nonempty (LocalRule α B)
  cases canApplyRule
  · constructor
    apply LocalTableau.sim
    by_contra hyp
    have := notSimpleThenLocalRule hyp
    tauto
  · simp at canApplyRule 
    cases' canApplyRule with B r_exists
    cases' r_exists with r
    cases r
    case bot _ h =>
      have t := LocalTableau.byLocalRule (LocalRule.bot h) _; use t
      intro Y; intro Y_in_empty; tauto
    case not _ _ h =>
      have t := LocalTableau.byLocalRule (LocalRule.not h) _; use t
      intro Y; intro Y_in_empty; tauto
    case neg _ f h =>
      have t := LocalTableau.byLocalRule (LocalRule.neg h) _; use t
      intro Y Y_def
      have rDec := localRulesDecreaseLength (LocalRule.neg h) Y Y_def
      subst nDef
      specialize IH (lengthOf Y) rDec Y (refl _)
      apply Classical.choice IH
    case con _ f g h =>
      have t := LocalTableau.byLocalRule (LocalRule.con h) _; use t
      intro Y Y_def
      have rDec := localRulesDecreaseLength (LocalRule.con h) Y Y_def
      subst nDef
      specialize IH (lengthOf Y) rDec Y (refl _)
      apply Classical.choice IH
    case nCo _ f g h =>
      have t := LocalTableau.byLocalRule (LocalRule.nCo h) _; use t
      intro Y Y_def
      have rDec := localRulesDecreaseLength (LocalRule.nCo h) Y Y_def
      subst nDef
      specialize IH (lengthOf Y) rDec Y (refl _)
      apply Classical.choice IH
#align existsLocalTableauFor existsLocalTableauFor

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
    finish
#align endNodesOfLEQ endNodesOfLEQ

theorem endNodesOfLocalRuleLT {X Z B next lr} :
    Z ∈ endNodesOf ⟨X, @LocalTableau.byLocalRule _ B lr next⟩ → lengthOf Z < lengthOf X :=
  by
  intro ZisEndNode
  rw [endNodesOf] at ZisEndNode 
  simp only [Finset.mem_biUnion, Finset.mem_attach, exists_true_left, Subtype.exists] at ZisEndNode 
  rcases ZisEndNode with ⟨a, a_in_WS, Z_endOf_a⟩
  change Z ∈ endNodesOf ⟨a, next a a_in_WS⟩ at Z_endOf_a 
  ·
    calc
      lengthOf Z ≤ lengthOf a := endNodesOfLEQ Z_endOf_a
      _ < lengthOfSet X := localRulesDecreaseLength lr a a_in_WS
#align endNodesOfLocalRuleLT endNodesOfLocalRuleLT

