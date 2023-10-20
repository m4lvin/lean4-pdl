import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation

import Pdl.Syntax

-- Kripke Models aka Labelled Transition Systems
structure KripkeModel (W : Type) : Type where
  val : W → Char → Prop
  Rel : Char → W → W → Prop

@[simp]
def complexityOfQuery {W : Type} :
    PSum (Σ' (_ : KripkeModel W) (_ : W), Formula)
         (Σ' (_ : KripkeModel W) (_ : Program) (_ : W), W) → ℕ
  | PSum.inl val => lengthOfFormula val.snd.snd
  | PSum.inr val => lengthOfProgram val.snd.fst

mutual
  @[simp]
  def evaluate {W : Type} : KripkeModel W → W → Formula → Prop
    | _, _, ⊥ => False
    | M, w, ·c => M.val w c
    | M, w, ~φ => Not (evaluate M w φ)
    | M, w, φ⋀ψ => evaluate M w φ ∧ evaluate M w ψ
    | M, w, ⌈α⌉ φ => ∀ v : W, relate M α w v → evaluate M v φ
    | M, w, †ϕ => evaluate M w ϕ
  @[simp]
  def relate {W : Type} : KripkeModel W → Program → W → W → Prop
    | M, ·c, w, v => M.Rel c w v
    | M, α;β, w, v => ∃ y, relate M α w y ∧ relate M β y v
    | M, α⋓β, w, v => relate M α w v ∨ relate M β w v
    | M, ∗α, w, v => Relation.ReflTransGen (relate M α) w v
    | M, ✓φ, w, v => w = v ∧ evaluate M w φ
end
termination_by
  evaluate _ _ f => sizeOf f
  relate _ p _ _ => sizeOf p

@[simp]
theorem evalDis {W M f g} {w : W} : evaluate M w (f⋁g) ↔ evaluate M w f ∨ evaluate M w g :=
  by
  simp
  tauto

@[simp]
def evaluatePoint {W : Type} : KripkeModel W × W → Formula → Prop
  | (M, w), ϕ => evaluate M w ϕ

def tautology (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w), evaluatePoint (M, w) φ

def contradiction (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w), ¬evaluatePoint (M, w) φ

def satisfiable (φ : Formula) :=
  ∃ (W : Type) (M : KripkeModel W) (w : _), evaluatePoint (M, w) φ

def semImpliesSets (X : Finset Formula) (Y : Finset Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluatePoint (M, w) φ) → ∀ ψ ∈ Y, evaluatePoint (M, w) ψ

def semEquiv (φ : Formula) (ψ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w), evaluate M w φ ↔ evaluate M w ψ

theorem semEquiv.transitive : Transitive semEquiv :=
  by
  unfold Transitive
  unfold semEquiv
  intro f g h f_is_g g_is_h W M w
  specialize f_is_g W M w
  specialize g_is_h W M w
  tauto

class vDash (α : Type) (β : Type) where
  SemImplies : α → β → Prop

open vDash

instance modelCanSemImplyForm {W : Type} : vDash (KripkeModel W × W) Formula := vDash.mk (@evaluatePoint W)
instance modelCanSemImplySet {W : Type} : vDash (KripkeModel W × W) (Finset Formula) := vDash.mk (λ ⟨M,w⟩ fs => ∀ f ∈ fs, @evaluate W M w f)
instance modelCanSemImplyList {W : Type} : vDash (KripkeModel W × W) (List Formula) := vDash.mk (λ ⟨M,w⟩ fs => ∀ f ∈ fs, @evaluate W M w f)
instance setCanSemImplySet : vDash (Finset Formula) (Finset Formula) := vDash.mk semImpliesSets
instance setCanSemImplyForm : vDash (Finset Formula) Formula:= vDash.mk fun X ψ => semImpliesSets X {ψ}
instance formCanSemImplySet : vDash Formula (Finset Formula) := vDash.mk fun φ X => semImpliesSets {φ} X
instance formCanSemImplyForm : vDash Formula Formula := vDash.mk fun φ ψ => semImpliesSets {φ} {ψ}

infixl:40 "⊨" => SemImplies

infixl:40 "≡" => semEquiv

infixl:40 "⊭" => fun a b => ¬a⊨b

-- useful lemmas to connect different ⊨ cases
theorem forms_to_sets {φ ψ : Formula} : φ⊨ψ → ({φ} : Finset Formula)⊨({ψ} : Finset Formula) :=
  by
  intro impTaut
  intro W M w lhs ψ psi_in_psi
  specialize impTaut W M w
  simp at psi_in_psi lhs impTaut
  rw [psi_in_psi]
  -- needed even though no ψ_1 in goal here?!
  apply impTaut
  exact lhs
