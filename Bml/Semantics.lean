-- SEMANTICS
import Mathlib.Data.Finset.Basic

import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

import Bml.Syntax

-- Definition 2, page 6
structure KripkeModel (W : Type) : Type where
  val : W → Char → Prop
  Rel : W → W → Prop

-- Definition 3, page 6
@[simp]
def Evaluate {W : Type} : KripkeModel W × W → Formula → Prop
  | (_, _), ⊥ => False
  | (M, w), ·p => M.val w p
  | (M, w), ~φ => ¬Evaluate (M, w) φ
  | (M, w), φ⋀ψ => Evaluate (M, w) φ ∧ Evaluate (M, w) ψ
  | (M, w), □φ => ∀ v : W, M.Rel w v → Evaluate (M, v) φ

@[simp]
theorem evalDis {W M f g} {w : W} : Evaluate (M, w) (f⋁g) ↔ Evaluate (M, w) f ∨ Evaluate (M, w) g :=
  by
  simp
  tauto

def Tautology (φ : Formula) :=
  ∀ (W) (M : KripkeModel W) (w), Evaluate (M, w) φ

def Contradiction (φ : Formula) :=
  ∀ (W) (M : KripkeModel W) (w), ¬Evaluate (M, w) φ

-- Definition 5, page 9
class HasSat (α : Type) where
  Satisfiable : α → Prop

open HasSat
@[simp]
instance formHasSat : HasSat Formula :=
  HasSat.mk fun ϕ => ∃ (W : _) (M : KripkeModel W) (w : _), Evaluate (M, w) ϕ
@[simp]
instance setHasSat : HasSat (Finset Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, Evaluate (M, w) φ

theorem notsatisfnotThenTaut : ∀ φ, ¬Satisfiable (~φ) → Tautology φ :=
  by
  intro phi
  unfold Satisfiable
  unfold Tautology
  simp

@[simp]
theorem singletonSat_iff_sat : ∀ φ, Satisfiable ({φ} : Finset Formula) ↔ Satisfiable φ :=
  by
  intro phi
  simp

theorem tautImp_iff_comboNotUnsat {ϕ ψ} :
    Tautology (ϕ↣ψ) ↔ ¬Satisfiable ({ϕ, ~ψ} : Finset Formula) :=
  by
  unfold Tautology
  simp

def SemImpliesSets (X : Finset Formula) (Y : Finset Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w), (∀ φ ∈ X, Evaluate (M, w) φ) → ∀ ψ ∈ Y, Evaluate (M, w) ψ

def semEquiv (φ : Formula) (ψ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w), Evaluate (M, w) φ ↔ Evaluate (M, w) ψ

theorem semEquiv.transitive : Transitive semEquiv :=
  by
  unfold Transitive
  unfold semEquiv
  intro f g h f_is_g g_is_h W M w
  specialize f_is_g W M w
  specialize g_is_h W M w
  tauto

-- Definition 5, page 9
class VDash (α β : Type) where
  SemImplies : α → β → Prop

open VDash

@[simp]
instance modelCanSemImplyForm {W : Type} : VDash (KripkeModel W × W) Formula := ⟨@Evaluate W⟩
@[simp]
instance modelCanSemImplySet {W : Type} : VDash (KripkeModel W × W) (Finset Formula) := ⟨fun Mw X => ∀ f ∈ X, @Evaluate W Mw f⟩
instance setCanSemImplySet : VDash (Finset Formula) (Finset Formula):= ⟨SemImpliesSets⟩
instance setCanSemImplyForm : VDash (Finset Formula) Formula := ⟨fun X ψ => SemImpliesSets X {ψ}⟩
instance formCanSemImplySet : VDash Formula (Finset Formula) := ⟨fun φ X => SemImpliesSets {φ} X⟩
instance formCanSemImplyForm : VDash (Formula) (Formula):= ⟨fun φ ψ => SemImpliesSets {φ} {ψ}⟩

infixl:40 "⊨" => SemImplies

infixl:40 "≡" => semEquiv

infixl:40 "⊭" => fun a b => ¬a⊨b

theorem forms_to_sets {φ ψ : Formula} : φ⊨ψ → ({φ} : Finset Formula)⊨({ψ} : Finset Formula) :=
  by
  intro impTaut
  intro W M w lhs ψ1 psi1_in_setpsi
  specialize impTaut W M w
  simp at *
  subst psi1_in_setpsi
  apply impTaut
  exact lhs
