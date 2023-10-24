import Order.CompleteLattice
import Order.FixedPoints
import Data.Set.Lattice
import Syntax

#align_import semantics

-- Definition 2, page 6
-- Definition 2, page 6
structure KripkeModel (W : Type) : Type where
  val : W → Char → Prop
  Rel : W → W → Prop
#align kripkeModel KripkeModel

-- Definition 3, page 6
def Evaluate {W : Type} : KripkeModel W × W → Formula → Prop
  | (M, w), ⊥ => False
  | (M, w), ·p => M.val w p
  | (M, w), ~φ => ¬Evaluate (M, w) φ
  | (M, w), φ⋏ψ => Evaluate (M, w) φ ∧ Evaluate (M, w) ψ
  | (M, w), □φ => ∀ v : W, M.Rel w v → Evaluate (M, v) φ
#align evaluate Evaluate

def Tautology (φ : Formula) :=
  ∀ (W) (M : KripkeModel W) (w), Evaluate (M, w) φ
#align tautology Tautology

def Contradiction (φ : Formula) :=
  ∀ (W) (M : KripkeModel W) (w), ¬Evaluate (M, w) φ
#align contradiction Contradiction

-- Definition 4, page 8
-- Definition 5, page 9
class HasSat (α : Type) where
  Satisfiable : α → Prop
#align has_sat HasSat

open HasSat

instance formHasSat : HasSat Formula :=
  HasSat.mk fun ϕ => ∃ (W : _) (M : KripkeModel W) (w : _), Evaluate (M, w) ϕ
#align form_has_sat formHasSat

instance setHasSat : HasSat (Finset Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, Evaluate (M, w) φ
#align set_has_sat setHasSat

theorem notsatisfnotThenTaut : ∀ φ, ¬Satisfiable (~φ) → Tautology φ :=
  by
  intro phi
  unfold satisfiable
  unfold Tautology
  simp
  intro lhs
  intro W M w
  specialize lhs W M w
  unfold Evaluate at *
  simp at lhs 
  exact lhs
#align notsatisfnotThenTaut notsatisfnotThenTaut

@[simp]
theorem singletonSat_iff_sat : ∀ φ, Satisfiable ({φ} : Finset Formula) ↔ Satisfiable φ :=
  by
  intro phi
  unfold satisfiable
  simp
#align singletonSat_iff_sat singletonSat_iff_sat

theorem tautImp_iff_comboNotUnsat {ϕ ψ} :
    Tautology (ϕ↣ψ) ↔ ¬Satisfiable ({ϕ, ~ψ} : Finset Formula) :=
  by
  unfold Tautology
  unfold satisfiable
  simp
  constructor <;>
    · intro hyp
      intro W M w
      specialize hyp W M w
      intro sat_phi
      unfold Evaluate at *; simp at *; tauto
#align tautImp_iff_comboNotUnsat tautImp_iff_comboNotUnsat

def SemImpliesSets (X : Finset Formula) (Y : Finset Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w), (∀ φ ∈ X, Evaluate (M, w) φ) → ∀ ψ ∈ Y, Evaluate (M, w) ψ
#align semImplies_sets SemImpliesSets

-- Definition 5, page 9
class VDash {α : Type} {β : Type} where
  SemImplies : α → β → Prop
#align vDash VDash

open VDash

@[simp]
instance modelCanSemImplyForm {W : Type} : VDash :=
  VDash.mk (@Evaluate W)
#align model_canSemImply_form modelCanSemImplyForm

@[simp]
instance modelCanSemImplySet {W : Type} : VDash :=
  @VDash.mk (KripkeModel W × W) (Finset Formula) fun Mw X => ∀ f ∈ X, @Evaluate W Mw f
#align model_canSemImply_set modelCanSemImplySet

instance setCanSemImplySet : VDash :=
  VDash.mk SemImpliesSets
#align set_canSemImply_set setCanSemImplySet

instance setCanSemImplyForm : VDash :=
  VDash.mk fun X ψ => SemImpliesSets X {ψ}
#align set_canSemImply_form setCanSemImplyForm

instance formCanSemImplySet : VDash :=
  VDash.mk fun φ X => SemImpliesSets {φ} X
#align form_canSemImply_set formCanSemImplySet

instance formCanSemImplyForm : VDash :=
  VDash.mk fun φ ψ => SemImpliesSets {φ} {ψ}
#align form_canSemImply_form formCanSemImplyForm

infixl:40 "⊨" => SemImplies

infixl:40 "⊭" => fun a b => ¬a⊨b

-- useful lemmas to connect all the different ⊨ cases
theorem forms_to_sets {φ ψ : Formula} : φ⊨ψ → ({φ} : Finset Formula)⊨({ψ} : Finset Formula) :=
  by
  intro impTaut
  intro W M w lhs ψ1 psi1_in_setpsi
  specialize impTaut W M w
  simp at *
  subst psi1_in_setpsi
  apply impTaut
  exact lhs
#align forms_to_sets forms_to_sets

