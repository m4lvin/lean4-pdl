import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation
import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints

import Pdl.Syntax
import Pdl.Measures

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
  @[simp]
  def relate {W : Type} : KripkeModel W → Program → W → W → Prop
    | M, ·c, w, v => M.Rel c w v
    | M, α;'β, w, v => ∃ y, relate M α w y ∧ relate M β y v
    | M, α⋓β, w, v => relate M α w v ∨ relate M β w v
    | M, ∗α, w, v => Relation.ReflTransGen (relate M α) w v
    | M, ?'φ, w, v => w = v ∧ evaluate M w φ
end

@[simp]
theorem evalDis {W M f g} {w : W} : evaluate M w (f⋁g) ↔ evaluate M w f ∨ evaluate M w g :=
  by
  simp
  tauto

@[simp]
def evaluatePoint {W : Type} : KripkeModel W × W → Formula → Prop
  | (M, w), ϕ => evaluate M w ϕ

def tautology (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, evaluate M w φ

def contradiction (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, ¬evaluate M w φ

-- MB: Definition 5, page 9
class HasSat (α : Type) where
  Satisfiable : α → Prop
open HasSat
@[simp]
instance formHasSat : HasSat Formula :=
  HasSat.mk fun ϕ => ∃ (W : _) (M : KripkeModel W) (w : _), evaluate M w ϕ
@[simp]
instance setHasSat : HasSat (Finset Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ
@[simp]
instance listHasSat : HasSat (List Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ

def semImpliesSets (X : Finset Formula) (Y : Finset Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ

def semImpliesLists (X : List Formula) (Y : List Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ

def semEquiv (φ : Formula) (ψ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w), evaluate M w φ ↔ evaluate M w ψ

theorem subsetSat {M : KripkeModel W} {w : W} {X Y : List Formula} : (∀ φ ∈ X, evaluate M w φ) → Y ⊆ X → ∀ φ ∈ Y, evaluate M w φ :=
  by aesop

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
instance modelCanSemImplySet {W : Type} : vDash (KripkeModel W × W) (List Formula) := vDash.mk (λ ⟨M,w⟩ fs => ∀ f ∈ fs, @evaluate W M w f)
@[simp]
instance modelCanSemImplyList {W : Type} : vDash (KripkeModel W × W) (List Formula) := vDash.mk (λ ⟨M,w⟩ fs => ∀ f ∈ fs, @evaluate W M w f)
instance setCanSemImplySet : vDash (List Formula) (List Formula) := vDash.mk semImpliesLists
instance setCanSemImplyForm : vDash (List Formula) Formula:= vDash.mk fun X ψ => semImpliesLists X [ψ]
instance formCanSemImplySet : vDash Formula (List Formula) := vDash.mk fun φ X => semImpliesLists [φ] X
instance formCanSemImplyForm : vDash Formula Formula := vDash.mk fun φ ψ => semImpliesLists [φ] [ψ]

infixl:40 "⊨" => SemImplies

infixl:40 "≡" => semEquiv

infixl:40 "⊭" => fun a b => ¬a⊨b

@[simp]
theorem singletonSat_iff_sat {M : KripkeModel W} {w : W} : ∀ φ, (M, w) ⊨ ([φ] : List Formula) ↔ evaluate M w φ :=
  by
  intro phi
  simp [modelCanSemImplyList]

-- useful lemmas to connect different ⊨ cases
theorem forms_to_lists {φ ψ : Formula} : φ⊨ψ → ([φ] : List Formula)⊨([ψ] : List Formula) :=
  by
  intro impTaut
  intro W M w lhs ψ psi_in_psi
  specialize impTaut W M w
  simp at psi_in_psi lhs
  rw [psi_in_psi]
  -- needed even though no ψ_1 in goal here?!
  apply impTaut
  rw [←singletonSat_iff_sat φ] at lhs
  · tauto
  · aesop


theorem notSat_iff_semImplies (X : List Formula) (χ : Formula):
    ¬Satisfiable (X ∪ [~χ]) ↔ X ⊨ ([χ] : List Formula) := by
  simp only [Satisfiable, not_exists, not_forall, exists_prop, setCanSemImplySet, semImpliesSets, forall_eq]
  constructor
  · intro nSat W M w satX
    specialize nSat W M w
    rcases nSat with ⟨φ, phi_in, not_phi⟩
    aesop
  · intro X_chi W M w
    specialize X_chi W M w
    -- cases em (evaluate M w χ)
    sorry

theorem equivSat {M : KripkeModel W} {w : W} (φ ψ : Formula): φ ≡ ψ → (M, w) ⊨ φ → (M, w) ⊨ ψ :=
  by
    intro φ_eq_ψ evalφ
    have : evaluate M w φ := by tauto
    rw [φ_eq_ψ] at this
    tauto

theorem relate_steps : ∀ x z, relate M (Program.steps (as ++ bs)) x z  ↔
  ∃ y, relate M (Program.steps as) x y ∧ relate M (Program.steps bs) y z :=
  by
  induction as
  · simp
  case cons a as IH =>
    intro x z
    constructor
    · intro lhs
      simp at *
      rcases lhs with ⟨y, x_a_y, y_asbs_z⟩
      rw [IH] at y_asbs_z
      rcases y_asbs_z with ⟨y', y_as_ys', ys'_bs_z⟩
      use y'
      constructor
      · use y
      · exact ys'_bs_z
    · intro rhs
      simp at *
      rcases rhs with ⟨y, ⟨y', x_a_y', y'_as_y⟩, bla⟩
      use y'
      rw [IH y' z]
      tauto

-- TODO: remove this, special instance of previous?
theorem rel_steps_last {as} : ∀ v w,
  relate M (Program.steps (as ++ [a])) v w ↔
    ∃ mid, relate M (Program.steps as) v mid ∧ relate M a mid w :=
  by
  induction as
  case nil =>
    simp at *
  case cons a2 as IH =>
    intro s t
    simp at *
    constructor
    · intro lhs
      rcases lhs with ⟨next, s_a2_next, next_asa_t⟩
      rw [IH] at next_asa_t
      tauto
    · intro rhs
      rcases rhs with ⟨m,⟨y,yP,yP2⟩,mP⟩
      use y
      rw [IH]
      tauto

theorem truthImply_then_satImply (X Y : List Formula) : X ⊨ Y → Satisfiable X → Satisfiable Y :=
  by
  intro X_Y
  intro satX
  rcases satX with ⟨W,M,w,v_X⟩
  specialize X_Y W M w v_X
  use W, M, w
