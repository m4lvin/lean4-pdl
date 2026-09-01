import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Sort
-- note: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Can.27t.20.23eval.20a.20Finset.20Nat.3F/near/577761910

import Pdl.Discon

/-! # Sequents -/

/-! ## Optional loaded formulas (Olfs) -/

/-- In nodes we optionally have a negated loaded formula on the left or right. -/
abbrev Olf := Option (NegLoadFormula ⊕ NegLoadFormula)

@[simp]
def Olf.voc : Olf → Vocab
| none => {}
| some (Sum.inl nlf) => nlf.voc
| some (Sum.inr nlf) => nlf.voc

def Olf.L : Olf → Finset Formula
| none => {}
| some (Sum.inl ⟨lf⟩) => {~ lf.unload}
| some (Sum.inr _) =>{}

@[simp]
lemma Olf.L_none : Olf.L none = {} := by rfl
@[simp]
lemma Olf.L_inr : Olf.L (some (Sum.inr lf)) = {} := by rfl
@[simp]
lemma Olf.L_map_inr : Olf.L (Option.map Sum.inr olf) = {} := by cases olf <;> rfl
@[simp]
lemma Olf.L_inl : Olf.L (some (Sum.inl lf)) = {~lf.1.unload} := by simp only [L]

def Olf.R : Olf → Finset Formula
| none => {}
| some (Sum.inl _) => {}
| some (Sum.inr ⟨lf⟩) => {~ lf.unload}

@[simp]
lemma Olf.R_none : Olf.R none = {} := by rfl
@[simp]
lemma Olf.R_inl : Olf.R (some (Sum.inl lf)) = {} := by rfl
@[simp]
lemma Olf.R_map_inl : Olf.R (Option.map Sum.inl olf) = {} := by cases olf <;> rfl
@[simp]
lemma Olf.R_inr : Olf.R (some (Sum.inr lf)) = {~lf.1.unload} := by simp only [R]

-- mathlib this?
@[simp]
instance Option.instHasSubsetOption : HasSubset (Option α) := HasSubset.mk
  fun o1 o2 =>
  match o1, o2 with
  | none, _ => True
  | some _, none => False
  | some f, some g => f = g

-- mathlib this?
@[simp]
theorem Option.some_subseteq {O : Option α} : (some x ⊆ O) ↔ some x = O := by
  cases O
  all_goals simp

-- mathlib this?
/-- Instance that is used to say `(O : Olf) \ (O' : Olf)`. -/
instance Option.insHasSdiff [DecidableEq α] : SDiff (Option α) := SDiff.mk
  fun o1 del =>
  match o1, del with
  | none, _ => none
  | some f, none => some f
  | some f, some g => if f = g then none else some f

@[simp]
lemma Option.insHasSdiff_none [DecidableEq α] :
    (none : Option α) \ o = none := by
  unfold Option.insHasSdiff
  grind

@[simp]
lemma Option.insHasSdiff_remove_none_cancel [DecidableEq α] :
    o \ (none : Option α) = o := by
  unfold Option.insHasSdiff
  grind

@[simp]
lemma Option.insHasSdiff_remove_sem_eq_none [DecidableEq α] :
    (some x) \ (some x : Option α) = none := by
  unfold Option.insHasSdiff
  grind

@[simp]
def Option.overwrite : Option α → Option α → Option α
| old, none   => old
| _  , some x => some x

def Olf.change (oldO : Olf) (Ocond : Olf) (newO : Olf) : Olf := (oldO \ Ocond).overwrite newO

@[simp]
theorem Olf.change_old_none_none {oldO} : Olf.change oldO none none = oldO := by
  cases oldO <;> simp [Olf.change, Option.overwrite, Option.insHasSdiff]

@[simp]
theorem Olf.change_none_none_new {newO} : Olf.change none none newO = newO := by
  cases newO <;> simp [Olf.change, Option.overwrite, Option.insHasSdiff]

@[simp]
theorem Olf.change_some {oldO whatever wnlf} :
    Olf.change oldO whatever (some wnlf) = some wnlf := by
  cases oldO <;> simp [Olf.change, Option.overwrite]

@[simp]
theorem Olf.change_some_some_eq : Olf.change (some nχ) (some nχ) Onew = Onew := by
  cases Onew <;> simp [Olf.change, Option.overwrite]

@[simp]
def Olf.isNone : Olf → Prop
 | .none => True
 | .some (Sum.inl _) => False
 | .some (Sum.inr _) => False

@[simp]
def Olf.isLeft : Olf → Prop
 | .none => False
 | .some (Sum.inl _) => True
 | .some (Sum.inr _) => False

@[simp]
def Olf.isRight : Olf → Prop
 | .none => False
 | .some (Sum.inl _) => False
 | .some (Sum.inr _) => True

instance instDecidableOlfisNone (o : Olf) : Decidable o.isNone := by
  rcases o with _|(_|_)
  · apply isTrue; simp_all
  · apply isFalse; simp_all
  · apply isFalse; simp_all

instance instDecidableOlfisLeft (o : Olf) : Decidable o.isLeft := by
  rcases o with _|(_|_)
  · apply isFalse; simp_all
  · apply isTrue; simp_all
  · apply isFalse; simp_all

instance instDecidableOlfisRight (o : Olf) : Decidable o.isRight := by
  rcases o with _|(_|_)
  · apply isFalse; simp_all
  · apply isFalse; simp_all
  · apply isTrue; simp_all

/-! ## Sequents and their (multi)set quality -/

/-- A tableau node is labelled with two finite sets of formulas and an `Olf`.
Each formula is placed on the left or right and up to one formula may be loaded. -/
def Sequent := Finset Formula × Finset Formula × Olf -- ⟨L, R, o⟩
  deriving DecidableEq, Repr

def Sequent.toFinset : Sequent → Finset Formula
| (L,R,O) => (L ∪ R) ∪ (O.map (Sum.elim negUnload negUnload)).toFinset

/-! ## Components and sides of sequents -/

def Sequent.L : Sequent → Finset Formula | ⟨L,_,_⟩ => L
def Sequent.R : Sequent → Finset Formula | ⟨_,R,_⟩ => R
def Sequent.O : Sequent → Olf | ⟨_,_,O⟩ => O

@[simp]
lemma Sequent.L_eq {L R O} : Sequent.L ⟨L,R,O⟩ = L := by simp [Sequent.L]
@[simp]
lemma Sequent.R_eq {L R O} : Sequent.R ⟨L,R,O⟩ = R := by simp [Sequent.R]
@[simp]
lemma Sequent.O_eq {L R O} : Sequent.O ⟨L,R,O⟩ = O := by simp [Sequent.O]

def Sequent.left (X : Sequent) : Finset Formula := X.L ∪ X.O.L
def Sequent.right (X : Sequent) : Finset Formula := X.R ∪ X.O.R

@[simp]
lemma Sequent.left_eq {L R O} : Sequent.left ⟨L,R,O⟩ = L ∪ O.L := by simp [Sequent.left]
@[simp]
def Sequent.right_eq {L R O} : Sequent.right ⟨L,R,O⟩ = R ∪ O.R := by simp [Sequent.right]


/-! ## (Joint) vocabulary of sequents -/

/-- Like `Olf.voc` but without the ⊕ inside. -/
def onlfvoc : Option NegLoadFormula → Vocab
| none => ∅
| some nlf => nlf.voc

def lfovoc (L : List (List Formula × Option NegLoadFormula)) : Vocab :=
  L.toFinset.sup (fun ⟨fs,o⟩ => fs.fvoc ∪ (onlfvoc o))

/-- The joint vocabulary occurring on both the left and the right side. -/
@[simp]
def jvoc (X : Sequent) : Vocab := (X.left).fvoc ∩ (X.right).fvoc

lemma jvoc_sub_of_voc_sub {Y X : Sequent}
    (hl : Y.left.fvoc ⊆ X.left.fvoc)
    (hr : Y.right.fvoc ⊆ X.right.fvoc)
    : jvoc Y ⊆ jvoc X := by
  intro x x_in_jY
  simp only [jvoc, Finset.mem_inter] at x_in_jY
  specialize @hl x x_in_jY.1
  specialize @hr x x_in_jY.2
  simp only [jvoc, Finset.mem_inter]
  tauto

/-! ## Formulas as elements of sequents -/

@[simp]
instance instMembershipFormulaSequent : Membership Formula Sequent := ⟨fun X φ => φ ∈ X.L ∨ φ ∈ X.R⟩

instance instDecidableMemFormulaSequent {φ : Formula} {X : Sequent} : Decidable (φ ∈ X) := by
  rcases X with ⟨L,R,o⟩
  simp only [instMembershipFormulaSequent]
  infer_instance

instance instFintypeSubtypeMemSequent {X : Sequent} : Fintype (Subtype (fun x => x ∈ X)) := by
  rcases X with ⟨L,R,o⟩
  simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R]
  apply Fintype.subtype (L ∪ R)
  aesop

@[simp]
def NegLoadFormula.mem_Sequent (X : Sequent) (nlf : NegLoadFormula) : Prop :=
  X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

instance : Decidable (NegLoadFormula.mem_Sequent ⟨L,R,O⟩ nlf) := by
  refine
    if h : O = some (Sum.inl nlf) then isTrue ?_
    else if h2 : O = some (Sum.inr nlf) then isTrue ?_ else isFalse ?_
  all_goals simp; tauto

@[simp]
instance instMembershipNegLoadFormulaSequent :
    Membership NegLoadFormula Sequent := ⟨NegLoadFormula.mem_Sequent⟩

def AnyNegFormula.mem_Sequent : (X : Sequent) → (anf : AnyNegFormula) → Prop
| X, ⟨.normal φ⟩ => (~φ) ∈ X
| X, ⟨.loaded χ⟩ => instMembershipNegLoadFormulaSequent.mem X (~'χ)
  -- Note: writing `∈` does not work because the first argument of `Membership` is `outParam`.

@[simp]
instance : Membership AnyNegFormula Sequent := ⟨AnyNegFormula.mem_Sequent⟩

/-! ## Closed, basic, loaded and free sequents -/

/-- A sequent is *closed* iff it contains `⊥` or contains a formula and its negation. -/
def Sequent.closed (X : Sequent) : Prop :=
  ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X

/-- A sequent is *basic* iff it only contains basic formulas and is not closed. -/
def Sequent.basic : Sequent → Prop
  | X => (∀ f ∈ X.toFinset, f.basic) ∧ ¬ X.closed

/-- A variant of `Fintype.decidableExistsFintype`, used by `instDecidableClosed`. -/
instance Fintype.decidableExistsConjFintype {α : Type u_1} {p q : α → Prop}
    [DecidablePred q] [Fintype (Subtype p)]
    : Decidable (∃ (a : α), p a ∧ q a) := by
  by_cases ∃ x : Subtype p, q x -- This uses the Fintype instance.
  · apply isTrue; aesop
  · apply isFalse; aesop

instance Sequent.instDecidableClosed {X : Sequent} : Decidable (X.closed) := by
  unfold Sequent.closed
  by_cases ⊥ ∈ X
  · apply isTrue; tauto
  · by_cases ∃ f, f ∈ X ∧ (~f) ∈ X
    · apply isTrue; aesop
    · apply isFalse; aesop

instance instDecidableBasic {X : Sequent} : Decidable (X.basic) := by
  by_cases X.closed
  · apply isFalse
    rcases X with ⟨L,R,o⟩
    unfold Sequent.basic
    aesop
  case neg h =>
    unfold Sequent.basic
    simp only [h, not_false_eq_true, and_true]
    by_cases ∃ f ∈ X.toFinset, f.basic ≠ true
    · apply isFalse
      push_neg
      assumption
    · apply isTrue
      push_neg at *
      assumption

def Sequent.isLoaded : Sequent → Prop
| ⟨_, _, none  ⟩ => False
| ⟨_, _, some _⟩ => True

/-- A loaded sequent that is not loaded on the left is loaded on the right. -/
lemma Sequent.isRight_of_not_isLeft_isLoaded {X : Sequent} (h1 : ¬ X.2.2.isLeft) (h2 : X.isLoaded) :
    X.2.2.isRight := by
  rcases X with ⟨L, R, _|(o|o)⟩ <;> simp_all [Sequent.isLoaded]

instance instDecidableSequentisLoaded (X : Sequent) : Decidable (X.isLoaded) := by
  rcases X with ⟨_, _, _|_⟩
  · apply isFalse; simp_all [Sequent.isLoaded]
  · apply isTrue; simp_all [Sequent.isLoaded]

def Sequent.isFree (Γ : Sequent) : Prop := ¬ Γ.isLoaded

instance instDecidableSequentisFree (X : Sequent) : Decidable (X.isFree) := by
  rcases X with ⟨_, _, _|_⟩
  · apply isTrue; simp_all [Sequent.isFree, Sequent.isLoaded]
  · apply isFalse; simp_all [Sequent.isFree, Sequent.isLoaded]

@[simp]
theorem Sequent.none_isFree L R : Sequent.isFree (L, R, none) := by
  simp [Sequent.isFree, Sequent.isLoaded]

@[simp]
theorem Sequent.some_not_isFree L R olf : ¬ Sequent.isFree (L, R, some olf) := by
  simp [Sequent.isFree, Sequent.isLoaded]

/-! ## Semantics of sequents -/

instance modelCanSemImplySequent : vDash (KripkeModel W × W) Sequent :=
  vDash.mk (fun ⟨M,w⟩ X => ∀ f ∈ X.toFinset, evaluate M w f)

instance instSequentHasSat : HasSat Sequent :=
  HasSat.mk fun Δ => ∃ (W : Type) (M : KripkeModel W) (w : W), (M,w) ⊨ Δ

open HasSat

theorem tautImp_iff_SequentUnsat {φ ψ} {X : Sequent} :
    X = ({φ}, {~ψ}, none) → (tautology (φ ↣ ψ) ↔ ¬ satisfiable X) := by
  intro defX
  subst defX
  simp_all [Sequent.toFinset, tautology, satisfiable, modelCanSemImplySequent]

theorem vDash_setEqTo_iff {X Y : Sequent} (h : X = Y) (M : KripkeModel W) (w : W) :
    (M,w) ⊨ X ↔ (M,w) ⊨ Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [modelCanSemImplySequent]
  cases h
  simp_all

lemma Sequent.satisfiable_top_cons_right {X : Sequent} (h_left_nil : X.left = {})
    (X_unsat : ¬satisfiable X) : ¬satisfiable ({⊤} ∪ X.right) := by
  rintro ⟨W,M,w,w_⟩
  absurd X_unsat; clear X_unsat
  use W, M, w
  intro φ φ_in
  rcases X with ⟨L,R,O⟩
  simp only [left_eq, Finset.union_eq_empty] at h_left_nil
  rcases h_left_nil with ⟨L_nil, OL_nil⟩
  subst L_nil
  simp only [toFinset, Finset.empty_union, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
    Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr] at φ_in
  rcases φ_in with _|_|⟨⟨χ⟩, ⟨O_def, def_φ⟩⟩
  · aesop
  · aesop
  · subst O_def def_φ
    unfold right at w_
    simp only [Formula.insTop, R_eq, O_eq, Olf.R_inr] at w_
    grind

/-! ## Removing loaded formulas from sequents -/

def Sequent.without : (LRO : Sequent) → (naf : AnyNegFormula) → Sequent
| ⟨L,R,O⟩, ⟨.normal f⟩  => ⟨L \ {~f}, R \ {~f}, O⟩
| ⟨L,R,O⟩, ⟨.loaded lf⟩ => if ((~'lf).mem_Sequent ⟨L,R,O⟩) then ⟨L, R, none⟩ else ⟨L,R,O⟩

@[simp]
theorem Sequent.without_normal_isFree_iff_isFree (LRO : Sequent) :
    (LRO.without (~''(.normal φ))).isFree ↔ LRO.isFree := by
  rcases LRO with ⟨L, R, O⟩
  simp [Sequent.without, isFree, isLoaded]
  aesop

@[simp]
theorem Sequent.isFree_then_without_isFree (LRO : Sequent) :
    LRO.isFree → ∀ anf, (LRO.without anf).isFree := by
  intro LRO_isFree anf
  rcases LRO with ⟨L, R, _|_⟩
  · rcases anf with ⟨_|_⟩ <;> simp [without, isFree, isLoaded]
  · exfalso
    simp [isFree, isLoaded] at *

lemma Sequent.without_loadBoxes_isFree_of_eq_inl {L R δs} {χ : LoadFormula} {φ : Formula}
    (h : χ = AnyFormula.loadBoxes αs φ)
    : (Sequent.without (L, R, some (Sum.inl (~'⌊⌊d :: δs⌋⌋χ)))
      (~''(AnyFormula.loadBoxes (d :: (δs ++ αs)) (AnyFormula.normal φ)))).isFree := by
  unfold Sequent.without
  simp
  suffices (⌊⌊d :: δs⌋⌋χ) = ⌊d⌋AnyFormula.loadBoxes (δs ++ αs) (AnyFormula.normal φ) by simp_all
  rw [box_loadBoxes_append_eq_of_loaded_eq_loadBoxes]
  exact h

lemma Sequent.without_loadBoxes_isFree_of_eq_inr {L R δs} {χ : LoadFormula} {φ : Formula}
    (h : χ = AnyFormula.loadBoxes αs φ)
    : (Sequent.without (L, R, some (Sum.inr (~'⌊⌊d :: δs⌋⌋χ)))
      (~''(AnyFormula.loadBoxes (d :: (δs ++ αs)) (AnyFormula.normal φ)))).isFree := by
  unfold Sequent.without
  simp
  suffices (⌊⌊d :: δs⌋⌋χ) = ⌊d⌋AnyFormula.loadBoxes (δs ++ αs) (AnyFormula.normal φ) by simp_all
  rw [box_loadBoxes_append_eq_of_loaded_eq_loadBoxes]
  exact h

lemma Sequent.without_loadMulti_isFree_of_splitLast_cons_inl {L R δs} {φ : Formula}
    (h : splitLast (d :: δs) = some δ_β)
    : (Sequent.without (L, R, some (Sum.inl (~'loadMulti δ_β.1 δ_β.2 φ)))
      (~''(AnyFormula.loadBoxes (d :: δs) (AnyFormula.normal φ)))).isFree := by
  rw [@loadMulti_of_splitLast_cons _ _ _ _ φ h]
  simp [Sequent.without]

lemma Sequent.without_loadMulti_isFree_of_splitLast_cons_inr {L R δs} {φ : Formula}
    (h : splitLast (d :: δs) = some δ_β)
    : (Sequent.without (L, R, some (Sum.inr (~'loadMulti δ_β.1 δ_β.2 φ)))
      (~''(AnyFormula.loadBoxes (d :: δs) (AnyFormula.normal φ)))).isFree := by
  rw [@loadMulti_of_splitLast_cons _ _ _ _ φ h]
  simp [Sequent.without]

inductive Side
| LL : Side
| RR : Side

@[simp]
def sideOf : Sum α α → Side
| Sum.inl _ => .LL
| Sum.inr _ => .RR

def AnyNegFormula.in_side : (anf : AnyNegFormula) → Side → (X : Sequent) → Prop
| ⟨.normal φ⟩, .LL, ⟨L, _, _⟩ => (~φ) ∈ L
| ⟨.normal φ⟩, .RR, ⟨_, R, _⟩ => (~φ) ∈ R
| ⟨.loaded χ⟩, .LL, ⟨_, _, O⟩ => O = some (Sum.inl (~'χ))
| ⟨.loaded χ⟩, .RR, ⟨_, _, O⟩ => O = some (Sum.inr (~'χ))

lemma LoadFormula.in_side_of_lf_inl {X} (lf : LoadFormula)
    (O_def : X.2.2 = some (Sum.inl (~'lf))) :
    (~''(AnyFormula.loaded lf)).in_side Side.LL X := by
  rcases X with ⟨L,R,O⟩
  simp_all [AnyNegFormula.in_side]

lemma LoadFormula.in_side_of_lf_inr {X} (lf : LoadFormula)
    (O_def : X.2.2 = some (Sum.inr (~'lf))) :
    (~''(AnyFormula.loaded lf)).in_side Side.RR X := by
  rcases X with ⟨L,R,O⟩
  simp_all [AnyNegFormula.in_side]

lemma Sequent.isLoaded_of_negAnyFormula_loaded {α ξ side} {X : Sequent}
    (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋ξ))).in_side side X)
    : X.isLoaded := by
  unfold AnyNegFormula.in_side at negLoad_in
  rcases X with ⟨L,R,O⟩
  rcases O with _|⟨lf|lf⟩
  · cases side <;> simp_all
  all_goals
    cases side <;> simp at negLoad_in
    subst negLoad_in
    cases ξ
    all_goals
      simp_all [isLoaded]

@[simp]
theorem Sequent.without_loaded_in_side_isFree (LRO : Sequent) ξ side :
    (~''(.loaded ξ)).in_side side LRO → (LRO.without (~''(.loaded ξ))).isFree := by
  rcases LRO with ⟨L, R, _|(OL|OR)⟩ <;> cases side
  all_goals
    simp [Sequent.without, isFree, isLoaded, AnyNegFormula.in_side]
    try aesop

/-! ## Whatever formulas

A type to describe all formulas that can occur in a sequent, without losing information
about whether they are loaded or not. -/

/-- Unfortunately our `AnyFormula` type does not include *negated* loaded formulas, so this is yet
another type to describe "whatever formula" can be in a sequent, without losing information. -/
inductive WhateverFormula : Type
  | any : AnyFormula → WhateverFormula
  | negLoad : NegLoadFormula → WhateverFormula
  deriving Repr, DecidableEq

instance : Coe Formula WhateverFormula := ⟨.any ∘ .normal⟩
instance : Coe LoadFormula WhateverFormula := ⟨.any ∘ .loaded⟩
instance : Coe NegLoadFormula WhateverFormula := ⟨WhateverFormula.negLoad⟩

def Olf.wForms : Olf → Finset WhateverFormula
  | none => {}
  | some (.inl (nφ)) => {.negLoad nφ}
  | some (.inr (nφ)) => {.negLoad nφ}

def Sequent.wForms : Sequent → Finset WhateverFormula
  | ⟨L,R,O⟩ => L.image Coe.coe ∪ R.image Coe.coe ∪ O.wForms

lemma Sequent.mem_toFinset_iff (φ : Formula) (X : Sequent) :
    φ ∈ X.toFinset ↔
      ((.any (.normal φ) : WhateverFormula) ∈ X.wForms
      ∨ (∃ χ, χ.unload = φ ∧ (.any (.loaded χ) ∈ X.wForms))
      ∨ (∃ ψ, negUnload ψ = φ ∧ (.negLoad ψ ∈ X.wForms))) := by
  rcases X with ⟨L, R, O⟩
  rcases O with _ | (ψ | ψ) <;>
    simp [Sequent.toFinset, Sequent.wForms, Olf.wForms, instCoeFormulaWhateverFormula] <;> tauto

/-- A normal formula is in `X.wForms` iff it is on the left or on the right of `X`.
(Note that the `Olf` part of `X` only contributes negated *loaded* formulas.) -/
lemma Sequent.mem_wForms_normal_iff {ψ : Formula} {L R : Finset Formula} {O : Olf} :
    ((ψ : WhateverFormula) ∈ Sequent.wForms ⟨L,R,O⟩) ↔ (ψ ∈ L ∨ ψ ∈ R) := by
  rcases O with _|(nl|nl) <;> simp [Sequent.wForms, Olf.wForms, instCoeFormulaWhateverFormula]

/-- In a basic sequent all free diamonds are atomic. -/
lemma Sequent.isAtomic_of_basic_of_negBox_mem_wForms {X : Sequent} {α φ} (bas : X.basic)
    (h : (~⌈α⌉φ : WhateverFormula) ∈ X.wForms) : α.isAtomic := by
  rcases X with ⟨L, R, O⟩
  rw [Sequent.mem_wForms_normal_iff] at h
  have := bas.1 (~⌈α⌉φ) (by simp [Sequent.toFinset]; tauto)
  cases α <;> simp_all [Formula.basic, Program.isAtomic]

/-- A negated loaded formula is in `X.wForms` iff it is the loaded formula of `X`. -/
lemma Sequent.mem_wForms_negLoad_iff {nlf : NegLoadFormula} {L R : Finset Formula} {O : Olf} :
    ((WhateverFormula.negLoad nlf) ∈ Sequent.wForms ⟨L,R,O⟩)
    ↔ (O = some (.inl nlf) ∨ O = some (.inr nlf)) := by
  rcases O with _|(nl|nl) <;>
    simp [Sequent.wForms, Olf.wForms, instCoeFormulaWhateverFormula] <;> tauto

/-- In a basic sequent all loaded diamonds are atomic. -/
lemma Sequent.isAtomic_of_basic_of_negLoad_mem_wForms {X : Sequent} {α} {ξ : AnyFormula}
    (bas : X.basic) (h : (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ X.wForms) : α.isAtomic := by
  rcases X with ⟨L, R, O⟩
  rw [Sequent.mem_wForms_negLoad_iff] at h
  have h_mem : (~ (⌊α⌋ξ).unload) ∈ Sequent.toFinset ⟨L, R, O⟩ := by
    rcases h with rfl | rfl <;> simp [Sequent.toFinset]
  have := bas.1 _ h_mem
  cases ξ <;> cases α <;> simp_all [Formula.basic, Program.isAtomic, LoadFormula.unload]

/-! ## Sorting Finsets of Sequents -/

/-- TODO: to make .all and other things computable, Finsets of Sequents should have an order to be
sorted, like Finsets of formulas with .fsort instead of .toList which is noncomputable. -/
def Finset.seqSort : Finset Sequent → List Sequent :=
  sorry

@[simp]
lemma Finset.mem_seqSort (A : Finset Sequent) : X ∈ A.seqSort ↔ X ∈ A := by
  sorry
