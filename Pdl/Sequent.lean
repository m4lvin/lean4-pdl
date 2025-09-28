import Mathlib.Data.Finset.Option

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

def Olf.L : Olf → List Formula
| none => []
| some (Sum.inl ⟨lf⟩) => [~ lf.unload]
| some (Sum.inr _) => []

@[simp]
lemma Olf.L_none : Olf.L none = [] := by rfl
@[simp]
lemma Olf.L_inr : Olf.L (some (Sum.inr lf)) = [] := by rfl

def Olf.R : Olf → List Formula
| none => []
| some (Sum.inl _) => []
| some (Sum.inr ⟨lf⟩) => [~ lf.unload]

@[simp]
lemma Olf.R_none : Olf.R none = [] := by rfl
@[simp]
lemma Olf.R_inl : Olf.R (some (Sum.inl lf)) = [] := by rfl

-- mathlib this?
@[simp]
instance Option.instHasSubsetOption : HasSubset (Option α) := HasSubset.mk
  λ o1 o2 =>
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
  λ o1 del =>
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
theorem Olf.change_none_none : Olf.change oldO none none = oldO := by
  cases oldO <;> simp [Olf.change, Option.overwrite, Option.insHasSdiff]

@[simp]
theorem Olf.change_some: Olf.change oldO whatever (some wnlf) = some wnlf := by
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

/-! ## Sequents and their (multi)set quality -/

/-- A tableau node is labelled with two lists of formulas and an `Olf`.
Each formula is placed on the left or right and up to one formula may be loaded. -/
def Sequent := List Formula × List Formula × Olf -- ⟨L, R, o⟩
  deriving DecidableEq, Repr

/-- Two `Sequent`s are set-equal when their components are finset-equal.
That is, we do not care about the order of the lists, but we do care
about the side of the formula and what formual is loaded.
Hint: use `List.toFinset.ext_iff` with this. -/
def Sequent.setEqTo : Sequent → Sequent → Prop
| (L,R,O), (L',R',O') => L.toFinset = L'.toFinset ∧ R.toFinset = R'.toFinset ∧ O = O'
deriving Decidable

instance : DecidableRel Sequent.setEqTo := by
  unfold Sequent.setEqTo DecidableRel
  rintro ⟨L,R,O⟩ ⟨L',R',O'⟩
  exact instDecidableAnd

/-- Two `Sequent`s are multiset-equal when their components are multiset-equal.
That is, we do not care about the order of the lists, but we do care about the side
on which the formula is, whether it is loaded or not, and how often it occurs. -/
def Sequent.multisetEqTo : Sequent → Sequent → Prop
| (L,R,O), (L',R',O') =>
  Multiset.ofList L = Multiset.ofList L' ∧ Multiset.ofList R = Multiset.ofList R' ∧ O = O'

instance : DecidableRel Sequent.multisetEqTo := by
  unfold Sequent.multisetEqTo DecidableRel
  rintro ⟨L,R,O⟩ ⟨L',R',O'⟩
  exact instDecidableAnd

@[grind]
lemma Sequent.setEqTo_of_multisetEqTo (X Y : Sequent) :
    X.multisetEqTo Y → X.setEqTo Y := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  intro hyp
  simp_all [multisetEqTo,setEqTo]
  grind [List.toFinset_eq_of_perm]

@[simp]
lemma Sequent.setEqTo_refl (X : Sequent) : X.setEqTo X := by
  rcases X with ⟨L,R,O⟩
  simp [Sequent.setEqTo]

lemma Sequent.setEqTo_symm (X Y : Sequent) : X.setEqTo Y ↔ Y.setEqTo X := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  unfold setEqTo
  tauto

@[simp]
lemma Sequent.multisetEqTo_refl (X : Sequent) : X.multisetEqTo X := by
  rcases X with ⟨L,R,O⟩
  simp [Sequent.multisetEqTo]

lemma Sequent.multisetEqTo_symm (X Y : Sequent) : X.multisetEqTo Y ↔ Y.multisetEqTo X := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  unfold multisetEqTo
  tauto

def Sequent.toFinset : Sequent → Finset Formula
| (L,R,O) => (L.toFinset ∪ R.toFinset) ∪ (O.map (Sum.elim negUnload negUnload)).toFinset

/-! ## Components and sides of sequents -/

@[simp]
def Sequent.L : Sequent → List Formula := λ⟨L,_,_⟩ => L
@[simp]
def Sequent.R : Sequent → List Formula := λ⟨_,R,_⟩ => R
@[simp]
def Sequent.O : Sequent → Olf := λ⟨_,_,O⟩ => O

@[simp]
def Sequent.left (X : Sequent) : List Formula := X.L ++ X.O.L
@[simp]
def Sequent.right (X : Sequent) : List Formula := X.R ++ X.O.R

/-! ## Formulas as elements of sequents -/

@[simp]
instance instMembershipFormulaSequent : Membership Formula Sequent := ⟨fun X φ => φ ∈ X.L ∨ φ ∈ X.R⟩

instance instDecidableMemFormulaSequent {φ : Formula} {X :Sequent} : Decidable (φ ∈ X) := by
  rcases X with ⟨L,R,o⟩
  simp only [instMembershipFormulaSequent]
  infer_instance

instance instFintypeSubtypeMemSequent {X : Sequent} : Fintype (Subtype (fun x => x ∈ X)) := by
  rcases X with ⟨L,R,o⟩
  simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R]
  apply Fintype.subtype (L.toFinset ∪ R.toFinset)
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
instance : Membership NegLoadFormula Sequent := ⟨NegLoadFormula.mem_Sequent⟩

def AnyNegFormula.mem_Sequent : (X : Sequent) → (anf : AnyNegFormula) → Prop
| X, ⟨.normal φ⟩ => (~φ) ∈ X
| X, ⟨.loaded χ⟩ => (~'χ).mem_Sequent X -- FIXME: ∈ not working here

@[simp]
instance : Membership AnyNegFormula Sequent := ⟨AnyNegFormula.mem_Sequent⟩

/-! ## Closed, basic, loaded and free sequents -/

/-- A sequent is *closed* iff it contains `⊥` or contains a formula and its negation. -/
def Sequent.closed (X : Sequent) : Prop :=
  ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X

/-- A sequent is *basic* iff it only contains basic formulas and is not closed. -/
def Sequent.basic : Sequent → Prop
  | (L, R, o) => (∀ f ∈ L ++ R ++ (o.map (Sum.elim negUnload negUnload)).toList, f.basic)
               ∧ ¬ Sequent.closed (L, R, o)

/-- A variant of `Fintype.decidableExistsFintype`, used by `instDecidableClosed`. -/
instance Fintype.decidableExistsConjFintype {α : Type u_1} {p q : α → Prop}
    [DecidablePred p] [DecidablePred q] [Fintype (Subtype p)]
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

def Sequent.isLoaded : Sequent → Bool
| ⟨_, _, none  ⟩ => False
| ⟨_, _, some _⟩ => True

def Sequent.isFree (Γ : Sequent) : Bool := ¬ Γ.isLoaded

@[simp]
theorem Sequent.none_isFree L R : Sequent.isFree (L, R, none) := by
  simp [Sequent.isFree, Sequent.isLoaded]

@[simp]
theorem Sequent.some_not_isFree L R olf : ¬ Sequent.isFree (L, R, some olf) := by
  simp [Sequent.isFree, Sequent.isLoaded]

-- delete me later?
theorem setEqTo_isLoaded_iff {X Y : Sequent} (h : X.setEqTo Y) : X.isLoaded = Y.isLoaded := by
  simp_all [Sequent.setEqTo, Sequent.isLoaded]
  rcases X with ⟨XL, XR, _|_⟩ <;> rcases Y with ⟨YL, YR, _|_⟩
  all_goals
    simp_all

theorem multisetEqTo_isLoaded_iff {X Y : Sequent} (h : X.multisetEqTo Y) : X.isLoaded = Y.isLoaded := by
  simp_all [Sequent.multisetEqTo, Sequent.isLoaded]
  rcases X with ⟨XL, XR, _|_⟩ <;> rcases Y with ⟨YL, YR, _|_⟩
  all_goals
    simp_all

/-! ## Semantics of sequents -/

instance modelCanSemImplySequent : vDash (KripkeModel W × W) Sequent :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, O⟩ =>
    ∀ f ∈ L ∪ R ∪ (O.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

instance modelCanSemImplyLLO : vDash (KripkeModel W × W) (List Formula × List Formula × Olf) :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, O⟩ =>
    ∀ f ∈ L ∪ R ∪ (O.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

instance instSequentHasSat : HasSat Sequent :=
  HasSat.mk fun Δ => ∃ (W : Type) (M : KripkeModel W) (w : W), (M,w) ⊨ Δ

open HasSat

theorem tautImp_iff_SequentUnsat {φ ψ} {X : Sequent} :
    X = ([φ], [~ψ], none) →
    (tautology (φ ↣ ψ) ↔ ¬ satisfiable X) :=
  by
  intro defX
  subst defX
  simp_all [tautology,satisfiable,modelCanSemImplySequent]

theorem vDash_setEqTo_iff {X Y : Sequent} (h : X.setEqTo Y) (M : KripkeModel W) (w : W) :
    (M,w) ⊨ X ↔ (M,w) ⊨ Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [modelCanSemImplySequent]
  unfold Sequent.setEqTo at h
  simp at h
  rw [List.toFinset.ext_iff, List.toFinset.ext_iff] at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  simp_all

theorem vDash_multisetEqTo_iff {X Y : Sequent} (h : X.multisetEqTo Y) (M : KripkeModel W) (w : W) :
    (M,w) ⊨ X ↔ (M,w) ⊨ Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [modelCanSemImplySequent]
  unfold Sequent.multisetEqTo at h
  simp at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  simp_all
  subst O_eq_O'
  have : ∀ f, f ∈ L ↔ f ∈ L' := fun f => List.Perm.mem_iff L_iff
  have : ∀ f, f ∈ R ↔ f ∈ R' := fun f => List.Perm.mem_iff R_iff
  aesop

/-- ## Removing loaded formulas from sequents -/

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

theorem AnyNegFormula.in_side_of_setEqTo {X Y} (h : X.setEqTo Y) {anf : AnyNegFormula} :
    anf.in_side side X ↔ anf.in_side side Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [Sequent.setEqTo] at *
  rw [List.toFinset.ext_iff, List.toFinset.ext_iff] at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  subst O_eq_O'
  cases side <;> rcases anf with ⟨(n|m)⟩ <;> simp_all [AnyNegFormula.in_side]

theorem AnyNegFormula.in_side_of_multisetEqTo {X Y} (h : X.multisetEqTo Y) {anf : AnyNegFormula} :
    anf.in_side side X ↔ anf.in_side side Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [Sequent.multisetEqTo] at *
  -- rw [List.toFinset.ext_iff, List.toFinset.ext_iff] at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  subst O_eq_O'
  cases side <;> rcases anf with ⟨(n|m)⟩ <;> simp_all [AnyNegFormula.in_side]
  · exact List.Perm.mem_iff L_iff
  · exact List.Perm.mem_iff R_iff

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
