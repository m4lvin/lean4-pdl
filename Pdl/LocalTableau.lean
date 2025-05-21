import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Option

import Pdl.UnfoldBox
import Pdl.UnfoldDia
import Mathlib.Data.Multiset.DershowitzManna

/-! # Local Tableaux (Section 3) -/

open HasLength

/-! ## Tableau Nodes -/

/-- In nodes we optionally have a negated loaded formula on the left or right. -/
abbrev Olf := Option (NegLoadFormula ⊕ NegLoadFormula)

@[simp]
def Olf.voc : Olf → Vocab
| none => {}
| some (Sum.inl nlf) => nlf.voc
| some (Sum.inr nlf) => nlf.voc

/-- A tableau node is labelled with two lists of formulas and an `Olf`. -/
-- TODO: turn this into "abbrev" to avoid silly instance below.
def Sequent := List Formula × List Formula × Olf -- ⟨L, R, o⟩
  deriving DecidableEq, Repr

-- Some thoughts about the Sequent type:
-- - one formula may be loaded
-- - each (loaded) formula can be on the left/right/both

/-- Two `Sequent`s are set-equal when their components are finset-equal.
That is, we do not care about the order of the lists, but we do care
about the side of the formula and what formual is loaded.
Hint: use `List.toFinset.ext_iff` with this. -/
def Sequent.setEqTo : Sequent → Sequent → Prop
| (L,R,O), (L',R',O') => L.toFinset = L'.toFinset ∧ R.toFinset = R'.toFinset ∧ O = O'

def Sequent.multisetEqTo : Sequent → Sequent → Prop
| (L,R,O), (L',R',O') =>
  Multiset.ofList L = Multiset.ofList L' ∧ Multiset.ofList R = Multiset.ofList R' ∧ O = O'

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

@[simp]
def Sequent.L : Sequent → List Formula := λ⟨L,_,_⟩ => L
@[simp]
def Sequent.R : Sequent → List Formula := λ⟨_,R,_⟩ => R
@[simp]
def Sequent.O : Sequent → Olf := λ⟨_,_,O⟩ => O

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

/-! ## Semantics of a Sequent -/

instance modelCanSemImplySequent : vDash (KripkeModel W × W) Sequent :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, O⟩ =>
    ∀ f ∈ L ∪ R ∪ (O.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

-- silly but useful:
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
  simp only [Sequent.setEqTo, modelCanSemImplySequent, vDash]
  unfold Sequent.setEqTo at h
  simp at h
  rw [List.toFinset.ext_iff, List.toFinset.ext_iff] at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  simp_all

theorem vDash_multisetEqTo_iff {X Y : Sequent} (h : X.multisetEqTo Y) (M : KripkeModel W) (w : W) :
    (M,w) ⊨ X ↔ (M,w) ⊨ Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [Sequent.multisetEqTo, modelCanSemImplySequent, vDash]
  unfold Sequent.multisetEqTo at h
  simp at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  simp_all
  subst O_eq_O'
  have : ∀ f, f ∈ L ↔ f ∈ L' := fun f => List.Perm.mem_iff L_iff
  have : ∀ f, f ∈ R ↔ f ∈ R' := fun f => List.Perm.mem_iff R_iff
  aesop

/-! ## Different kinds of formulas as elements of Sequent -/

@[simp]
instance : Membership Formula Sequent := ⟨fun X φ => φ ∈ X.L ∨ φ ∈ X.R⟩

@[simp]
def NegLoadFormula.mem_Sequent (X : Sequent) (nlf : NegLoadFormula) : Prop :=
  X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

instance : Decidable (NegLoadFormula.mem_Sequent ⟨L,R,O⟩ nlf) := by
  refine
    if h : O = some (Sum.inl nlf) then isTrue ?_
    else if h2 : O = some (Sum.inr nlf) then isTrue ?_ else isFalse ?_
  all_goals simp; tauto

def Sequent.without : (LRO : Sequent) → (naf : AnyNegFormula) → Sequent
| ⟨L,R,O⟩, ⟨.normal f⟩  => ⟨L \ {~f}, R \ {~f}, O⟩
| ⟨L,R,O⟩, ⟨.loaded lf⟩ => if ((~'lf).mem_Sequent ⟨L,R,O⟩) then ⟨L, R, none⟩ else ⟨L,R,O⟩

@[simp]
instance : Membership NegLoadFormula Sequent := ⟨NegLoadFormula.mem_Sequent⟩

def AnyNegFormula.mem_Sequent : (X : Sequent) → (anf : AnyNegFormula) → Prop
| X, ⟨.normal φ⟩ => (~φ) ∈ X
| X, ⟨.loaded χ⟩ => (~'χ).mem_Sequent X -- FIXME: ∈ not working here

@[simp]
instance : Membership AnyNegFormula Sequent := ⟨AnyNegFormula.mem_Sequent⟩

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
  simp only [Sequent.setEqTo, modelCanSemImplySequent, vDash] at *
  rw [List.toFinset.ext_iff, List.toFinset.ext_iff] at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  subst O_eq_O'
  cases side <;> rcases anf with ⟨(n|m)⟩ <;> simp_all [AnyNegFormula.in_side]

theorem AnyNegFormula.in_side_of_multisetEqTo {X Y} (h : X.multisetEqTo Y) {anf : AnyNegFormula} :
    anf.in_side side X ↔ anf.in_side side Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [Sequent.multisetEqTo, modelCanSemImplySequent, vDash] at *
  -- rw [List.toFinset.ext_iff, List.toFinset.ext_iff] at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  subst O_eq_O'
  cases side <;> rcases anf with ⟨(n|m)⟩ <;> simp_all [AnyNegFormula.in_side]
  · exact List.Perm.mem_iff L_iff
  · exact List.Perm.mem_iff R_iff

@[simp]
theorem Sequent.without_loaded_in_side_isFree (LRO : Sequent) ξ side :
    (~''(.loaded ξ)).in_side side LRO → (LRO.without (~''(.loaded ξ))).isFree := by
  rcases LRO with ⟨L, R, _|(OL|OR)⟩ <;> cases side
  all_goals
    simp [Sequent.without, isFree, isLoaded, AnyNegFormula.in_side]
    try aesop

/-! ## Local Tableaux -/

/-- Local rules replace a given set of formulas by other sets, one for each branch.
The list of resulting branches can be empty, representing that the given set is closed.
In the Haskell prover this is done in "ruleFor" in the Logic.PDL.Prove.Tree module. -/
inductive OneSidedLocalRule : List Formula → List (List Formula) → Type
  -- PROP LOGIC
  -- closing rules:
  | bot                 : OneSidedLocalRule [⊥]      ∅
  | not (φ   : Formula) : OneSidedLocalRule [φ, ~φ]  ∅
  | neg (φ   : Formula) : OneSidedLocalRule [~~φ]    [[φ]]
  | con (φ ψ : Formula) : OneSidedLocalRule [φ ⋀ ψ]  [[φ,ψ]]
  | nCo (φ ψ : Formula) : OneSidedLocalRule [~(φ⋀ψ)] [[~φ], [~ψ]]
  -- PROGRAMS
  -- the two general local rules:
  | box (α φ) : (notAtom : ¬ α.isAtomic) → OneSidedLocalRule [ ⌈α⌉φ] (unfoldBox     α φ)
  | dia (α φ) : (notAtom : ¬ α.isAtomic) → OneSidedLocalRule [~⌈α⌉φ] (unfoldDiamond α φ)
  deriving DecidableEq, Repr

theorem oneSidedLocalRuleTruth (lr : OneSidedLocalRule X B) : Con X ≡ discon B :=
  by
  intro W M w
  cases lr
  all_goals try (simp; done) -- takes care of all propositional rules
  case box α φ notAtom =>
    rw [conEval]
    simp only [List.mem_singleton, forall_eq]
    rw [localBoxTruth α φ W M w]
    simp only [disEval, List.mem_map, exists_exists_and_eq_and, unfoldBox, disconEval]
    constructor
    · rintro ⟨l,hyp⟩; use l; rw [conEval] at hyp; tauto
    · rintro ⟨l,hyp⟩; use l; rw [conEval]; tauto
  case dia α φ notAtom =>
    rw [conEval]
    simp only [List.mem_singleton, forall_eq, discon, unfoldDiamond]
    rw [localDiamondTruth α φ W M w, disEval, disconEval]
    apply mapCon_mapForall

/-- The loaded diamond rule, given by `unfoldDiamondLoaded`.
In MB page 19 these were multiple rules ¬u, ¬; ¬* and ¬?.
It replaces the loaded formula by up to one loaded formula and a list of normal formulas.
It's a bit annoying to need the rule twice here due to the definition of LoadFormula
and the extra definition of `unfoldDiamondLoaded'`.  -/
inductive LoadRule : NegLoadFormula → List (List Formula × Option NegLoadFormula) → Type
  | dia  {α χ} : (notAtom : ¬ α.isAtomic) → LoadRule (~'⌊α⌋(χ : LoadFormula)) (unfoldDiamondLoaded  α χ)
  | dia' {α φ} : (notAtom : ¬ α.isAtomic) → LoadRule (~'⌊α⌋(φ : Formula    )) (unfoldDiamondLoaded' α φ)
  deriving DecidableEq, Repr

/-- Given a LoadRule application, define the equivalent unloaded rule application.
This allows re-using `oneSidedLocalRuleTruth` to prove `loadRuleTruth`. -/
def LoadRule.unload : LoadRule (~'χ) B → OneSidedLocalRule [~χ.unload] (B.map pairUnload)
| @dia α χ notAtom => unfoldDiamondLoaded_eq α χ ▸ OneSidedLocalRule.dia α χ.unload notAtom
| @dia' α φ notAtom => unfoldDiamondLoaded'_eq α φ ▸ OneSidedLocalRule.dia α φ notAtom

/-- The loaded unfold rule is sound and invertible.
In the notes this is part of localRuleTruth. -/
theorem loadRuleTruth (lr : LoadRule (~'χ) B) :
    (~χ.unload) ≡ dis (B.map (Con ∘ pairUnload)) :=
  by
  intro W M w
  have := oneSidedLocalRuleTruth (lr.unload) W M w
  simp only [Con, evaluate, disconEval, List.mem_map] at this
  simp only [evaluate, disEval, List.mem_map]
  rw [this]
  clear this
  simp only [Prod.exists]
  constructor
  · rintro ⟨Y, ⟨a, ⟨b, ab_in_B, def_Y⟩⟩, w_Y⟩
    use Con Y
    simp_all only [conEval, implies_true, and_true]
    use a, b, ab_in_B
    rw [← def_Y]
    simp
  · rintro ⟨f, ⟨a, b, ab_in_B, def_f⟩, w_f⟩
    subst def_f
    simp at w_f
    rw [conEval] at w_f
    use pairUnload (a,b)
    constructor
    · use a, b
    · exact w_f

/-- A local rule is a `OneSidedLocalRule`, a left-right contradiction, or a `LoadRule`.
Note that formulas can be in four places: left, right, loaded left, loaded right.

We do *not* have neg/contradiction rules between loaded and unloaded formulas (i.e.
between `({unload χ}, ∅, some (Sum.inl ~χ))` and `(∅, {unload χ}, some (Sum.inr ~χ))`)
because in any such case we could also close the tableau before or without loading.
-/
inductive LocalRule : Sequent → List Sequent → Type
  | oneSidedL (orule : OneSidedLocalRule precond ress) : LocalRule (precond,∅,none) $ ress.map $ λ res => (res,∅,none)
  | oneSidedR (orule : OneSidedLocalRule precond ress) : LocalRule (∅,precond,none) $ ress.map $ λ res => (∅,res,none)
  | LRnegL (ϕ : Formula) : LocalRule ([ϕ], [~ϕ], none) ∅ --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ([~ϕ], [ϕ], none) ∅ -- ~ϕ occurs on the left side,  ϕ on the right
  | loadedL (χ : LoadFormula) (lrule : LoadRule (~'χ) ress) :
      LocalRule (∅, ∅, some (Sum.inl (~'χ))) $ ress.map $ λ (X, o) => (X, ∅, o.map Sum.inl)
  | loadedR (χ : LoadFormula) (lrule : LoadRule (~'χ) ress) :
      LocalRule (∅, ∅, some (Sum.inr (~'χ))) $ ress.map $ λ (X, o) => (∅, X, o.map Sum.inr)
  deriving Repr
  -- TODO -- deriving DecidableEq does not work with function in loadedL and loadedR

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

/-- Instance that is used to say `(O : Olf) \ (O' : Olf)`. -/
instance Option.insHasSdiff [DecidableEq α] : SDiff (Option α) := SDiff.mk
  λ o1 del =>
  match o1, del with
  | none, _ => none
  | some f, none => some f
  | some f, some g => if f = g then none else some f

@[simp]
def Option.overwrite : Option α → Option α → Option α
| old, none   => old
| _  , some x => some x

def Olf.change (oldO : Olf) (Ocond : Olf) (newO : Olf) : Olf := (oldO \ Ocond).overwrite newO

@[simp]
theorem Olf.change_none_none : Olf.change oldO none none = oldO := by
  cases oldO <;> simp [Olf.change, Option.overwrite, Option.insHasSdiff]

@[simp]
theorem Olf.change_some_some_none : Olf.change (some wnlf) (some wnlf) none = none := by
  simp [Olf.change, Option.overwrite, Option.insHasSdiff]

@[simp]
theorem Olf.change_some: Olf.change oldO whatever (some wnlf) = some wnlf := by
    cases oldO <;> simp [Olf.change, Option.overwrite, Option.insHasSdiff]

@[simp]
def applyLocalRule : LocalRule (Lcond, Rcond, Ocond) ress → Sequent → List Sequent
  | _, ⟨L, R, O⟩ => ress.map $
      fun (Lnew, Rnew, Onew) => ( L.diff Lcond ++ Lnew
                                , R.diff Rcond ++ Rnew
                                , Olf.change O Ocond Onew )

inductive LocalRuleApp : Sequent → List Sequent → Type
  | mk {L R : List Formula}
       {C : List Sequent}
       {ress : List Sequent}
       {O : Olf}
       (Lcond Rcond : List Formula)
       (Ocond : Olf)
       (rule : LocalRule (Lcond, Rcond, Ocond) ress)
       {hC : C = applyLocalRule rule (L,R,O)}
       (preconditionProof : List.Subperm Lcond L ∧ List.Subperm Rcond R ∧ Ocond ⊆ O)
       : LocalRuleApp (L,R,O) C

theorem localRuleTruth
    (lrA : LocalRuleApp X C) {W} (M : KripkeModel W) (w : W)
  : (M,w) ⊨ X ↔ ∃ Ci ∈ C, (M,w) ⊨ Ci
  := by
  rcases X with ⟨L,R,O⟩
  rcases lrA with ⟨Lcond, Rcond, Ocond, rule, preconditionProof⟩
  cases rule

  case oneSidedL ress orule hC =>
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp [applyLocalRule] at *
    constructor
    · intro w_LRO
      have : evaluate M w (discon ress) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [List.mem_union_iff, List.mem_append]
        exact Or.inl $ Or.inl $ List.Subperm.subset preconditionProof f_in
      rw [disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [List.mem_union_iff, List.mem_append] at f_in
        rcases f_in with (((f_in_L | f_in_Y) | f_in_R) | f_in_O)
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inl $ List.diff_subset L Lcond f_in_L
        · exact claim f f_in_Y
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          tauto
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inr f_in_O
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      simp only [List.mem_union_iff, List.mem_append] at f_in
      rcases f_in with ((f_in_L | f_in_R) | f_in_O)
      · rcases em (f ∈ Lcond) with f_in_cond | f_notin_cond
        · have : ∀ f ∈ Lcond, evaluate M w f := by
            rw [← conEval, osTruth, disconEval]
            use Y
            constructor
            · exact Y_in
            · intro f f_in; apply w_LYRO; simp_all
          exact this f f_in_cond
        · apply w_LYRO
          simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inl $ Or.inl $ List.mem_diff_of_mem f_in_L f_notin_cond
      · apply w_LYRO; simp_all
      · apply w_LYRO; simp_all
  case oneSidedR ress orule hC =>
    -- based on oneSidedL case
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp [applyLocalRule] at *
    constructor
    · intro w_LRO
      have : evaluate M w (discon ress) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [List.mem_union_iff, List.mem_append]
        exact Or.inl $ Or.inr $ List.Subperm.subset preconditionProof f_in
      rw [disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [List.mem_union_iff, List.mem_append] at f_in
        rcases f_in with ((f_in_L | (f_in_R | f_in_Y)) | f_in_O)
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inl f_in_L
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inr $ List.diff_subset R Rcond f_in_R
        · exact claim f f_in_Y
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inr f_in_O
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      simp only [List.mem_union_iff, List.mem_append] at f_in
      rcases f_in with ((f_in_L | f_in_R) | f_in_O)
      · apply w_LYRO; simp_all
      · rcases em (f ∈ Rcond) with f_in_cond | f_notin_cond
        · have : ∀ f ∈ Rcond, evaluate M w f := by
            rw [← conEval, osTruth, disconEval]
            use Y
            constructor
            · exact Y_in
            · intro f f_in; apply w_LYRO; simp_all
          exact this f f_in_cond
        · apply w_LYRO
          simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inr $ Or.inl $ List.mem_diff_of_mem f_in_R f_notin_cond
      · apply w_LYRO; simp_all

  case LRnegL φ hC =>
    subst hC
    simp [applyLocalRule] at *
    intro hyp
    have := hyp φ
    have := hyp (~φ)
    aesop
  case LRnegR φ hC =>
    subst hC
    simp [applyLocalRule] at *
    intro hyp
    have := hyp φ
    have := hyp (~φ)
    aesop

  case loadedL ress χ lrule hC  =>
    have := loadRuleTruth lrule W M w
    rw [disEval] at this
    subst hC
    simp at preconditionProof
    subst preconditionProof
    simp [modelCanSemImplyForm,modelCanSemImplyLLO] at *
    constructor
    · intro hyp
      have hyp' := hyp (~χ.unload)
      simp at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨f, ⟨X , O, in_ress, def_f⟩, w_f⟩
      cases O
      · use (L ++ X, R, none)
        constructor
        · use X, none; simp only [Option.map_none', Olf.change_some_some_none, and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L ++ X, R, some (Sum.inl val))
        constructor
        · use X, some val; simp only [Option.map_some', Olf.change_some, and_true]; exact in_ress
        · intro g g_in
          subst def_f
          simp_all [pairUnload, negUnload, conEval]
          have := w_f (~val.1.unload)
          aesop
    · rintro ⟨Ci, ⟨⟨X, O, ⟨in_ress, def_Ci⟩⟩, w_Ci⟩⟩
      intro f f_in
      subst def_Ci
      cases O <;> simp at *
      · cases f_in
        · aesop
        subst_eqs
        simp only [evaluate]
        rw [this]
        use (Con (pairUnload (X, none)))
        constructor
        · use X, none
        · simp only [pairUnload, conEval]
          intro f f_in
          apply w_Ci
          simp_all
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use Con (pairUnload (X, some val))
          constructor
          · use X, some val
          · simp only [pairUnload, negUnload, conEval, List.mem_union_iff, List.mem_singleton]
            intro g g_in
            rcases g_in with (_|g_def)
            · apply w_Ci; simp_all
            · subst g_def; apply w_Ci; simp_all

  case loadedR ress χ lrule hC =>
    -- based on loadedL case
    have := loadRuleTruth lrule W M w
    rw [disEval] at this
    subst hC
    simp at preconditionProof
    subst preconditionProof
    simp [modelCanSemImplyForm,modelCanSemImplyLLO] at *
    constructor
    · intro hyp
      have hyp' := hyp (~χ.unload)
      simp at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨f, ⟨X , O, in_ress, def_f⟩, w_f⟩
      cases O
      · use (L, R ++ X, none)
        constructor
        · use X, none; simp only [Option.map_none', Olf.change_some_some_none, and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L, R ++ X, some (Sum.inr val))
        constructor
        · use X, some val; simp only [Option.map_some', Olf.change_some, and_true]; exact in_ress
        · intro g g_in
          subst def_f
          simp_all [pairUnload, negUnload, conEval]
          have := w_f (~val.1.unload)
          aesop
    · rintro ⟨Ci, ⟨⟨X, O, ⟨in_ress, def_Ci⟩⟩, w_Ci⟩⟩
      intro f f_in
      subst def_Ci
      cases O <;> simp at *
      · cases f_in
        · aesop
        subst_eqs
        simp only [evaluate]
        rw [this]
        use (Con (pairUnload (X, none)))
        constructor
        · use X, none
        · simp only [pairUnload, conEval]
          intro f f_in
          apply w_Ci
          simp_all
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use Con (pairUnload (X, some val))
          constructor
          · use X, some val
          · simp only [pairUnload, negUnload, conEval, List.mem_union_iff, List.mem_singleton]
            intro g g_in
            rcases g_in with (_|g_def)
            · apply w_Ci; simp_all
            · subst g_def; apply w_Ci; simp_all

/-- A basic formula is of the form `¬⊥`, `p`, `¬p`, `[a]_` or `¬[a]_`.
Note: in the article also `⊥` is basic, but not here because then
`OneSidedLocalRule.bot` can be applied to it. -/
@[simp]
def Formula.basic : Formula → Bool
  | ⊥ => False
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | ⌈·_⌉_ => True
  | ~⌈·_⌉_ => True
  | _ => False

/-- A sequent is *closed* iff it contains `⊥` or contains a formula and its negation. -/
def Sequent.closed (X : Sequent) : Prop :=
  ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X

/-- A sequent is *basic* iff it only contains basic formulas and is not closed. -/
def Sequent.basic : Sequent → Prop
  | (L, R, o) => (∀ f ∈ L ++ R ++ (o.map (Sum.elim negUnload negUnload)).toList, f.basic)
               ∧ ¬ Sequent.closed (L, R, o)

/-- Local tableau for `X`, maximal by definition. -/
inductive LocalTableau : (X : Sequent) → Type
  | byLocalRule {X B} (_ : LocalRuleApp X B) (next : ∀ Y ∈ B, LocalTableau Y) : LocalTableau X
  | sim {X} : X.basic → LocalTableau X

-- Should be easier to do, or in mathlib already?
theorem mem_of_two_subperm {α} {l : List α} {a b : α}  [DecidableEq α] :
    [a,b].Subperm l → a ∈ l ∧ b ∈ l := by
  intro subl
  have := List.subperm_ext_iff.1 subl
  simp at this
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  constructor
  · linarith
  · rcases this with ⟨al, bl⟩
    by_cases a = b
    · subst_eqs
      simp_all [-List.count_pos_iff]
      rw [@List.subperm_ext_iff] at subl
      linarith
    · aesop

/-- If we can apply a local rule to a sequent then it cannot be basic. -/
lemma nonbasic_of_localRuleApp (lrA : LocalRuleApp X B)  : ¬ X.basic := by
  rcases X with ⟨L,R,o⟩
  unfold Sequent.basic
  simp only [List.append_assoc, List.mem_append, Option.mem_toList, Option.mem_def,
    Option.map_eq_some', Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr]
  rw [and_iff_not_or_not]
  simp only [not_not]
  rcases lrA with ⟨Lcond, Rcond, Ocond, rule, preconditionProof⟩
  cases rule
  case oneSidedL ress orule hC =>
    cases orule
    case bot => right; simp_all [Sequent.closed]
    case not φ =>
      right; simp_all [Sequent.closed]; right
      have := mem_of_two_subperm preconditionProof
      refine ⟨φ, Or.inl ?_, Or.inl ?_⟩ <;> tauto
    case neg φ =>
      left; push_neg
      refine ⟨~~φ, Or.inl (by simp_all), by simp⟩
    case con φ1 φ2 =>
      left; push_neg
      refine ⟨φ1 ⋀ φ2, Or.inl (by simp_all), by simp⟩
    case nCo φ1 φ2 =>
      left; push_neg
      refine ⟨~(φ1 ⋀ φ2), Or.inl (by simp_all), by simp⟩
    case box α φ α_nonAtom =>
      left; push_neg
      refine ⟨⌈α⌉φ, Or.inl (by simp_all), ?_⟩
      cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
    case dia α φ α_nonAtom =>
      left; push_neg
      refine ⟨~⌈α⌉φ, Or.inl ?_, ?_⟩
      · rw [List.singleton_subperm_iff] at preconditionProof
        exact preconditionProof.1
      · cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
  case oneSidedR ress orule hC => -- analogous to oneSidedL
    cases orule
    case bot => right; simp_all [Sequent.closed]
    case not φ =>
      right; simp_all [Sequent.closed]; right
      have := mem_of_two_subperm preconditionProof
      refine ⟨φ, Or.inr ?_, Or.inr ?_⟩ <;> tauto
    case neg φ =>
      left; push_neg
      refine ⟨~~φ, Or.inr (by simp_all), by simp⟩
    case con φ1 φ2 =>
      left; push_neg
      refine ⟨φ1 ⋀ φ2, Or.inr (by simp_all), by simp⟩
    case nCo φ1 φ2 =>
      left; push_neg
      refine ⟨~(φ1 ⋀ φ2), Or.inr (by simp_all), by simp⟩
    case box α φ α_nonAtom =>
      left; push_neg
      refine ⟨⌈α⌉φ, Or.inr (by simp_all), ?_⟩
      cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
    case dia α φ α_nonAtom =>
      left; push_neg
      refine ⟨~⌈α⌉φ, Or.inr (Or.inl ?_), ?_⟩
      · rw [List.singleton_subperm_iff] at preconditionProof
        exact preconditionProof.2.1
      · cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
  case LRnegL =>
    right
    simp [Sequent.closed]
    aesop
  case LRnegR =>
    right
    simp [Sequent.closed]
    aesop
  case loadedL ress χ lrule hC =>
    left
    push_neg
    cases lrule
    case dia α χ α_nonAtom =>
      refine ⟨(⌊α⌋AnyFormula.loaded χ).unload, Or.inr (Or.inr ?_), ?_⟩
      · sorry
      · cases α <;> simp_all
        simp [Program.isAtomic] at α_nonAtom
    case dia' α φ α_nonAtom =>
      refine ⟨(⌊α⌋AnyFormula.normal φ).unload, Or.inr (Or.inr ?_), ?_⟩
      · sorry
      · cases α <;> simp_all
        simp [Program.isAtomic] at α_nonAtom
  case loadedR => -- should be analogous to loadedL
    sorry

/-! ## Termination of LocalTableau -/

theorem testsOfProgram_sizeOf_lt α : ∀ τ ∈ testsOfProgram α, sizeOf τ < sizeOf α := by
  intro τ τ_in
  cases α
  all_goals
    simp [testsOfProgram] at *
  case sequence α β =>
    rcases τ_in with τ_in | τ_in
    · have := testsOfProgram_sizeOf_lt α _ τ_in; linarith
    · have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case union α β =>
    rcases τ_in with τ_in | τ_in
    · have := testsOfProgram_sizeOf_lt α _ τ_in; linarith
    · have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case star β =>
    have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case test τ =>
    subst_eqs
    linarith

open LocalTableau

/-- The local measure we use together with D-M to show that LocalTableau are finite. -/
@[simp]
def lmOfFormula : (f : Formula) → Nat
| ⊥ => 0
| ·_ => 0
| φ⋀ψ => 1 + lmOfFormula φ + lmOfFormula ψ
| ⌈·_⌉ _ => 0 -- No more local steps
| ⌈α⌉φ => 1 + lmOfFormula φ -- unfoldBox
            + ((testsOfProgram α).attach.map (fun τ => lmOfFormula (~τ.1))).sum
| ~⊥ => 0
| ~·_ => 0
| ~~φ => 1 + lmOfFormula φ
| ~(φ⋀ψ) => 1 + lmOfFormula (~φ) + lmOfFormula (~ψ)
| ~⌈·_⌉ _ => 0 -- No more local steps
| ~⌈α⌉φ => 1 + lmOfFormula (~φ) -- unfoldDia
             + ((testsOfProgram α).attach.map (fun τ => lmOfFormula τ.1)).sum
decreasing_by
  all_goals simp_wf
  all_goals try linarith
  all_goals
    have := testsOfProgram_sizeOf_lt _ _ τ.2
    linarith

theorem lmOfFormula_lt_box_of_nonAtom (h : ¬ α.isAtomic) :
    lmOfFormula (~φ) < lmOfFormula (~⌈α⌉φ) := by
  cases α <;> simp_all [List.attach_map_val, Program.isAtomic, testsOfProgram] <;> linarith

-- Only need this here, so don't export this.
@[simp]
private instance instLTFormula : LT Formula := ⟨fun φ1 φ2 => lmOfFormula φ1 < lmOfFormula φ2⟩

instance Formula.WellFoundedLT : WellFoundedLT Formula := by
  constructor
  simp_all only [instLTFormula, Nat.lt_eq]
  exact @WellFounded.onFun Formula Nat Nat.lt lmOfFormula Nat.lt_wfRel.wf

instance Formula.instPreorderFormula : Preorder Formula := Preorder.lift lmOfFormula

@[simp]
def node_to_multiset : Sequent → Multiset Formula
| (L, R, none) => (L + R)
| (L, R, some (Sum.inl (~'χ))) => (L + R + [~χ.unload])
| (L, R, some (Sum.inr (~'χ))) => (L + R + [~χ.unload])

def Olf.toForm : Olf → Multiset Formula
| none => {}
| some (Sum.inl (~'χ)) => {~χ.unload}
| some (Sum.inr (~'χ)) => {~χ.unload}

theorem node_to_multiset_eq : node_to_multiset (L, R, O) = Multiset.ofList L + Multiset.ofList R + O.toForm := by
  cases O
  · simp [node_to_multiset, Olf.toForm]
  case some nlf =>
    cases nlf
    · simp [node_to_multiset, Olf.toForm]
    · simp [node_to_multiset, Olf.toForm]

/-- If each three parts are the same then node_to_multiset is the same. -/
theorem node_to_multiset_eq_of_three_eq (hL : L = L') (hR : R = R') (hO : O = O') :
    node_to_multiset (L, R, O) = node_to_multiset (L', R', O') := by
  aesop

-- mathlib this?
lemma List.Subperm.append {α : Type u_1} {l₁ l₂ r₁ r₂ : List α} :
    l₁.Subperm l₂ → r₁.Subperm r₂ → (l₁ ++ r₁).Subperm (l₂ ++ r₂) := by
  intro hl hr
  cases l₁
  case nil =>
    simp
    apply List.Subperm.trans hr
    induction l₂
    · simp
      exact Subperm.refl r₂
    case cons IH =>
      simp_all
      apply List.Subperm.cons_right
      exact IH
  case cons h t =>
    have : (h :: t ++ r₁).Subperm (l₂ ++ r₁) := by
      rw [List.subperm_append_right]
      exact hl
    apply List.Subperm.trans this
    rw [List.subperm_append_left]
    exact hr

theorem preconP_to_submultiset (preconditionProof : List.Subperm Lcond L ∧ List.Subperm Rcond R ∧ Ocond ⊆ O) :
    node_to_multiset (Lcond, Rcond, Ocond) ≤ node_to_multiset (L, R, O) :=
  by
  cases Ocond <;> cases O
  all_goals (try (rename_i f g; cases f; cases g))
  all_goals (try (rename_i f; cases f))
  all_goals
    simp [node_to_multiset] at * -- FIXME avoid non-terminal simp here!
  case none.none =>
    exact (List.Subperm.append preconditionProof.1 preconditionProof.2)
  case none.some.inl =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2) f
    simp_all
    linarith
  case none.some.inr =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2) f
    simp_all
    linarith
  case some.some.inl.inl.neg =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2.1) f
    simp_all
  case some.some.inr.neg a =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2.1) f
    cases g <;> (rename_i nlform; cases nlform; simp_all)

theorem Multiset.sub_of_le [DecidableEq α] {M N X Y: Multiset α} (h : N ≤ M) :
    M - N + Y = X ↔ M + Y = X + N := by
  constructor
  all_goals
    intro hyp
    ext φ
    rw [@Multiset.ext] at hyp
    specialize hyp φ
    rw [@le_iff_count] at h
    specialize h φ
    simp only [count_add, count_sub] at *
    omega

theorem Multiset_diff_append_of_le [DecidableEq α] {R Rcond Rnew : List α} :
    Multiset.ofList (R.diff Rcond ++ Rnew)
    = Multiset.ofList R - Multiset.ofList Rcond + Multiset.ofList Rnew := by
  rw [@Multiset.coe_sub]
  rw [Multiset.coe_add]

theorem List.Perm_diff_append_of_Subperm {α} [DecidableEq α] {L M : List α} (h : M.Subperm L) :
    L.Perm (L.diff M ++ M) := by
  rw [perm_iff_count]
  intro φ
  rw [← Multiset.coe_count, ← Multiset.coe_count]
  rw [@Multiset_diff_append_of_le α _ L M M]
  rw [tsub_add_cancel_of_le h]

theorem List.count_eq_diff_of_subperm [DecidableEq α] {L M : List α} (h : M.Subperm L) φ :
    List.count φ L = List.count φ (L.diff M) + List.count φ M := by
  suffices L.Perm (L.diff M ++ M) by
    rw [← count_append]
    have := @List.perm_iff_count _ _ L (L.diff M ++ M)
    tauto
  apply List.Perm_diff_append_of_Subperm h

/-- Applying `node_to_multiset` before or after `applyLocalRule` gives the same. -/
theorem node_to_multiset_of_precon {O Ocond Onew : Olf}
    (precon : Lcond.Subperm L ∧ Rcond.Subperm R ∧ Ocond ⊆ O)
    (O_extracon : O ≠ none → Ocond = none → Onew = none)
    : node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond) + node_to_multiset (Lnew, Rnew, Onew)
    = node_to_multiset (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, Olf.change O Ocond Onew) := by
  have my_le := preconP_to_submultiset precon
  rw [Multiset.sub_of_le my_le]
  clear my_le
  simp only [node_to_multiset_eq]
  rw [Multiset_diff_append_of_le]
  rw [Multiset_diff_append_of_le]
  have claim : ↑L - ↑Lcond + ↑Lnew + (↑R - ↑Rcond + ↑Rnew) + (O.change Ocond Onew).toForm + (↑Lcond + ↑Rcond + Ocond.toForm) = ↑L + ↑Lnew + (↑R + ↑Rnew) + (O.change Ocond Onew).toForm + (Ocond.toForm) := by
    rw [← add_assoc]
    apply add_right_cancel_iff.mpr
    rw [add_add_add_comm]
    rw [← add_assoc]
    rw [add_right_comm]
    rw [@add_right_cancel_iff]
    ext φ
    simp only [Multiset.coe_sub, Multiset.coe_add, List.append_assoc, Multiset.coe_count,
      List.count_append]
    have := List.count_eq_diff_of_subperm precon.2.1 φ
    have := List.count_eq_diff_of_subperm precon.1 φ
    linarith
  rw [claim]
  clear claim
  ext φ
  simp
  suffices Multiset.count φ O.toForm + (Multiset.count φ Onew.toForm) =
      Multiset.count φ (O.change Ocond Onew).toForm + Multiset.count φ Ocond.toForm by
    linarith
  unfold Olf.change
  have claim : (Olf.toForm (Option.overwrite (O \ Ocond) Onew)) = O.toForm - Ocond.toForm + Onew.toForm := by
    all_goals cases O_Def : O <;> try (cases O_def2 : O)
    all_goals cases Ocond_Def : Ocond <;> try (cases Ocond_def2 : Ocond)
    all_goals cases Onew_Def : Onew <;> try (cases Onew_def2 : Onew)
    all_goals simp_all [Olf.toForm, Olf.change, Option.insHasSdiff]
  rw [claim]
  -- we now get 3 * 3 * 3 = 27 cases
  all_goals cases O <;> try (rename_i O; cases O)
  all_goals cases Onew <;> try (rename_i Onew; cases Onew)
  all_goals cases Ocond <;> try (rename_i cond; cases cond)
  all_goals simp_all [Olf.toForm, Olf.change] -- solve 23 out of 27 cases, of which 4 use O_extracon
  all_goals
    linarith

@[simp]
def lt_Sequent (X : Sequent) (Y : Sequent) := Multiset.IsDershowitzMannaLT (node_to_multiset X) (node_to_multiset Y)

-- Needed for termination of endNOdesOf.
-- Here we use `dm_wf` from MultisetOrder.lean.
instance : WellFoundedRelation Sequent where
  rel := lt_Sequent
  wf := InvImage.wf node_to_multiset (Multiset.wellFounded_isDershowitzMannaLT)

theorem LocalRule.cond_non_empty (rule : LocalRule (Lcond, Rcond, Ocond) X) :
    node_to_multiset (Lcond, Rcond, Ocond) ≠ ∅ :=
  by
  cases rule
  all_goals simp [node_to_multiset]
  case oneSidedL _ orule => cases orule <;> simp
  case oneSidedR _ orule => cases orule <;> simp

theorem Multiset.sub_add_of_subset_eq [DecidableEq α] {M : Multiset α} (h : X ≤ M):
    M = M - X + X := (tsub_add_cancel_of_le h).symm

theorem unfoldBox.decreases_lmOf_nonAtomic {α : Program} {φ : Formula} {X : List Formula}
    (α_non_atomic : ¬ α.isAtomic)
    (X_in : X ∈ unfoldBox α φ)
    (ψ_in_X : ψ ∈ X)
    : lmOfFormula ψ < lmOfFormula (⌈α⌉φ) := by
  have ubc := unfoldBoxContent (α) φ X X_in ψ ψ_in_X
  cases α <;> simp [Program.isAtomic] at *
  case sequence α β =>
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ) < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (α;'β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (α;'β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ]
      apply List.le_sum_of_mem
      simp only [List.mem_map]
      use τ
    · subst def_ψ
      simp [lmOfFormula]
  case union α β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ) < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (α⋓β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (α⋓β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]
  case star β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ) < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (∗β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (∗β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]
  case test τ0 => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ) < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (?'τ0)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (?'τ0)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]

theorem lmOfFormula.le_union_left α β φ : lmOfFormula (~⌈α⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) := by
  cases α <;> simp [lmOfFormula, List.attach_map_val]
  all_goals
    simp [testsOfProgram]

theorem lmOfFormula.le_union_right α β φ : lmOfFormula (~⌈β⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) := by
  cases β <;> simp [lmOfFormula, List.attach_map_val]
  all_goals
    simp [testsOfProgram]

theorem H_goes_down (α : Program) φ {Fs δ} (in_H : (Fs, δ) ∈ H α) {ψ} (in_Fs: ψ ∈ Fs) :
    lmOfFormula ψ < lmOfFormula (~⌈α⌉φ) := by
  cases α
  · simp_all [H]
  case sequence α β =>
    simp only [lmOfFormula]
    simp only [H, List.mem_flatten, List.mem_map, Prod.exists] at in_H
    rcases in_H with ⟨l, ⟨Fs', δ', in_H, def_l⟩, in_l⟩
    · subst def_l
      by_cases δ' = []
      · subst_eqs
        simp_all only [List.nil_append, ite_true, List.mem_flatten, List.mem_map, Prod.exists]
        rcases in_l with ⟨l, ⟨Fs'', δ'', in_Hβ, def_l⟩, in_l⟩
        subst def_l
        simp only [List.mem_singleton, Prod.mk.injEq] at in_l
        cases in_l
        subst_eqs
        simp_all only [List.mem_union_iff]
        rcases in_Fs with in_Fs'|in_Fs''
        · have IHα := H_goes_down α φ in_H in_Fs'
          cases α
          all_goals
            simp [lmOfFormula] at IHα
          all_goals
            simp only [List.attach_map_val, testsOfProgram] at *
            simp_all [lmOfFormula]
            try linarith
        · have IHβ := H_goes_down β φ in_Hβ in_Fs''
          cases β
          all_goals
            simp_all [H, testsOfProgram, lmOfFormula, List.attach_map_val]
            try linarith
      · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq, testsOfProgram,
        List.attach_append, List.map_append, List.map_map, List.sum_append]
        rw [Function.comp_def, Function.comp_def, List.attach_map_val, List.attach_map_val]
        cases in_l
        subst_eqs
        have IHα := H_goes_down α φ in_H in_Fs
        cases α
        all_goals
          simp_all [H, testsOfProgram, lmOfFormula, List.attach_map_val]
        all_goals
          try rw [Function.comp_def, Function.comp_def, List.attach_map_val, List.attach_map_val] at IHα
          try linarith
  case union α β =>
    simp only [H, List.mem_union_iff] at in_H
    rcases in_H with hyp|hyp
    · have IHα := H_goes_down α φ hyp in_Fs
      suffices lmOfFormula (~⌈α⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) by linarith
      apply lmOfFormula.le_union_left
    · have IHβ := H_goes_down β φ hyp in_Fs
      suffices lmOfFormula (~⌈β⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) by linarith
      apply lmOfFormula.le_union_right
  case star α =>
    simp only [lmOfFormula]
    simp [H] at in_H
    rcases in_H with _ | ⟨l, ⟨Fs', δ', in_H', def_l⟩, in_l⟩
    · simp_all only [List.not_mem_nil]
    · subst def_l
      by_cases δ' = []
      · simp_all only [List.nil_append, ite_true, List.not_mem_nil]
      · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq, testsOfProgram]
        cases in_l
        subst_eqs
        have IHα := H_goes_down α φ in_H' in_Fs
        cases α <;> simp_all only [lmOfFormula, not_lt_zero']
  case test τ =>
    simp_all [H, testsOfProgram, List.attach_map_val]

theorem unfoldDiamond.decreases_lmOf_nonAtomic {α : Program} {φ : Formula} {X : List Formula}
    (α_non_atomic : ¬ α.isAtomic)
    (X_in : X ∈ unfoldDiamond α φ)
    (ψ_in_X : ψ ∈ X)
    : lmOfFormula ψ < lmOfFormula (~⌈α⌉φ) :=
  by
  have udc := unfoldDiamondContent _ _ _ X_in _ ψ_in_X
  rcases udc with ψ_def | ⟨τ, τ_in, ψ_def⟩ | ⟨a, δ, ψ_def⟩ <;> subst ψ_def
  · exact lmOfFormula_lt_box_of_nonAtom α_non_atomic
  · cases α <;> simp_all [Program.isAtomic, testsOfProgram, List.attach_map_val]
    case sequence α β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (α;'β))).sum.succ by
        simp_all [testsOfProgram, Function.comp_def, List.attach_map_val]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (α;'β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
    case union α β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (α⋓β))).sum.succ by
        simp_all [testsOfProgram, Function.comp_def, List.attach_map_val]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (α;'β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
    case star β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (∗β))).sum.succ by
        simp_all [testsOfProgram]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (∗β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
  · simp only [lmOfFormula, gt_iff_lt]
    cases α <;> simp_all [Program.isAtomic]

theorem LocalRuleDecreases (rule : LocalRule X ress) :
    ∀ Y ∈ ress, ∀ y ∈ node_to_multiset Y, ∃ x ∈ node_to_multiset X, y < x :=
  by
    intro Y Y_in_ress y y_in_Y
    cases rule
    case LRnegL => simp at *
    case LRnegR => simp at *

    case oneSidedL orule =>
      cases orule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case neg.refl => linarith
      case con.refl => cases y_in_Y <;> (subst_eqs; linarith)
      case nCo => cases Y_in_ress <;> (subst_eqs; simp at * ; subst_eqs; linarith)
      case dia α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldDiamond.decreases_lmOf_nonAtomic notAtom E_in y_in_Y
      case box α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldBox.decreases_lmOf_nonAtomic notAtom E_in y_in_Y

    case oneSidedR orule =>
      cases orule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case neg.refl => linarith
      case con.refl => cases y_in_Y <;> (subst_eqs; linarith)
      case nCo => cases Y_in_ress <;> (subst_eqs; simp at * ; subst_eqs ; linarith)
      case dia α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldDiamond.decreases_lmOf_nonAtomic notAtom  E_in y_in_Y
      case box α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldBox.decreases_lmOf_nonAtomic notAtom E_in y_in_Y

    case loadedL lrule =>
      simp [node_to_multiset]
      cases lrule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case dia α χ notAtom =>
        -- we re-use the lemma for the free analogue here
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded_eq α χ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload, negUnload]
      case dia' α φ notAtom =>
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded'_eq α φ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload]

    case loadedR lrule =>
      simp [node_to_multiset]
      cases lrule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case dia α χ notAtom =>
        -- we re-use the lemma for the free analogue here
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded_eq α χ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload, negUnload]
      case dia' α φ notAtom =>
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded'_eq α φ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload]

-- An equivalent definition of DM.
def MultisetLT' {α} [Preorder α] (M : Multiset α) (N : Multiset α) : Prop :=
  ∃ (X Y Z: Multiset α),
        Y ≠ ∅ ∧
        M = Z + X ∧
        N = Z + Y ∧
        (∀ x ∈ X, ∃ y ∈ Y, x < y)

-- The definition used in Multiset.IsDershowitzMannaLT is equivalent to ours.
theorem MultisetDMLT.iff_MultisetLT' [Preorder α] {M N : Multiset α} :
    Multiset.IsDershowitzMannaLT M N ↔ MultisetLT' M N := by
  unfold MultisetLT'
  constructor
  · intro M_LT_N
    cases M_LT_N
    aesop
  · intro M_LT'_N
    rcases M_LT'_N with ⟨X,Y,Z,claim⟩
    constructor
    all_goals tauto

theorem localRuleApp.decreases_DM {X : Sequent} {B : List Sequent}
    (lrA : LocalRuleApp X B) : ∀ Y ∈ B, lt_Sequent Y X :=
  by
  rcases lrA with ⟨Lcond,Rcond,Ocond,rule,preconP⟩
  rename_i L R ress O B_def
  subst B_def
  intro RES RES_in
  simp [applyLocalRule] at RES_in
  rcases RES_in with ⟨⟨Lnew,Rnew,Onew⟩, Y_in_ress, def_RES⟩
  unfold lt_Sequent
  simp at def_RES
  rw [MultisetDMLT.iff_MultisetLT']
  unfold MultisetLT'
  use node_to_multiset (Lnew, Rnew, Onew) -- choose X to be the newly added formulas
  use node_to_multiset (Lcond, Rcond, Ocond) -- choose Y to be the removed formulas
  -- Now choose a way to define Z (the context formulas that stay)
  -- let Z:= use node_to_multiset RES - node_to_multiset (Lnew, Rnew, Onew) -- way 1
  let Z := node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond) -- way 2
  use Z
  -- claim that the other definition would have been the same:
  have Z_eq : Z = node_to_multiset RES - node_to_multiset (Lnew, Rnew, Onew) := by
    unfold Z
    have : node_to_multiset RES = node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond) + node_to_multiset (Lnew, Rnew, Onew) := by
      have lrOprop : O ≠ none → Ocond = none → Onew = none := by
        cases O <;> cases Ocond <;> cases Onew <;> cases rule <;> simp_all
        all_goals
          rcases Y_in_ress with ⟨a, a_in, bla⟩ ; cases bla
      rw [← def_RES, node_to_multiset_of_precon preconP lrOprop]
    rw [this]
    subst def_RES
    simp_all only [Option.instHasSubsetOption, add_tsub_cancel_right]
  split_ands
  · exact (LocalRule.cond_non_empty rule : node_to_multiset (Lcond, Rcond, Ocond) ≠ ∅)
  · rw [Z_eq]
    apply Multiset.sub_add_of_subset_eq
    -- This works but should be cleaned up to avoid non-terminal simp.
    all_goals cases O <;> try (rename_i cond; cases cond)
    all_goals cases Onew <;> try (rename_i f; cases f)
    all_goals cases Ocond <;> try (rename_i cond; cases cond)
    all_goals simp_all
    all_goals subst_eqs
    all_goals
      simp only []
      rw [Multiset.le_iff_count]
      intro φ
      simp_all
      linarith
  · apply Multiset.sub_add_of_subset_eq
    exact preconP_to_submultiset preconP
  · exact LocalRuleDecreases rule _ Y_in_ress

@[simp]
def endNodesOf : {X : _} → LocalTableau X → List Sequent
  | .(_), (@byLocalRule X B _lr next) => (B.attach.map (fun ⟨Y, h⟩ => endNodesOf (next Y h))).flatten
  | .(_), (@sim X _) => [X]
termination_by
  X => X -- pick up instance WellFoundedRelation Sequent from above!
decreasing_by
  simp_wf
  apply localRuleApp.decreases_DM _lr Y h

/-! ## Helper functions, relating end nodes and children -/

-- TODO Computable version possible?
noncomputable def endNode_to_endNodeOfChildNonComp (lrA)
  (E_in: E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  @Subtype Sequent (fun x => ∃ h, E ∈ endNodesOf (subTabs x h)) := by
  simp [endNodesOf] at E_in
  choose l h E_in using E_in
  choose c c_in l_eq using h
  subst l_eq
  use c
  use c_in

theorem endNodeIsEndNodeOfChild (lrA)
  (E_in: E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  ∃ Y h, E ∈ endNodesOf (subTabs Y h) := by
  have := endNode_to_endNodeOfChildNonComp lrA E_in
  use this
  aesop

theorem endNodeOfChild_to_endNode
    {X Y: Sequent}
    {ltX}
    {C : List Sequent}
    (lrA : LocalRuleApp X C)
    subTabs
    (h : ltX = LocalTableau.byLocalRule lrA subTabs)
    (Y_in : Y ∈ C)
    {Z : Sequent}
    (Z_in: Z ∈ endNodesOf (subTabs Y Y_in))
    : Z ∈ endNodesOf ltX :=
  by
  cases h' : subTabs Y Y_in -- No induction needed for this!
  case sim Y_isSimp =>
    subst h
    simp
    use endNodesOf (subTabs Y Y_in)
    constructor
    · use Y, Y_in
    · exact Z_in
  case byLocalRule C' subTabs' lrA' =>
    subst h
    rw [h'] at Z_in
    simp
    use endNodesOf (subTabs Y Y_in)
    constructor
    · use Y, Y_in
    · rw [h']
      exact Z_in

/-! ## Overall Soundness and Invertibility of LocalTableau -/

theorem localTableauTruth {X} (lt : LocalTableau X) {W} (M : KripkeModel W) (w : W) :
    (M,w) ⊨ X  ↔ ∃ Y ∈ endNodesOf lt, (M,w) ⊨ Y := by
  induction lt
  case byLocalRule Y B lrA next IH  =>
    have := localRuleTruth lrA M w
    aesop
  case sim =>
    simp_all

theorem localTableauSat {X} (lt : LocalTableau X) :
    satisfiable X ↔ ∃ Y ∈ endNodesOf lt, satisfiable Y := by
  constructor
  · rintro ⟨W, M, w, w_X⟩
    rw [localTableauTruth lt M w] at w_X
    rcases w_X with ⟨Y, Y_in, w_Y⟩
    use Y, Y_in, W, M, w
  · rintro ⟨Y, Y_in, ⟨W, M, w, w_Y⟩⟩
    use W, M, w
    apply (localTableauTruth lt M w).2
    use Y

/-! ## Local Tableaux make progress

These lemmas are used to show soundness, in particular `loadedDiamondPaths`.
-/

/-- End nodes of any local tableau are basic. -/
lemma endNodesOf_basic {X Z} {ltZ : LocalTableau Z} : X ∈ endNodesOf ltZ → X.basic := by
  induction ltZ
  case byLocalRule B lrA next IH =>
    intro X_in
    simp [endNodesOf] at X_in
    aesop
  case sim X =>
    simp_all

/-- If `X` is not basic, then all end nodes `Y` of a local tableau `lt` for `X`
are strictly lower than `X` according to the DM-ordering of their multisets. -/
theorem endNodesOf_nonbasic_lt_Sequent {X Y} (lt : LocalTableau X) (X_nonbas : ¬ X.basic) :
    Y ∈ endNodesOf lt → lt_Sequent Y X := by
  induction lt
  case byLocalRule X B lrA next IH =>
    intro Y_in
    simp at Y_in
    rcases Y_in with ⟨l, ⟨Z, Z_in_B, def_l⟩ , Y_in_l⟩
    subst def_l
    by_cases Z.basic
    case pos Z_basic =>
      have next_Z_is_end : endNodesOf (next Z Z_in_B) = [Z] := by
        cases next Z Z_in_B <;> simp
        case byLocalRule lrA =>
          absurd nonbasic_of_localRuleApp lrA
          exact Z_basic
      have Z_eq_Y : Z = Y := by aesop
      subst Z_eq_Y
      exact localRuleApp.decreases_DM lrA _ Z_in_B
    case neg Z_nonbas =>
      -- We use that lt_Sequent is transitive.
      apply @Multiset.IsDershowitzMannaLT.trans _ _ _ (node_to_multiset Z)
      · exact IH Z Z_in_B Z_nonbas Y_in_l
      · exact localRuleApp.decreases_DM lrA _ Z_in_B
  case sim =>
    exfalso
    tauto

/-- If a sequent is lower according the DM-ordering, then it is different. -/
lemma non_eq_of_ltSequent : lt_Sequent X Y → X ≠ Y := by
  intro lt X_eq_Y
  subst X_eq_Y
  absurd lt
  -- This us easy, because DM ordering is irreflexive.
  have := WellFounded.isIrrefl (instWellFoundedRelationSequent.2)
  apply this.1

/-- If `X` is not basic, then for all end nodes `Y` of a
local tableau `lt` for `X` we have that `Y ≠ X`. -/
theorem endNodesOf_nonbasic_non_eq {X Y} (lt : LocalTableau X) (X_nonbas : ¬ X.basic) :
    Y ∈ endNodesOf lt → Y ≠ X := by
  intro Y_in
  apply non_eq_of_ltSequent
  apply endNodesOf_nonbasic_lt_Sequent lt X_nonbas Y_in

-- upstream me / Haitian? ;-)
lemma IsDershowitzMannaLT.irrefl [Preorder α] [WellFoundedLT α] (X : Multiset α) :
    ¬ Multiset.IsDershowitzMannaLT X X := by
  apply (WellFounded.isIrrefl (?_)).1
  exact (@Multiset.instWellFoundedisDershowitzMannaLT α _ _).2

/-- If a sequent is lower according to the DM-ordering, then they are multiset-different.
(The analogue with finset instead of multiset does not hold.) -/
lemma non_multisetEqTo_of_ltSequent : lt_Sequent X Y → ¬ X.multisetEqTo Y := by
  intro lt X_eq_Y
  unfold lt_Sequent at lt
  have : node_to_multiset X ≠ node_to_multiset Y := by
    intro hyp
    rw [hyp] at lt
    absurd lt
    apply IsDershowitzMannaLT.irrefl
  clear lt
  rcases X with ⟨L,R,_|(lfl|lfr)⟩ <;> rcases Y with ⟨L',R',_|(lfl'|lfr')⟩
  <;> simp [Sequent.multisetEqTo, node_to_multiset] at *
  · sorry
  · simp_all
    sorry
  · simp_all
    sorry
