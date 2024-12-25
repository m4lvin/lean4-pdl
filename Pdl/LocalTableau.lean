-- LOCAL TABLEAU (Section 3)

import Mathlib.Algebra.Order.BigOperators.Group.List

import Pdl.UnfoldBox
import Pdl.UnfoldDia
import Pdl.MultisetOrder

open HasLength

/-! ## Tableau Nodes -/

/-- In nodes we optionally have a negated loaded formula on the left or right. -/
abbrev Olf := Option (NegLoadFormula ⊕ NegLoadFormula)

@[simp]
def Olf.voc : Olf → Vocab
| none => {}
| some (Sum.inl nlf) => nlf.voc
| some (Sum.inr nlf) => nlf.voc

/-- A tableau node has two lists of formulas and an `Olf`. -/
-- TODO: rename `TNode` to `Sequent`
-- TODO: turn this into "abbrev" to avoid silly instance below.
def TNode := List Formula × List Formula × Olf -- ⟨L, R, o⟩
  deriving DecidableEq, Repr

-- Some thoughts about the TNode type:
-- - one formula may be loaded
-- - each (loaded) formula can be on the left/right/both

/-- Two `TNode`s are set-equal when their components are finset-equal.
That is, we do not care about the order of the lists, but we do care
about the side of the formula and what formual is loaded.
Hint: use `List.toFinset.ext_iff` with this. -/
def TNode.setEqTo : TNode → TNode → Prop
| (L,R,O), (L',R',O') => L.toFinset = L'.toFinset ∧ R.toFinset = R'.toFinset ∧ O = O'

def TNode.toFinset : TNode → Finset Formula
| (L,R,O) => (L.toFinset ∪ R.toFinset) ∪ (O.map (Sum.elim negUnload negUnload)).toFinset

@[simp]
def TNode.L : TNode → List Formula := λ⟨L,_,_⟩ => L
@[simp]
def TNode.R : TNode → List Formula := λ⟨_,R,_⟩ => R
@[simp]
def TNode.O : TNode → Olf := λ⟨_,_,O⟩ => O

def TNode.isLoaded : TNode → Bool
| ⟨_, _, none  ⟩ => False
| ⟨_, _, some _⟩ => True

def TNode.isFree (Γ : TNode) : Bool := ¬ Γ.isLoaded

@[simp]
theorem TNode.none_isFree L R : TNode.isFree (L, R, none) := by
  simp [TNode.isFree, TNode.isLoaded]

@[simp]
theorem TNode.some_not_isFree L R olf : ¬ TNode.isFree (L, R, some olf) := by
  simp [TNode.isFree, TNode.isLoaded]

theorem setEqTo_isLoaded_iff {X Y : TNode} (h : X.setEqTo Y) : X.isLoaded = Y.isLoaded := by
  simp_all [TNode.setEqTo, TNode.isLoaded]
  rcases X with ⟨XL, XR, _|_⟩ <;> rcases Y with ⟨YL, YR, _|_⟩
  all_goals
    simp_all

/-! ## Semantics of a TNode -/

instance modelCanSemImplyTNode : vDash (KripkeModel W × W) TNode :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, O⟩ =>
    ∀ f ∈ L ∪ R ∪ (O.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

-- silly but useful:
instance modelCanSemImplyLLO : vDash (KripkeModel W × W) (List Formula × List Formula × Olf) :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, O⟩ =>
    ∀ f ∈ L ∪ R ∪ (O.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

instance tNodeHasSat : HasSat TNode :=
  HasSat.mk fun Δ => ∃ (W : Type) (M : KripkeModel W) (w : W), (M,w) ⊨ Δ

open HasSat

theorem tautImp_iff_TNodeUnsat {φ ψ} {X : TNode} :
    X = ([φ], [~ψ], none) →
    (φ ⊨ ψ ↔ ¬ satisfiable X) :=
  by
  intro defX
  subst defX
  simp [satisfiable,evaluate,modelCanSemImplyTNode,formCanSemImplyForm,semImpliesLists] at *

theorem vDash_setEqTo_iff {X Y : TNode} (h : X.setEqTo Y) (M : KripkeModel W) (w : W) :
    (M,w) ⊨ X ↔ (M,w) ⊨ Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [TNode.setEqTo, modelCanSemImplyTNode, vDash]
  unfold TNode.setEqTo at h
  simp at h
  rw [List.toFinset.ext_iff, List.toFinset.ext_iff] at h
  rcases h with ⟨L_iff, R_iff, O_eq_O'⟩
  simp_all

/-! ## Different kinds of formulas as elements of TNode -/

@[simp]
instance : Membership Formula TNode := ⟨fun X φ => φ ∈ X.L ∨ φ ∈ X.R⟩

@[simp]
def NegLoadFormula.mem_TNode (X : TNode) (nlf : NegLoadFormula) : Prop :=
  X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

instance : Decidable (NegLoadFormula.mem_TNode ⟨L,R,O⟩ nlf) := by
  refine
    if h : O = some (Sum.inl nlf) then isTrue ?_
    else if h2 : O = some (Sum.inr nlf) then isTrue ?_ else isFalse ?_
  all_goals simp; tauto

def TNode.without : (LRO : TNode) → (naf : AnyNegFormula) → TNode
| ⟨L,R,O⟩, ⟨.normal f⟩  => ⟨L \ {~f}, R \ {~f}, O⟩
| ⟨L,R,O⟩, ⟨.loaded lf⟩ => if ((~'lf).mem_TNode ⟨L,R,O⟩) then ⟨L, R, none⟩ else ⟨L,R,O⟩

@[simp]
instance : Membership NegLoadFormula TNode := ⟨NegLoadFormula.mem_TNode⟩

def AnyNegFormula.mem_TNode : (X : TNode) → (anf : AnyNegFormula) → Prop
| X, ⟨.normal φ⟩ => (~φ) ∈ X
| X, ⟨.loaded χ⟩ => (~'χ).mem_TNode X -- FIXME: ∈ not working here

@[simp]
instance : Membership AnyNegFormula TNode := ⟨AnyNegFormula.mem_TNode⟩

/-! ## Local Tableaux -/

/-- A set is closed iff it contains `⊥` or contains a formula and its negation. -/
def closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X

-- Local rules replace a given set of formulas by other sets, one for each branch.
-- (In Haskell this is "ruleFor" in Logic.PDL.Prove.Tree.)
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

-- LOADED rule applications
-- Only the local diamond rule may be applied to loaded formulas.
-- (In MB page 19 these were the rules ¬u, ¬; ¬* and ¬?).
-- Each rule replaces the loaded formula by:
-- - up to one loaded formula,
-- - and a set of normal formulas.
-- It's annoying to need the rule twice here due to the definition of LoadFormula.
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

-- A LocalRule is a OneSidedLocalRule or a LoadRule.
-- Formulas can be in four places now: left, right, loaded left, loaded right.
inductive LocalRule : TNode → List TNode → Type
  | oneSidedL (orule : OneSidedLocalRule precond ress) : LocalRule (precond,∅,none) $ ress.map $ λ res => (res,∅,none)
  | oneSidedR (orule : OneSidedLocalRule precond ress) : LocalRule (∅,precond,none) $ ress.map $ λ res => (∅,res,none)
  | LRnegL (ϕ : Formula) : LocalRule ([ϕ], [~ϕ], none) ∅ --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ([~ϕ], [ϕ], none) ∅ -- ~ϕ occurs on the left side,  ϕ on the right
  -- NOTE: do we need neg rules for ({unload χ}, ∅, some (Sum.inl ~χ)) and (∅, {unload χ}, some (Sum.inr ~χ)), ..here?
  -- Probably not, because then we could also have closed before/without loading!
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
def applyLocalRule (_ : LocalRule (Lcond, Rcond, Ocond) ress) : TNode → List TNode
  | ⟨L, R, O⟩ => ress.map $
      fun (Lnew, Rnew, Onew) => ( L.diff Lcond ++ Lnew
                                , R.diff Rcond ++ Rnew
                                , Olf.change O Ocond Onew )

inductive LocalRuleApp : TNode → List TNode → Type
  | mk {L R : List Formula}
       {C : List TNode}
       {ress : List TNode}
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
    have := oneSidedLocalRuleTruth orule W M w
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

@[simp]
def isBasicForm : Formula → Bool
  | ⊥ => True -- TODO: change to False, covered by bot rule?
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | ⌈·_⌉_ => True
  | ~⌈·_⌉_ => True
  | _ => False

def isBasicSet : Finset Formula → Bool
  | X => ∀ P ∈ X, isBasicForm P

/-- A sequent is _basic_ iff it only contains ⊥, ¬⊥, p, ¬p, [A]_ or ¬[A]_ formulas. -/
def isBasic : TNode → Bool
  | (L, R, o) => ∀ f ∈ L ++ R ++ (o.map (Sum.elim negUnload negUnload)).toList, isBasicForm f

/-- Local tableau for `X`, maximal by definition. -/
inductive LocalTableau : (X : TNode) → Type
  | byLocalRule {X B} (_ : LocalRuleApp X B) (next : ∀ Y ∈ B, LocalTableau Y) : LocalTableau X
  | sim {X} : isBasic X → LocalTableau X

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

-- FIXME Only need this here, be careful with exporting this?
@[simp]
instance : LT Formula := ⟨Nat.lt on lmOfFormula⟩

instance Formula.WellFoundedLT : WellFoundedLT Formula := by
  constructor
  simp_all only [instLTFormula, Nat.lt_eq]
  exact @WellFounded.onFun Formula Nat Nat.lt lmOfFormula Nat.lt_wfRel.wf

instance Formula.instPreorderFormula : Preorder Formula := Preorder.lift lmOfFormula

@[simp]
def node_to_multiset : TNode → Multiset Formula
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
def List.Subperm.append {α : Type u_1} {l₁ l₂ r₁ r₂ : List α} :
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
def lt_TNode (X : TNode) (Y : TNode) := Multiset.IsDershowitzMannaLT (node_to_multiset X) (node_to_multiset Y)

-- Needed for termination of endNOdesOf.
-- Here we use `dm_wf` from MultisetOrder.lean.
instance : WellFoundedRelation TNode where
  rel := lt_TNode
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
      suffices ∃ τ' ∈ testsOfProgram (α;'β), lmOfFormula τ < 1 + lmOfFormula τ' by
        rw [List.attach_map_val (testsOfProgram (α;'β)) (fun x => lmOfFormula (~↑x))]
        rw [Nat.lt_succ]
        -- TODO: use `List.le_sum_of_mem` from newer mathlib
        exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
      refine ⟨τ, τ_in, by linarith⟩
    · subst def_ψ
      simp [lmOfFormula]
  case union α β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ) < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (α⋓β)).attach).sum.succ by
        simp_all
        linarith
      suffices ∃ τ' ∈ testsOfProgram (α⋓β), lmOfFormula τ < 1 + lmOfFormula τ' by
        rw [List.attach_map_val (testsOfProgram (α⋓β)) (fun x => lmOfFormula (~↑x))]
        rw [Nat.lt_succ]
        exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
      refine ⟨τ, τ_in, by linarith⟩
    · subst def_ψ
      simp [lmOfFormula]
  case star β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ) < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (∗β)).attach).sum.succ by
        simp_all
        linarith
      suffices ∃ τ' ∈ testsOfProgram (∗β), lmOfFormula τ < 1 + lmOfFormula τ' by
        rw [List.attach_map_val (testsOfProgram (∗β)) (fun x => lmOfFormula (~↑x))]
        rw [Nat.lt_succ]
        exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
      refine ⟨τ, τ_in, by linarith⟩
    · subst def_ψ
      simp [lmOfFormula]
  case test τ0 => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ) < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (?'τ0)).attach).sum.succ by
        simp_all
        linarith
      suffices ∃ τ' ∈ testsOfProgram (?'τ0), lmOfFormula τ < 1 + lmOfFormula τ' by
        rw [List.attach_map_val (testsOfProgram (?'τ0)) (fun x => lmOfFormula (~↑x))]
        rw [Nat.lt_succ]
        exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
      refine ⟨τ, τ_in, by linarith⟩
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
        -- TODO: use `List.le_sum_of_mem` from newer mathlib also here?
        apply List.single_le_sum (by simp) _
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
        -- TODO: use `List.le_sum_of_mem` from newer mathlib also here?
        apply List.single_le_sum (by simp) _
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
        -- TODO: use `List.le_sum_of_mem` from newer mathlib also here?
        apply List.single_le_sum (by simp) _
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
  · simp only [lmOfFormula, gt_iff_lt]
    cases α <;> simp_all [Program.isAtomic]

theorem LocalRule.Decreases (rule : LocalRule X ress) :
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

-- This is standard definition of DM.
-- TODO: Move to MultisetOrder
def MultisetLT' {α} [DecidableEq α] [Preorder α] (M : Multiset α) (N : Multiset α) : Prop :=
  ∃ (X Y Z: Multiset α),
        Y ≠ ∅ ∧
        M = Z + X ∧
        N = Z + Y ∧
        (∀ x ∈ X, ∃ y ∈ Y, x < y)

-- The definition used in the DM proof is equivalent to the standard definition.
-- TODO: Move to MultisetOrder
theorem MultisetDMLT.iff_MultisetLT' [DecidableEq α] [Preorder α] {M N : Multiset α} :
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

theorem localRuleApp.decreases_DM {X : TNode} {B : List TNode}
    (lrA : LocalRuleApp X B) : ∀ Y ∈ B, lt_TNode Y X :=
  by
  rcases lrA with ⟨Lcond,Rcond,Ocond,rule,preconP⟩
  rename_i L R ress O B_def
  subst B_def
  intro RES RES_in
  simp [applyLocalRule] at RES_in
  rcases RES_in with ⟨⟨Lnew,Rnew,Onew⟩, Y_in_ress, def_RES⟩
  unfold lt_TNode
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
  · exact LocalRule.Decreases rule _ Y_in_ress

@[simp]
def endNodesOf : {X : _} → LocalTableau X → List TNode
  | .(_), (@byLocalRule X B _lr next) => (B.attach.map (fun ⟨Y, h⟩ => endNodesOf (next Y h))).flatten
  | .(_), (@sim X _) => [X]
termination_by
  X => X -- pick up instance WellFoundedRelation TNode from above!
decreasing_by
  simp_wf
  apply localRuleApp.decreases_DM _lr Y h

/-- ## Helper functions, relating end nodes and children -/

-- TODO Computable version possible?
noncomputable def endNode_to_endNodeOfChildNonComp (lrA)
  (E_in: E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  @Subtype TNode (fun x => ∃ h, E ∈ endNodesOf (subTabs x h)) := by
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
    {X Y: TNode}
    {ltX}
    {C : List TNode}
    (lrA : LocalRuleApp X C)
    subTabs
    (h : ltX = LocalTableau.byLocalRule lrA subTabs)
    (Y_in : Y ∈ C)
    {Z : TNode}
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
