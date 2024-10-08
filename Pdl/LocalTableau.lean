-- LOCAL TABLEAU

import Mathlib.Algebra.Order.BigOperators.Group.List

import Pdl.UnfoldBox
import Pdl.UnfoldDia
import Pdl.MultisetOrder

open HasLength

/-! ## Tableau Nodes -/

/-- In nodes we optionally have a negated loaded formula on the left or right. -/
abbrev Olf := Option (NegLoadFormula ⊕ NegLoadFormula)

open HasVocabulary

@[simp]
def vocabOfOlf : Olf → Vocab
| none => {}
| some (Sum.inl nlf) => voc nlf
| some (Sum.inr nlf) => voc nlf

@[simp]
instance : HasVocabulary Olf := ⟨ vocabOfOlf ⟩

/-- A tableau node has two lists of formulas and an `Olf`. -/
-- TODO: rename `TNode` to `Sequent`
-- TODO: turn this into "abbrev" to avoid silly instance below.
def TNode := List Formula × List Formula × Olf -- ⟨L, R, o⟩
  deriving DecidableEq, Repr

-- Some thoughts about the TNode type:
-- - one formula may be loaded
-- - each (loaded) formula can be on the left/right/both

/-- We do not care about the order of the lists.
TNodes are considered equal when their Finset versions are equal.
Hint: use `List.toFinset.ext_iff` with this. -/
def TNode.setEqTo : TNode → TNode → Prop
| (L,R,O), (L',R',O') => L.toFinset == L'.toFinset ∧ R.toFinset == R'.toFinset ∧ O == O'

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

theorem setEqTo_isLoaded_iff {X Y : TNode} (h : X.setEqTo Y) : X.isLoaded = Y.isLoaded := by
  simp_all [TNode.setEqTo, TNode.isLoaded]
  rcases X with ⟨XL, XR, _|_⟩ <;> rcases Y with ⟨YL, YR, _|_⟩
  all_goals
    simp_all
  all_goals
    exfalso; rcases h with ⟨_,_,impossible⟩ ; exact (Bool.eq_not_self _).mp impossible

/-! ## Semantics of a TNode -/

instance modelCanSemImplyTNode : vDash (KripkeModel W × W) TNode :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, o⟩ => ∀ f ∈ L ∪ R ∪ (o.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

-- silly but useful:
instance modelCanSemImplyLLO : vDash (KripkeModel W × W) (List Formula × List Formula × Olf) :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, o⟩ => ∀ f ∈ L ∪ R ∪ (o.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

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

/-! ## Different kinds of formulas as elements of TNode -/

@[simp]
instance : Membership Formula TNode := ⟨fun φ X => φ ∈ X.L ∨ φ ∈ X.R⟩

@[simp]
def NegLoadFormula_in_TNode (nlf : NegLoadFormula) (X : TNode) : Prop :=
  X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

instance : Decidable (NegLoadFormula_in_TNode nlf ⟨L,R,O⟩) := by
  refine
    if h : O = some (Sum.inl nlf) then isTrue ?_
    else if h2 : O = some (Sum.inr nlf) then isTrue ?_ else isFalse ?_
  all_goals simp; tauto

def TNode.without : (LRO : TNode) → (naf : AnyNegFormula) → TNode
| ⟨L,R,O⟩, ⟨.normal f⟩  => ⟨L \ {~f}, R \ {~f}, O⟩
| ⟨L,R,O⟩, ⟨.loaded lf⟩ => if (NegLoadFormula_in_TNode (~'lf) ⟨L,R,O⟩) then ⟨L, R, none⟩ else ⟨L,R,O⟩

@[simp]
instance : Membership NegLoadFormula TNode := ⟨NegLoadFormula_in_TNode⟩

def AnyNegFormula_in_TNode : (anf : AnyNegFormula) → (X : TNode) → Prop
| ⟨.normal φ⟩, X => (~φ) ∈ X
| ⟨.loaded χ⟩, X => NegLoadFormula_in_TNode (~'χ) X -- FIXME: ∈ not working here

@[simp]
instance : Membership AnyNegFormula TNode := ⟨AnyNegFormula_in_TNode⟩

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

/-- Given a LoadRule application, define the equivalent unloaded rule application.
This allows re-using `oneSidedLocalRuleTruth` to prove `loadRuleTruth`. -/
def LoadRule.unload : LoadRule (~'χ) B → OneSidedLocalRule [~(unload χ)] (B.map pairUnload)
| @dia α χ notAtom => unfoldDiamondLoaded_eq α χ ▸ OneSidedLocalRule.dia α ((_root_.unload χ)) notAtom
| @dia' α φ notAtom => unfoldDiamondLoaded'_eq α φ ▸ OneSidedLocalRule.dia α φ notAtom

/-- The loaded unfold rule is sound and invertible.
In the notes this is part of localRuleTruth. -/
theorem loadRuleTruth (lr : LoadRule (~'χ) B) :
    (~(unload χ)) ≡ dis (B.map (Con ∘ pairUnload)) :=
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

@[simp]
def Olf.change : (oldO : Olf) → (Ocond : Olf) → (newO : Olf) → Olf
| oldO, none  , none      => oldO      -- no change
| _   , none  , some wnlf => some wnlf -- loading
| _   , some _, none      => none      -- unloading
| _   , some _, some wnlf => some wnlf -- replacing

@[simp]
def applyLocalRule (_ : LocalRule (Lcond, Rcond, Ocond) ress) : TNode → List TNode
  | ⟨L, R, O⟩ => ress.map $
      fun (Lnew, Rnew, Onew) => ( L.diff Lcond ++ Lnew
                                , R.diff Rcond ++ Rnew
                                , Olf.change O Ocond Onew )

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
    {L R : List Formula}
    {C : List TNode}
    {O : Olf}
    (lrA : LocalRuleApp (L,R,O) C) {W} (M : KripkeModel W) (w : W)
  : (M,w) ⊨ (L,R,O) ↔ ∃ Ci ∈ C, (M,w) ⊨ Ci
  := by
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
      have hyp' := hyp (~unload χ)
      simp at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨f, ⟨X , O, in_ress, def_f⟩, w_f⟩
      cases O
      · use (L ++ X, R, none)
        constructor
        · use X, none; simp only [Option.map_none', and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L ++ X, R, some (Sum.inl val))
        constructor
        · use X, some val; simp only [Option.map_some', and_true]; exact in_ress
        · intro g g_in
          subst def_f
          simp_all [pairUnload, negUnload, conEval]
          have := w_f (~unload val.1)
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
      have hyp' := hyp (~unload χ)
      simp at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨f, ⟨X , O, in_ress, def_f⟩, w_f⟩
      cases O
      · use (L, R ++ X, none)
        constructor
        · use X, none; simp only [Option.map_none', and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L, R ++ X, some (Sum.inr val))
        constructor
        · use X, some val; simp only [Option.map_some', and_true]; exact in_ress
        · intro g g_in
          subst def_f
          simp_all [pairUnload, negUnload, conEval]
          have := w_f (~unload val.1)
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
| ~⌈α⌉φ => 1 + lmOfFormula φ -- unfoldDia
             + ((testsOfProgram α).attach.map (fun τ => lmOfFormula τ.1)).sum
decreasing_by
  all_goals simp_wf
  all_goals try linarith
  all_goals
    have := testsOfProgram_sizeOf_lt _ _ τ.2
    linarith

/-
def boxTestSumOf α := ((testsOfProgram α).attach.map (fun ⟨τ, _τ_in⟩ => lmOfFormula τ)).sum

def diaTestSumOf α := ((testsOfProgram α).attach.map (fun ⟨τ, _τ_in⟩ => lmOfFormula (~τ))).sum

-- fox box, also needed for diamond?
theorem testsOfProgram_lmOf_lt α : ∀ τ ∈ testsOfProgram α, lmOfFormula (~τ) < boxTestSumOf α := by
  sorry
-/

-- FIXME Only need this here, be careful with exporting this?
@[simp]
instance : LT Formula := ⟨Nat.lt on lmOfFormula⟩

instance Formula.WellFoundedLT : WellFoundedLT Formula := by
  unfold WellFoundedLT
  constructor
  simp_all only [instLTFormula, Nat.lt_eq]
  exact @WellFounded.onFun Formula Nat Nat.lt lmOfFormula Nat.lt_wfRel.wf

instance Formula.instPreorderFormula : Preorder Formula := Preorder.lift lmOfFormula

@[simp]
def node_to_multiset : TNode → Multiset Formula
| (L, R, none) => (L + R)
| (L, R, some (Sum.inl (~'χ))) => (L + R + [~ unload χ])
| (L, R, some (Sum.inr (~'χ))) => (L + R + [~ unload χ])

/-- If each three parts are the same then node_to_multiset is the same. -/
theorem node_to_multiset_eq_of_three_eq (hL : L = L') (hR : R = R') (hO : O = O') :
    node_to_multiset (L, R, O) = node_to_multiset (L', R', O') := by
  aesop

/-- Applying `node_to_multiset` before or after `applyLocalRule` gives the same. -/
theorem node_to_multiset_of_precon (precon : Lcond.Subperm L ∧ Rcond.Subperm R ∧ Ocond ⊆ O) :
    node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond) + node_to_multiset (Lnew, Rnew, Onew)
    = node_to_multiset (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, Olf.change O Ocond Onew) := by
  rcases precon with ⟨Lpre, Rpre, Opre⟩
  ext φ
  all_goals cases O <;> try (rename_i cond; cases cond)
  all_goals cases Onew <;> try (rename_i f; cases f)
  all_goals cases Ocond <;> try (rename_i cond; cases cond)
  all_goals simp_all
  ·
    sorry
  all_goals
    sorry

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

@[simp]
def lt_TNode (X : TNode) (Y : TNode) := MultisetDMLT (node_to_multiset X) (node_to_multiset Y)

-- Needed for termination of endNOdesOf.
-- Here we use `dm_wf` from MultisetOrder.lean.
instance : WellFoundedRelation TNode where
  rel := lt_TNode
  wf := InvImage.wf node_to_multiset (dmLT_wf Formula.WellFoundedLT)

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

theorem H_goes_down (α : Program) φ {Fs δ} (in_H : (Fs, δ) ∈ H α) {ψ} (in_Fs: ψ ∈ Fs) :
    lmOfFormula ψ < lmOfFormula (~⌈α⌉φ) := by
  cases α <;> simp [lmOfFormula]
  · simp_all [H]
  case sequence α β =>
    simp_all [H, testsOfProgram, List.attach_map_val]
    have IHα := H_goes_down α
    have IHβ := H_goes_down β
    sorry
  case union α β =>
    have IHα := H_goes_down α
    have IHβ := H_goes_down β
    sorry
  case star α =>
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
  simp [unfoldDiamond,Yset] at X_in
  rcases X_in with ⟨Fs, δ, in_H, def_X⟩
  subst def_X
  simp only [List.mem_union_iff, List.mem_singleton] at ψ_in_X
  cases ψ_in_X
  case inl ψ_in =>
    exact H_goes_down α φ in_H ψ_in
  · subst_eqs
    cases α <;> simp [lmOfFormula, Program.isAtomic] at *
    all_goals
      rw [List.attach_map_val]
      -- Need Lemma that tells us δ starts with something atomic.
      -- `unfoldDiamondContent`, analogous to `unfoldBoxContent`?
      sorry

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
    MultisetDMLT M N ↔ MultisetLT' M N := by
  unfold MultisetLT'
  constructor
  · intro M_LT_N
    cases M_LT_N
    aesop
  · intro M_LT'_N
    rcases M_LT'_N with ⟨X,Y,Z,claim⟩
    apply MultisetDMLT.DMLT X Y Z
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
    unfold_let Z
    have : node_to_multiset RES = node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond) + node_to_multiset (Lnew, Rnew, Onew) := by
      rw [node_to_multiset_of_precon preconP]
      subst def_RES
      simp
    rw [this]
    subst def_RES
    simp_all only [Option.instHasSubsetOption, add_tsub_cancel_right]
  split_ands
  · exact (LocalRule.cond_non_empty rule : node_to_multiset (Lcond, Rcond, Ocond) ≠ ∅)
  · rw [Z_eq]
    apply Multiset.sub_add_of_subset_eq
    -- This works but be cleaner with fewer non-terminal simp.
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
  | .(_), (@byLocalRule X B _lr next) => (B.attach.map (fun ⟨Y, h⟩ => endNodesOf (next Y h))).join
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
