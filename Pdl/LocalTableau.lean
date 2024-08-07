-- LOCAL TABLEAU

import Pdl.UnfoldBox
import Pdl.UnfoldDia
import Pdl.MultisetOrder

open HasLength

/-! ## Tableau Nodes -/

-- A tableau node has two lists of formulas and one or no negated loaded formula.
-- TODO: rename `TNode` to `Sequent`
-- TODO: turn this into "abbrev" to avoid silly instance below.
def TNode := List Formula × List Formula × Option (Sum NegLoadFormula NegLoadFormula) -- ⟨L, R, o⟩
  deriving DecidableEq, Repr

-- Some thoughts about the TNode type:
-- - one formula may be loaded
-- - loading is not changed in local tableaux, but must be tracked through it.
-- - each (loaded) formula can be on the left/right/both
-- - we also need to track loading and the side "through" dagger tableau.

/-- We do not care about the order of the lists.
TNodes should be considered equal when their Finset versions are equal.
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
def TNode.O : TNode → Option (Sum NegLoadFormula NegLoadFormula) := λ⟨_,_,O⟩ => O

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
instance modelCanSemImplyLLO : vDash (KripkeModel W × W) (List Formula × List Formula × Option (Sum NegLoadFormula NegLoadFormula)) :=
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

def NegLoadFormula_in_TNode (nlf : NegLoadFormula) (X : TNode) : Prop :=
  X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

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
  | box (α φ) : OneSidedLocalRule [ ⌈α⌉φ] (unfoldBox     α φ)
  | dia (α φ) : OneSidedLocalRule [~⌈α⌉φ] (unfoldDiamond α φ)

theorem oneSidedLocalRuleTruth (lr : OneSidedLocalRule X B) : Con X ≡ discon B :=
  by
  intro W M w
  cases lr
  all_goals try (simp; done) -- takes care of all propositional rules
  case box α φ =>
    rw [conEval]
    simp only [List.mem_singleton, forall_eq]
    rw [localBoxTruth α φ W M w]
    simp only [disEval, List.mem_map, exists_exists_and_eq_and, unfoldBox, disconEval]
    constructor
    · rintro ⟨l,hyp⟩; use l; rw [conEval] at hyp; tauto
    · rintro ⟨l,hyp⟩; use l; rw [conEval]; tauto
  case dia α φ =>
    rw [conEval]
    simp only [List.mem_singleton, forall_eq, discon, unfoldDiamond]
    rw [localDiamondTruth α φ W M w, disEval, disconEval]
    apply mapCon_mapForall

-- LOADED rule applications
-- Only the local diamond rule may be applied to loaded formulas.
-- (In MB page 19 these were only the rules ¬u, ¬; ¬* and ¬?).
-- Each rule replaces the loaded formula by:
-- - up to one loaded formula,
-- - and a set of normal formulas.
-- It's annoying to need the rule twice here due to the definition of LoadFormula.
inductive LoadRule : NegLoadFormula → List (List Formula × Option NegLoadFormula) → Type
  | dia  {α χ}   : LoadRule (~'⌊α  ⌋(χ : LoadFormula)) (unfoldDiamondLoaded α χ)
    -- ([ (∅, some (~'χ)) ] ++ loadDagEndNodes (∅, (Sum.inr (NegDagLoadFormula.neg (injectLoad α χ)))))
  | dia' {α φ}   : LoadRule (~'⌊α  ⌋(φ : Formula    )) (unfoldDiamondLoaded' α φ)
    -- ([ ([~φ], none) ] ++ loadDagEndNodes (∅, (Sum.inr (NegDagLoadFormula.neg (injectLoad' α φ)))))

theorem loadRuleTruth (lr : LoadRule (~'χ) B) :
    (~(unload χ)) ≡ dis (B.map (λ (fs, o) => Con (fs ++ (o.map negUnload).toList))) :=
  by
  intro W M w
  cases lr
  case dia =>
    sorry
  case dia' =>
    sorry

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
def applyLocalRule (_ : LocalRule (Lcond, Rcond, Ocond) ress) : TNode → List TNode
  | ⟨L, R, O⟩ => ress.map $ λ (Lnew, Rnew, Onew) => match Onew with
      | none                 => (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, O)
      | some (Sum.inl (~'χ)) => (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, some (Sum.inl (~'χ)))
      | some (Sum.inr (~'χ)) => (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, some (Sum.inr (~'χ)))

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

inductive LocalRuleApp : TNode → List TNode → Type
  | mk {L R : List Formula}
       {C : List TNode}
       {ress : List TNode}
       {O : Option (Sum NegLoadFormula NegLoadFormula)}
       (Lcond Rcond : List Formula)
       (Ocond : Option (Sum NegLoadFormula NegLoadFormula))
       (rule : LocalRule (Lcond, Rcond, Ocond) ress)
       {hC : C = applyLocalRule rule (L,R,O)}
       (preconditionProof : List.Sublist Lcond L ∧ List.Sublist Rcond R ∧ Ocond ⊆ O)
       : LocalRuleApp (L,R,O) C

theorem localRuleTruth
    {L R : List Formula}
    {C : List TNode}
    {O : Option (Sum NegLoadFormula NegLoadFormula)}
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
        exact Or.inl $ Or.inl $ List.Sublist.subset preconditionProof f_in
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
        exact Or.inl $ Or.inr $ List.Sublist.subset preconditionProof f_in
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
      · use (L ++ X, R, some (Sum.inl (~'χ)))
        constructor
        · use X, none; simp only [Option.map_none', and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L ++ X, R, some (Sum.inl val))
        constructor
        · use X, some val; simp only [Option.map_some', and_true]; exact in_ress
        · intro g g_in; subst def_f; rw [conEval] at w_f
          simp only [List.mem_union_iff, List.mem_append, List.mem_singleton] at g_in
          rcases g_in with ((g_in|g_in)|g_in)|g_in
          all_goals aesop
    · rintro ⟨Ci, ⟨⟨X, O, ⟨in_ress, def_Ci⟩⟩, w_Ci⟩⟩
      intro f f_in
      subst def_Ci
      cases O
      all_goals simp at *
      · have := w_Ci f
        aesop
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use Con (X ++ Option.toList (Option.map negUnload (some val)))
          constructor
          · use X, some val
          · rw [conEval]
            simp only [Option.map_some', negUnload, Option.toList_some, List.mem_append, List.mem_singleton]
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
      · use (L, R ++ X, some (Sum.inr (~'χ)))
        constructor
        · use X, none; simp only [Option.map_none', and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L, R ++ X, some (Sum.inr val))
        constructor
        · use X, some val; simp only [Option.map_some', and_true]; exact in_ress
        · intro g g_in; subst def_f; rw [conEval] at w_f
          simp only [List.mem_union_iff, List.mem_append, List.mem_singleton] at g_in
          rcases g_in with (g_in|(g_in|g_in))|g_in
          all_goals aesop
    · rintro ⟨Ci, ⟨⟨X, O, ⟨in_ress, def_Ci⟩⟩, w_Ci⟩⟩
      intro f f_in
      subst def_Ci
      cases O
      all_goals simp at *
      · have := w_Ci f
        aesop
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use Con (X ++ Option.toList (Option.map negUnload (some val)))
          constructor
          · use X, some val
          · rw [conEval]
            simp only [Option.map_some', negUnload, Option.toList_some, List.mem_append, List.mem_singleton]
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

open LocalTableau

-- Use this plus D-M to show termination on LocalTableau. Overkill?
mutual
@[simp]
def lmOfFormula : Formula → Nat
| ⊥ => 0
| ·_ => 0
| ~φ => 1 + lmOfFormula (φ)
| φ⋀ψ => 1 + lmOfFormula φ + lmOfFormula ψ
| ⌈α⌉ φ => lmOfProgram α + lmOfFormula φ
@[simp]
def lmOfProgram : Program → Nat
| ·_  => 0 -- No more local steps!
| ?'φt  => 1 + lmOfFormula (~φt)
| α;'β  => 1 + lmOfProgram (α) + lmOfProgram (β)
| α⋓β  => 1 + lmOfProgram (α) + lmOfProgram (β)
| ∗α  => 1 + lmOfProgram (α) -- DagTab does all α steps, but may stop at other formulas ?????
end

/-
-- original, closer to actual rules:
| ~⊥ => 0
| ~·_ => 0
| ~~φ => 1 + lmOfFormula φ
| ~φ⋀ψ => 1 + lmOfFormula (~φ) + lmOfFormula (~ψ)
| ~⌈·_⌉ _ => 0 -- No more local steps
| ~⌈?'φt⌉ φ => 1 + lmOfFormula (~φt) + lmOfFormula (~φ)
| ~⌈α;'β⌉ φ => 1 + lmOfFormula (~⌈α⌉φ) + lmOfFormula (~⌈β⌉φ)
| ~⌈α⋓β⌉ φ => 1 + lmOfFormula (~⌈α⌉φ) + lmOfFormula (~⌈β⌉φ) -- max
| ~⌈∗α⌉ φ => 1 + lmOfFormula (~φ) -- because DagTab does all α steps
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

def node_to_multiset : TNode → Multiset Formula
| (L, R, none) => (L + R)
| (L, R, some (Sum.inl (~'χ))) => (L + R + [~ unload χ])
| (L, R, some (Sum.inr (~'χ))) => (L + R + [~ unload χ])

def preconP_to_submultiset (preconditionProof : List.Sublist Lcond L ∧ List.Sublist Rcond R ∧ Ocond ⊆ O) :
    node_to_multiset (Lcond, Rcond, Ocond) ≤ node_to_multiset (L, R, O) :=
  by
  cases Ocond <;> cases O
  all_goals (try (rename_i f g; cases f; cases g))
  all_goals (try (rename_i f; cases f))
  all_goals
    simp [node_to_multiset] at * -- FIXME avoid non-terminal simp here!
  case none.none =>
    exact (List.Sublist.append preconditionProof.1 preconditionProof.2).subperm
  case none.some.inl =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Sublist.count_le (List.Sublist.append preconditionProof.1 preconditionProof.2) f
    simp_all
    linarith
  case none.some.inr =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Sublist.count_le (List.Sublist.append preconditionProof.1 preconditionProof.2) f
    simp_all
    linarith
  case some.some.inl.inl.neg =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Sublist.count_le (List.Sublist.append preconditionProof.1 preconditionProof.2.1) f
    simp_all
  case some.some.inr.neg a =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Sublist.count_le (List.Sublist.append preconditionProof.1 preconditionProof.2.1) f
    cases g <;> (rename_i nlform; cases nlform; simp_all)

@[simp]
def lt_TNode (X : TNode) (Y : TNode) := MultisetLT (node_to_multiset X) (node_to_multiset Y)

-- Needed for termination of endNOdesOf.
-- Here we use `dm_wf` from MultisetOrder.lean.
instance : WellFoundedRelation TNode where
  rel := lt_TNode
  wf := InvImage.wf node_to_multiset (dm_wf Formula.WellFoundedLT)

theorem LocalRule.cond_non_empty (rule : LocalRule (Lcond, Rcond, Ocond) X) :
    node_to_multiset (Lcond, Rcond, Ocond) ≠ ∅ :=
  by
  cases rule
  all_goals simp [node_to_multiset]
  case oneSidedL _ orule => cases orule <;> simp
  case oneSidedR _ orule => cases orule <;> simp

theorem Multiset.sub_add_of_subset_eq [DecidableEq α] {M : Multiset α} (h : X ≤ M):
    M = M - X + X := (tsub_add_cancel_of_le h).symm

-- TODO: move this to `Unfold.lean`? (after moving lmOf to Measures?)
theorem unfoldBox.decreases_lmOf {α : Program} {φ : Formula} {E : List Formula}
    (E_in : E ∈ unfoldBox α φ)
    (y_in_E : y ∈ E)
    : lmOfFormula y < lmOfProgram α + lmOfFormula φ :=
  by
  -- OLD NOTE:
  -- Is this even true? Why is there no ∗α in the claim? Is the diamond case easier?
  -- Try induction loading and a claim about boxDagNext and intermediate (dagger) formulas?
  cases y
  case box β φ =>
    cases β
    case star β =>
      simp
      -- OLD NOTE: y_in_E is *not* impossible now, dagEndNodes may contain top-level stars (e.g. via tests).
      sorry
    all_goals sorry
  all_goals sorry

-- TODO: move this to Unfold? (after moving lmOf to Measures?)
theorem unfoldDiamond.decreases_lmOf {α : Program} {φ : Formula} {E : List Formula}
    (E_in : E ∈ unfoldDiamond α φ)
    (y_in_E : y ∈ E)
    : lmOfFormula y < 1 + lmOfProgram α + lmOfFormula φ :=
  by
  -- Note: the "1+" comes from the diamond/negation.
  sorry

-- TODO: also need loadDagEndNodes.decreases_lmOf or similar?

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
      case nCo => cases Y_in_ress <;> (subst_eqs; simp at * ; subst_eqs ; simp at *); linarith
      case dia α φ =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        rw [← add_assoc]
        exact unfoldDiamond.decreases_lmOf E_in y_in_Y
      case box α φ =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldBox.decreases_lmOf E_in y_in_Y

    case oneSidedR orule =>
      cases orule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case neg.refl => linarith
      case con.refl => cases y_in_Y <;> (subst_eqs; linarith)
      case nCo => cases Y_in_ress <;> (subst_eqs; simp at * ; subst_eqs ; simp at *); linarith
      case dia α φ =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        rw [← add_assoc]
        exact unfoldDiamond.decreases_lmOf E_in y_in_Y
      case box α φ =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldBox.decreases_lmOf E_in y_in_Y

    case loadedL lrule =>
      simp [node_to_multiset]
      cases lrule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case dia α χ =>
        -- need: lmOfFormula goes down in unfoldDiamondLoad
        sorry
      case dia' α φ =>
        -- need: lmOfFormula goes down in unfoldDiamondLoad'
        sorry

    case loadedR lrule =>
      simp [node_to_multiset]
      cases lrule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case dia α χ =>
        -- need: lmOfFormula goes down in unfoldDiamondLoad
        sorry
      case dia' α φ =>
        -- need: lmOfFormula goes down in unfoldDiamondLoad'
        sorry

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
theorem MultisetLT.iff_MultisetLT' [DecidableEq α] [Preorder α] {M N : Multiset α} :
    MultisetLT M N ↔ MultisetLT' M N := by
  unfold MultisetLT'
  constructor
  · intro M_LT_N
    cases M_LT_N
    aesop
  · intro M_LT'_N
    rcases M_LT'_N with ⟨X,Y,Z,claim⟩
    apply MultisetLT.MLT X Y Z
    all_goals tauto

theorem localRuleApp.decreases_DM {X : TNode} {B : List TNode}
    (lrA : LocalRuleApp X B) : ∀ Y ∈ B, lt_TNode Y X :=
  by
  rcases lrA with ⟨Lcond,Rcond,Ocond,rule,preconP⟩
  rename_i L R ress O B_def
  subst B_def
  intro RES RES_in
  simp [applyLocalRule] at RES_in
  rcases RES_in with ⟨⟨Lnew,Rnew,Onew⟩, Y_in_ress, claim⟩
  unfold lt_TNode
  simp at claim
  rw [MultisetLT.iff_MultisetLT']
  unfold MultisetLT'
  use node_to_multiset (Lnew, Rnew, Onew) -- choose X to be the newly added formulas
  use node_to_multiset (Lcond, Rcond, Ocond) -- choose Y to be the removed formulas
  -- Now choose a way to define Z:
  -- let Z:= use node_to_multiset RES - node_to_multiset (Lnew, Rnew, Onew) -- way 1
  let Z := node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond) -- way 2
  use Z
  -- claim that the other definition would have been the same:
  have Z_eq : Z = node_to_multiset RES - node_to_multiset (Lnew, Rnew, Onew) := by
    -- maybe similar to the proof of preconP_to_submultiset?
    sorry
  split_ands
  · exact (LocalRule.cond_non_empty rule : node_to_multiset (Lcond, Rcond, Ocond) ≠ ∅)
  · rw [Z_eq]
    apply Multiset.sub_add_of_subset_eq
    cases Onew
    -- TODO: clean this up once it works
    all_goals try (rename_i f; cases f)
    all_goals simp_all
    all_goals cases O
    all_goals try (rename_i cond; cases cond)
    all_goals cases Ocond
    all_goals try (rename_i cond; cases cond)
    all_goals try simp_all
    all_goals subst claim
    all_goals
      simp [node_to_multiset]
      try apply List.Sublist.subperm
      try simp_all
      sorry
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
