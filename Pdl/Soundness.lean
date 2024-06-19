-- SOUNDNESS

import Pdl.Star
import Pdl.Tableau

import Mathlib.Tactic.Ring

open Classical

open HasSat

/-- ## Tools for saying that different kinds of formulas are in a TNode -/

@[simp]
instance : Membership Formula TNode :=
  ⟨fun φ X => φ ∈ X.L ∨ φ ∈ X.R⟩

@[simp]
def NegLoadFormula_in_TNode := fun nlf (X : TNode) => X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

@[simp]
instance NegLoadFormula.HasMem_TNode : Membership NegLoadFormula TNode := ⟨NegLoadFormula_in_TNode⟩

def AnyFormula := Sum Formula LoadFormula

inductive AnyNegFormula
| neg : AnyFormula → AnyNegFormula

local notation "~''" φ:arg => AnyNegFormula.neg φ

@[simp]
instance modelCanSemImplyAnyNegFormula {W : Type} : vDash (KripkeModel W × W) AnyNegFormula :=
  vDash.mk (λ ⟨M,w⟩ af => match af with
   | ⟨Sum.inl f⟩ => evaluate M w f
   | ⟨Sum.inr f⟩ => evaluate M w (unload f)
   )

@[simp]
def anyNegLoad : Program → AnyFormula → NegLoadFormula
| α, Sum.inl φ => ~'⌊α⌋φ
| α, Sum.inr χ => ~'⌊α⌋χ

local notation "~'⌊" α "⌋" χ => anyNegLoad α χ

-- set_option trace.Meta.synthInstance true -- turn this on to debug ∈ below.
@[simp]
def AnyNegFormula_in_TNode := fun (anf : AnyNegFormula) (X : TNode) => match anf with
| ⟨Sum.inl φ⟩ => (~φ) ∈ X
| ⟨Sum.inr χ⟩ => NegLoadFormula_in_TNode (~'χ) X -- FIXME: ∈ not working here

@[simp]
instance : Membership AnyNegFormula TNode := ⟨AnyNegFormula_in_TNode⟩

/-- ## Helper functions, TODO: move to (Local)Tableau.lean -/

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

/-- ## Navigating through tableaux -/

-- To define ancestor / decendant relations inside tableaux we need to
-- represent both the whole Tableau and a specific node in it.
-- For this we use `PathInLocal` and `PathIn`.
-- They basically say "go to this child, then to this child, etc."
--
-- TODO: Do we need paths that go through/across multiple LocalTableau like
--       LHistories and unlike the Paths used in the Complteness Proof
--
-- TODO: Do we need paths that include back-loops?

-- TODO: Replace the "unsafe" list paths with inductive types
--       See the toy examples and experiments in "Repeat.lean".

inductive PathInLocal : ∀ {X}, LocalTableau X → Type
| byLocalRuleStep :
    (h : Y ∈ B)
    → PathInLocal (next Y h)
    → PathInLocal (LocalTableau.byLocalRule lrApp (next: ∀ Y ∈ B, LocalTableau Y))
| simEnd : PathInLocal (LocalTableau.sim _)

-- Three ways to make a path: empty, local step or pdl step.
-- The steps correspond to two out of three constructors of `ClosedTableau`.
inductive PathIn : ∀ {H X}, ClosedTableau H X → Type
| nil : PathIn _
| loc : (Y_in : Y ∈ endNodesOf lt) → (tail : PathIn (next Y Y_in)) → PathIn (ClosedTableau.loc lt next)
| pdl : (r : PdlRule Γ Δ hfun) → PathIn (child : ClosedTableau (hfun Hist) Δ) → PathIn (ClosedTableau.pdl r child)

def tabAt : PathIn tab → Σ H X, ClosedTableau H X
| PathIn.nil => ⟨_,_,tab⟩
| PathIn.loc _ tail => tabAt tail
| PathIn.pdl _ p_child => tabAt p_child

def nodeAt {H X} {tab : (ClosedTableau H X)} : PathIn tab → TNode
| PathIn.nil => X
| PathIn.loc _ tail => nodeAt tail
| PathIn.pdl _ p_child => nodeAt p_child

-- TODO: adjust notation and s-t or t-s convention to notes!

/-- The parent-child relation `s ◃ t` in a tableau -/
def stepRel {H X} {ctX : ClosedTableau H X} : PathIn ctX → PathIn ctX → Prop
| s, t => sorry -- TODO
  -- (∃ Y_in, s = PathIn.loc Y_in t) -- does not make sense, both paths are from the same root!

notation pa:arg "◃" pb:arg => stepRel pa pb

/-- Successor relation plus back loops: ◃' (MB: page 26) -/
def edgesBack {H X} {ctX : ClosedTableau H X} : PathIn ctX → PathIn ctX → Prop
| t, s => sorry -- TODO

notation pa:arg "◃'" pb:arg => edgesBack pa pb

/-- ReflTrans closure of ◃ is denoted by ≤' -/
notation pa:arg "≤'" pb:arg => Relation.ReflTransGen stepRel pa pb

-- NOTE: for free nodes we have < iff <'

-- TODO: def companionOf : ...

def K {H X} {ctX : ClosedTableau H X} : PathIn ctX → PathIn ctX → Prop
| t, s => sorry -- TODO: t is successful leaf and s is the companion of s

def E {H X} {ctX : ClosedTableau H X} : PathIn ctX → PathIn ctX → Prop
| t, s => (t ◃ s) ∨ K t s

theorem loadedDiamondPaths
  {Root Δ : TNode}
  (tab : ClosedTableau ([],[]) Root) -- ensure History = [] here to prevent repeats from "above".
  (path_to_Δ : PathIn tab)
  (h : Δ = nodeAt path_to_Δ)
  {M : KripkeModel W} {v : W}
  (φ : AnyFormula)
  (negLoad_in : NegLoadFormula_in_TNode (~'⌊α⌋φ) Δ) -- FIXME: ∈ not working here?
  (v_X : (M,v) ⊨ Δ)
  (v_α_w : relate M α v w)
  (w_φ : (M,w) ⊨ ~''φ)
  : ∃ Γ : TNode,
    ∃ path_to_Γ : PathIn tab,
        Γ = nodeAt path_to_Γ
      -- TODO: must be an extension of path_to_Δ
      ∧ (AnyNegFormula_in_TNode (~''φ) Γ) -- FIXME: ∈ not working here?
      ∧ (M,w) ⊨ Γ :=
  by
  let ⟨L,R,O⟩ := Δ
  all_goals sorry


theorem tableauThenNotSat : ∀ X, ClosedTableau LoadHistory.nil X → ¬satisfiable X :=
  by
  intro X t
  sorry


theorem correctness : ∀LR : TNode, satisfiable LR → consistent LR :=
  by
    intro LR
    contrapose
    unfold consistent
    unfold inconsistent
    simp only [not_nonempty_iff, not_isEmpty_iff, not_exists, not_forall, exists_prop, Nonempty.forall]
    intro hyp
    apply tableauThenNotSat LR hyp

theorem soundTableau : ∀φ, provable φ → ¬satisfiable ({~φ} : Finset Formula) :=
  by
    intro φ prov
    rcases prov with ⟨tabl⟩|⟨tabl⟩
    exact tableauThenNotSat ([~φ], [], none) tabl
    exact tableauThenNotSat ([], [~φ], none) tabl

theorem soundness : ∀φ, provable φ → tautology φ :=
  by
    intro φ prov
    apply notsatisfnotThenTaut
    rw [← singletonSat_iff_sat]
    apply soundTableau
    exact prov
