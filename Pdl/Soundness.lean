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

inductive PathIn {H X} : ClosedTableau H X → Type
-- TODO  this would now have 8 cases, maybe first refactor `ClosedTableau`?

/-- The parent-child relation ◃ in a tableau -/
def stepRel {H X} {ctX : ClosedTableau H X} : PathIn ctX → PathIn ctX → Prop
| t, s => sorry -- TODO

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

-- Given:
-- - a local tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the TNode at the end of the path or a local end node and the remaining path
-- TOOD: rewrite with more match cases in term mode without "by"?
def nodeInLocalAt (ltX : LocalTableau X) : List TNode → Option (TNode ⊕ (Subtype (fun Y => Y ∈ endNodesOf ltX) × List TNode))
| [] => some (Sum.inl X) -- we have reached the destination
| (Y::rest) => by
    cases ltX
    case byLocalRule B lnext lrApp =>
      refine if Y_in : Y ∈ B then ?_ else ?_
      · cases nodeInLocalAt (lnext Y Y_in) rest -- make a recursive call!
        case none => exact none -- not found.
        case some foo =>
          cases foo
          case inl Z =>
            exact some (Sum.inl Z) -- found it!
          case inr Z_ =>
            rcases Z_ with ⟨⟨Z,Z_in⟩, remainder⟩
            apply some
            apply Sum.inr
            refine ⟨⟨Z, ?_⟩, ?_⟩
            · apply endNodeOfChild_to_endNode lrApp lnext rfl Y_in Z_in
            · exact remainder
      · exact none -- cannot follow path
    case sim X_simp =>
      apply some
      apply Sum.inr
      constructor
      · use X
        rw [endNodesOf, List.mem_singleton]
      · exact Y::rest -- Problem: This case means "reminder" may be of same length still.

-- Given:
-- - a tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the TNode at the end of the path
def nodeInAt : (Σ X HistX, ClosedTableau HistX X) → List TNode → Option TNode
| ⟨X, hX, tab⟩, [] => some X -- we have reached the destination
| ⟨X, hX, tab⟩, (Y::rest) => by
      cases tab
      case loc ltX next =>
        cases nodeInLocalAt ltX (Y::rest)
        case none => exact none
        case some lt_res =>
          cases lt_res
          case inl Z => exact some Z -- reached end of path inside the local tableau.
          case inr Y_end_remainder =>
            rcases Y_end_remainder with ⟨⟨Y, Y_in⟩, remainder⟩
            have : remainder.length < (Y::rest).length := sorry -- needed for termination, may need to add this in tabInLocalAt
            exact nodeInAt ⟨Y, hX, next Y Y_in⟩ remainder
      case mrkL =>
        -- apply nodeInAt ?
        sorry
      case rep isRep =>
        exact none -- fail, we cannot go to Y (and should be using Loopy from below!)
      all_goals sorry
termination_by
   Xhtab toWalk => toWalk.length

-- Given:
-- - a local tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the local tableau at the end of the path or a local end node and the remaining path
-- TOOD: rewrite with more match cases in term mode without "by"?
def tabInLocalAt (ltX : LocalTableau X) : List TNode → Option ((Σ Z, LocalTableau Z) ⊕ (Subtype (fun Y => Y ∈ endNodesOf ltX) × List TNode))
| [] => some (Sum.inl ⟨X, ltX⟩) -- we have reached the destination
| (Y::rest) => by
    cases ltX
    case byLocalRule B lnext lrApp =>
      refine if Y_in : Y ∈ B then ?_ else ?_
      · cases tabInLocalAt (lnext Y Y_in) rest -- make a recursive call!
        case none => exact none -- not found.
        case some foo =>
          cases foo
          case inl Z =>
            exact some (Sum.inl Z) -- found it!
          case inr Z_ =>
            rcases Z_ with ⟨⟨Z,Z_in⟩, remainder⟩
            apply some
            apply Sum.inr
            refine ⟨⟨Z, ?_⟩, ?_⟩
            · apply endNodeOfChild_to_endNode lrApp lnext rfl Y_in Z_in
            · exact remainder
      · exact none -- cannot follow path
    case sim X_simp =>
      apply some
      apply Sum.inr
      constructor
      · use X
        rw [endNodesOf, List.mem_singleton]
      · exact Y::rest -- Problem: This case means "reminder" may be of same length still.

-- Given:
-- - a tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the closed tableau at the end of the path
def tabInAt : (Σ X HistX, ClosedTableau HistX X) → List TNode → Option (Σ Y HistY, ClosedTableau HistY Y)
| ⟨X, hX, tab⟩, [] => some ⟨X, hX, tab⟩ -- we have reached the destination
| ⟨X, hX, tab⟩, (Y::rest) => by
      cases tab
      case loc ltX next =>
        cases tabInLocalAt ltX (Y::rest)
        case none => exact none
        case some lt_res =>
          cases lt_res
          case inl Z_ltZ =>
            -- reached end of path inside the local tableau.
            rcases Z_ltZ with ⟨Z, ltZ⟩
            let ctZnext : (W : TNode) → W ∈ endNodesOf ltZ → ClosedTableau hX W :=
              fun W W_in => next _ sorry -- Need: endNnodesOf ltZ ⊆ endNnodesOf ltX
            let ctZ : ClosedTableau _ Z := ClosedTableau.loc ltZ ctZnext
            exact some ⟨Z, _, ctZ⟩
          case inr Y_end_remainder =>
            rcases Y_end_remainder with ⟨⟨Y, Y_in⟩, remainder⟩
            have : remainder.length < (Y::rest).length := sorry -- needed for termination, may need to add this in tabInLocalAt
            exact tabInAt ⟨Y, hX, next Y Y_in⟩ remainder
      case mrkL =>
        -- apply tabInAt ?
        sorry
      case rep isRep =>
        exact none -- fail, we cannot go to Y (and should be using Loopy from below!)
      all_goals sorry
termination_by
   Xhtab toWalk => toWalk.length

-- Go one step, to Y, but possibly via a loop
-- Given:
-- - the root of a tableau
-- - a path already walked - needed to go back up to companion
-- - a path still to be walked
-- return: the tableau at the end of the path, possibly by looping via condition 6 repeats
--
-- IDEA: instead of using "tabInAt", add the Closed (or Local?!) tableau at "done" as another input?
def goTo : (Σ R, ClosedTableau ([],[]) R) → List TNode → TNode → Option (Σ Y HistY, ClosedTableau HistY Y)
| ⟨R, tab⟩, done, Y => by
      cases tab_def : tabInAt ⟨R, ([],[]), tab⟩ done
      case none =>
        exact none -- this should never happen :-(
      case some X_ =>
        rcases X_ with ⟨X, HistX, ctX⟩
        cases ctX
        case loc ltX next =>
          cases ltX
          case byLocalRule B lnext lrApp =>
            refine if Y_in : Y ∈ B then ?_ else ?_
            -- move down a real step:
            · let ltY := lnext Y Y_in
              -- now need to turn ltY into a closed tableau. or change the return type?
              let ctYnext : (Z : TNode) → Z ∈ endNodesOf ltY → ClosedTableau HistX Z :=
                fun Z Z_in => next _ (endNodeOfChild_to_endNode lrApp lnext rfl Y_in Z_in)
              let ctY : ClosedTableau _ Y := ClosedTableau.loc ltY ctYnext
              exact some ⟨Y, _, ctY⟩
            -- not found:
            · exact none
          case sim X_simp =>
            have ctXnew := next X (by simp)
            simp [endNodesOf, List.mem_singleton] at ctXnew
            -- Now check that Y is among the successors given by non-local rules?
            -- Or could we make a recursive call here?
            -- Instead of `tabInAt ⟨R, ([],[]), tab⟩ done` above, now we want to consider ctXnew ?!
            cases ctXnew
            all_goals sorry
        case mrkL =>
          -- apply tabInAt ?
          sorry
        case rep theRep =>
          simp only [condSixRepeat, List.any_eq_true] at theRep
          rcases theRep with ⟨⟨k,Y⟩, getk, X_is_Y⟩ -- is k the index now? start with 0 or 1?
          let (bef, aft) := HistX
          -- now go back to the companion (and thus allow the path to be longer than the actual tableau)
          let pathToCompanion : List TNode := done.drop (k+1) -- undo the steps since companion
          have : pathToCompanion.length + 1 < done.length := by -- no more "rest" here as we only do one step
            zify
            -- ring -- why not working?
            sorry
          exact (tabInAt ⟨R, ([],[]), tab⟩ pathToCompanion)
        all_goals sorry

-- MB: Lemma 7
theorem loadedDiamondPaths
  {Root Δ : TNode}
  (tab : ClosedTableau ([],[]) Root) -- ensure History = [] here to prevent repeats from "above".
  (path_to_Δ : List TNode)
  (h : some tabΔ = tabInAt ⟨Root,_,tab⟩ path_to_Δ)
  {M : KripkeModel W} {v : W}
  (φ : AnyFormula)
  (negLoad_in : NegLoadFormula_in_TNode (~'⌊α⌋φ) Δ) -- FIXME: ∈ not working here?
  (v_X : (M,v) ⊨ Δ)
  (v_α_w : relate M α v w)
  (w_φ : (M,w) ⊨ ~''φ)
  : ∃ path_Δ_to_Γ : List TNode,
    ∃ Γ ∈ tabInAt ⟨Root,_,tab⟩ (path_to_Δ ++ path_Δ_to_Γ),
    (AnyNegFormula_in_TNode (~''φ) Γ.1) -- FIXME: ∈ not working here?
    ∧
    (M,w) ⊨ Γ.1 :=
  by
  let ⟨L,R,O⟩ := Δ
  let ⟨ΔNode, ΔHist, ΔTab⟩ := tabΔ
  -- cases tab -- No, we want to distinguish by cases what is happening at Δ
  cases ΔTab
  case mrkL =>
    -- it should be impossible to apply (M+)
    -- because we already have a loaded formula in Δ
    simp at negLoad_in
    cases negLoad_in
    case inl hyp => subst hyp; sorry
    all_goals sorry

  all_goals sorry

-- MB: Lemma 8
-- theorem freeSatDown : Prop := sorry
-- have := localRuleTruth
-- have := loadedDiamondPaths


theorem tableauThenNotSat : ∀ X, ClosedTableau LoadHistory.nil X → ¬satisfiable X :=
  by
  intro X t
  sorry

-- Theorem 2, page 30
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
