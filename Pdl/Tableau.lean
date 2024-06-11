-- TABLEAU

import Mathlib.Data.List.ReduceOption

import Pdl.LocalTableau

open HasLength

-- PROJECTIONS

@[simp]
def formProjection : Nat → Formula → Option Formula
  | A, ⌈·B⌉φ => if A == B then some φ else none
  | _, _ => none

def projection : Nat → List Formula → List Formula
  | A, X => (X.map fun x => (formProjection A x)).reduceOption

@[simp]
theorem proj : g ∈ projection A X ↔ (⌈·A⌉g) ∈ X :=
  by
  induction X
  case nil =>
    simp only [projection, formProjection, beq_iff_eq, List.map_nil, List.not_mem_nil, iff_false]
    exact List.count_eq_zero.mp rfl
  case cons =>
    simp only [projection, formProjection, beq_iff_eq, List.map_cons, List.mem_cons]
    rw [List.reduceOption_mem_iff]
    aesop

/-! ## Loading and Loaded Histories -/

def boxesOf : Formula → List Program × Formula
| (Formula.box prog nextf) => let (rest,endf) := boxesOf nextf; ⟨prog::rest, endf⟩
| f => ([], f)

-- From ~⌈α⌉φ to ~'⌊α⌋χ with maximal loading
def toNegLoad (α : Program) (φ : Formula) : NegLoadFormula :=
  let (bs, f) := boxesOf φ
  match (bs.reverse, f) with -- reverse so we get bs.last for LoadFormula.load.
    | ([], f) => ~'⌊α⌋f
    | (b::bs, f) => ~'⌊α⌋(List.foldl (flip LoadFormula.box) (LoadFormula.load b f) bs)

-- NOTES about the History type:
-- - The newest/lowest TNode should be the head of the list.
-- - We only track "big" steps, hoping we do not need steps within local tableaux.

-- TNodes  before × since  last (M) application (and only recording loaded nodes)
def LoadHistory : Type := List TNode × List TNode -- This may not be enough!

def LoadHistory.nil : LoadHistory := ([], [])

@[simp]
def newLoadHistory : TNode → LoadHistory
| X => ([], [X])

@[simp]
def LoadHistory.addAtm : TNode → LoadHistory → LoadHistory
| X, (before, since) => (X :: since ++ before, [])

-- MB Condition 6, simplified to only represent closed tableau:
--
-- A node t repeating s can be treated as a closed end node if
-- the path from s to t is critical and loaded.
def condSixRepeat (X : TNode) (Hist : LoadHistory) :=
  Subtype (fun (k, Y) => Hist.1.get? k = some Y ∧ X.setEqTo Y)

/-! ## The PDL rules -/

/-- A rule to go from Γ to Δ. Note the four variants of the modal rule. -/
-- TODO: Think about whether the LoadHistory function works backwards!?
-- hfun converts the LoadHistory for Γ into that of Δ
inductive PdlRule : (Γ : TNode) → (Δ : TNode) → (hfun : LoadHistory → LoadHistory) → Type
  | mrkL : (~⌈α⌉φ) ∈ L → PdlRule (L, R, none)
                                 (L.erase (~⌈α⌉φ), R, some (Sum.inl (toNegLoad α φ)))
                                 (fun _ => newLoadHistory (L, R, none))
  | mrkR : (~⌈α⌉φ) ∈ R → PdlRule (L, R, none)
                                 (L, R.erase (~⌈α⌉φ), some (Sum.inr (toNegLoad α φ)))
                                 (fun _ => newLoadHistory (L, R, none))
  | atmL   {A X χ} : X = ⟨L, R, some (Sum.inl (~'⌊·A⌋(χ : LoadFormula)))⟩ → isBasic X → PdlRule X
                         ⟨projection A L, projection A R, some (Sum.inl (~'χ))⟩
                         (LoadHistory.addAtm X)
  | atmR   {A X χ} : X = ⟨L, R, some (Sum.inr (~'⌊·A⌋(χ : LoadFormula)))⟩ → isBasic X → PdlRule X
                         ⟨projection A L, projection A R, some (Sum.inr (~'χ))⟩
                         (LoadHistory.addAtm X)
  | atmL'  {A X φ} : X = ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩ → isBasic X → PdlRule X
                         ⟨(~φ) :: projection A L, projection A R, none⟩
                         (LoadHistory.addAtm X)
  | atmR'  {A X φ} : X = ⟨L, R, some (Sum.inr (~'⌊·A⌋(φ : Formula)))⟩ → isBasic X → PdlRule X
                         ⟨projection A L, (~φ) :: projection A R, none⟩
                         (LoadHistory.addAtm X)

-- ClosedTableau [parent, grandparent, ...] child
--
-- A closed tableau for X is either of:
-- - a local tableau for X followed by closed tableaux for all end nodes,
-- - a PDL rule application
-- - a successful loaded repeat (MB condition six)

inductive ClosedTableau : LoadHistory → TNode → Type
  -- FIXME: also record the "loc" step in `Hist`?
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf lt, ClosedTableau Hist Y) → ClosedTableau Hist X
  | pdl {Δ Γ} : PdlRule Γ Δ hfun → ClosedTableau (hfun Hist) Δ → ClosedTableau Hist Γ
  | rep {X Hist} (rep : condSixRepeat X Hist) : ClosedTableau Hist X

inductive provable : Formula → Prop
  | byTableauL {φ : Formula} : ClosedTableau ([],[]) ⟨[~φ], [], none⟩ → provable φ
  | byTableauR {φ : Formula} : ClosedTableau ([],[]) ⟨[], [~φ], none⟩ → provable φ

-- Definition 17, page 30
def inconsistent : TNode → Prop
  | LR => Nonempty (ClosedTableau .nil LR)

def consistent : TNode → Prop
  | LR => ¬inconsistent LR
