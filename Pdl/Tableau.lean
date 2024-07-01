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

/-- A pair of lists of TNodes: since × before last (M) application, only recording loaded nodes.
This only tracks "big" steps,  hoping we do not need steps within a local tableau.
The head of the first list is the newest TNode. -/
structure LoadHistory : Type := (since : List TNode) (before : List TNode) -- This may not be enough!

def LoadHistory.nil : LoadHistory := ⟨[], []⟩

@[simp]
def newLoadHistory : TNode → LoadHistory
| X => ⟨[], [X]⟩

@[simp]
def LoadHistory.add : TNode → LoadHistory → LoadHistory
| X, ⟨since, before⟩ => ⟨X :: since, before⟩

@[simp]
def LoadHistory.addAtm : TNode → LoadHistory → LoadHistory
| X, ⟨since, before⟩ => ⟨[], X :: since ++ before⟩

/-- A repeat with a loaded path to its companion (MB condition 6) -/
def LoadedPathRepeat (X : TNode) (Hist : LoadHistory) : Type :=
  Subtype (fun (k, Y) => Hist.before.get? k = some Y ∧ X.setEqTo Y)

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
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf lt, ClosedTableau (Hist.add X) Y) → ClosedTableau Hist X
  | pdl {Δ Γ} : PdlRule Γ Δ hfun → ClosedTableau (hfun Hist) Δ → ClosedTableau Hist Γ
  | rep {X Hist} (lpr : LoadedPathRepeat X Hist) : ClosedTableau Hist X

inductive provable : Formula → Prop
  | byTableauL {φ : Formula} : ClosedTableau ⟨[],[]⟩ ⟨[~φ], [], none⟩ → provable φ
  | byTableauR {φ : Formula} : ClosedTableau ⟨[],[]⟩ ⟨[], [~φ], none⟩ → provable φ

/-- A TNode is inconsistent if there exists a closed tableau for it. -/
def inconsistent : TNode → Prop
  | LR => Nonempty (ClosedTableau .nil LR)

/-- A TNode is consistent iff it is not inconsistent. -/
def consistent : TNode → Prop
  | LR => ¬inconsistent LR
