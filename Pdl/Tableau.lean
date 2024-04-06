-- TABLEAU

import Mathlib.Data.List.ReduceOption

import Pdl.LocalTableau

open HasLength

-- PROJECTIONS

@[simp]
def formProjection : Char → Formula → Option Formula
  | A, ⌈·B⌉φ => if A == B then some φ else none
  | _, _ => none

def projection : Char → List Formula → List Formula
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

-- LOADING

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

-- TNodes  before × since  last (At) application (and only recording loaded nodes)
def LoadHistory : Type := List TNode × List TNode -- This may not be enough!

def LoadHistory.nil : LoadHistory := ([], [])

-- MB Condition 6, simplified to only represent closed tableau:
--
-- A node t repeating s can be treated as a closed end node if
-- the path from s to t is critical and loaded.
def condSixRepeat (X : TNode) (Hist : LoadHistory) :=
  Subtype (fun (k, Y) => Hist.1.get? k = some Y ∧ X.setEqTo Y)

-- TABLEAUX

-- The "Step" notation has two jobs:
-- - flip the order in the definition below to be more natural.
-- - avoid having to repeat "parent" to build the history.

-- Step to an unloaded node, resetting history.
notation "Step" Ct:arg Hist:arg parent:arg child:arg => Ct ([],[]) child → Ct Hist parent

-- Lstep to a loaded node, contnuing the history.
notation "LStep" Ct:arg Hist:arg recf:arg parent:arg child:arg => Ct (recf Hist parent) child → Ct Hist parent

def record : LoadHistory → TNode → LoadHistory
| (before, after), X => if X.isLoaded then (before, X :: after) else ([], [])

-- Use this for atmL and atmR, but not for the primed ones!
def recordAtm : LoadHistory → TNode → LoadHistory
| (before, after), X => (after ++ before, [X])

/-
inductive PdlRule : TNode → TNode → Type
  | mrkL : (~⌈α⌉φ) ∈ L → PdlRule (L, R, none)
                                 (L.erase (~⌈α⌉φ), R, some (Sum.inl (toNegLoad α φ)))
  | mrkR : (~⌈α⌉φ) ∈ R → PdlRule (L, R, none)
                                 (L, R.erase (~⌈α⌉φ), some (Sum.inr (toNegLoad α φ)))
  -- The (At) rule:
  | atmL   {A X χ} : isSimpleNode X → PdLRule ⟨L, R, some (Sum.inl (~'⌊·A⌋(χ : LoadFormula)))⟩
                                              (projection A L, projection A R, some (Sum.inl (~'χ)))
  | atmR   {A X χ} : isSimpleNode X → PdlRule ⟨L, R, some (Sum.inr (~'⌊·A⌋(χ : LoadFormula)))⟩
                                              (projection A L, projection A R, some (Sum.inr (~'χ)))
  | atmL'  {A X φ} : isSimpleNode X → PdlRule ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                              (projection A L ++ [~φ], projection A R, none)
  | atmR'  {A X φ} : isSimpleNode X → PdlRule ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                              (projection A L, projection A R ++ [~φ], none)
-/

-- ClosedTableau [parent, grandparent, ...] child
--
--
-- (MB: Definition 16, page 29)
-- A closed tableau for X is either of:
-- - a local tableau for X followed by tableaux for all end nodes,
-- - a (M+) loading rule application
--   (left or right)
-- - a (At) modal rule application (two cases due to LoadFormula type)
--   (left or right, and loaded or unloaded)
-- - a good repeat (MB condition six)
inductive ClosedTableau : LoadHistory → TNode → Type
  -- Do a local tableau: (not recording any history!)
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf lt, ClosedTableau Hist Y) → ClosedTableau Hist X
  -- The (M+) rule:
  | mrkL : (~⌈α⌉φ) ∈ L → Step ClosedTableau Hist (L, R, none)
                                                 (L.erase (~⌈α⌉φ), R, some (Sum.inl (toNegLoad α φ)))
  | mrkR : (~⌈α⌉φ) ∈ R → Step ClosedTableau Hist (L, R, none)
                                                 (L, R.erase (~⌈α⌉φ), some (Sum.inr (toNegLoad α φ)))
  -- The (At) rule:
  -- TODO: can we avoid the four cases?
  | atmL   {A X χ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inl (~'⌊·A⌋(χ : LoadFormula)))⟩
                                                              (projection A L, projection A R, some (Sum.inl (~'χ)))
  | atmL'  {A X φ} : isSimpleNode X → LStep ClosedTableau Hist record ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                                              (projection A L ++ [~φ], projection A R, none)
  | atmR   {A X χ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inr (~'⌊·A⌋(χ : LoadFormula)))⟩
                                                              (projection A L, projection A R, some (Sum.inr (~'χ)))
  | atmR'  {A X φ} : isSimpleNode X → LStep ClosedTableau Hist record ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                                              (projection A L, projection A R ++ [~φ], none)
  -- Condition 6a repeats are end nodes:
  | rep {X Hist} (rep : condSixRepeat X Hist) : ClosedTableau Hist X

inductive Provable : Formula → Prop
  | byTableauL {φ : Formula} : ClosedTableau ([],[]) ⟨[~φ], [], none⟩ → Provable φ
  | byTableauR {φ : Formula} : ClosedTableau ([],[]) ⟨[], [~φ], none⟩ → Provable φ

-- Definition 17, page 30
def Inconsistent : TNode → Prop
  | LR => Nonempty (ClosedTableau .nil LR)

def Consistent : TNode → Prop
  | LR => ¬Inconsistent LR
