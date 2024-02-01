-- TABLEAU

import Mathlib.Data.List.Card

import Pdl.Syntax
import Pdl.Measures
import Pdl.Semantics
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
  rw [projection]
  simp
  induction X
  aesop
  aesop


-- LOADING

def boxesOf : Formula → List Program × Formula
| (Formula.box prog nextf) => let (rest,endf) := boxesOf nextf; ⟨prog::rest, endf⟩
| f => ([], f)

-- From ~⌈α⌉φ to ~'⌊α⌋χ
def toNegLoad (α : Program) (φ : Formula) : NegLoadFormula :=
  match boxesOf φ with
    | ([],f) => ~'⌊α⌋f
    | (bs,f) => sorry

-- NOTES about the History type:
-- - The newest/lowest TNode should be the head of the list.
-- - we also need the rule that is applied to check isCritical.
--   Add "× LocalRuleApp" to History type? Need Σ.
-- - currently we only track "big" steps, do we need local steps?
--
def History : Type := List TNode -- This may not be enough!

-- A history is loaded iff it always contains a loaded formula.
def isLoaded : History → Bool
  | [] => True
  | ((_,_,some _)::rest) => isLoaded rest
  | ((_,_,none  )::_) => False

def isCriticalTo : TNode → (Hist : History) → Bool
  | X, [] => False
  | X, (Y::rest) =>
      if X == Y then sorry else sorry -- need to know the rules that were applied!

-- MB Condition 6, simplified to only represent closed tableau:
--
-- A node t repeating s can be treated as a closed end node if
-- the path from s to t is critical and loaded.
def isCondSixRepeat : TNode → History → Bool :=
  by sorry

-- TABLEAUX

-- The "Step" notation has two jobs:
-- - flip the order in the definition below to be more natural.
-- - avoid having to repeat "parent" to build the history.
notation "Step" Ct:arg Hist:arg parent:arg child:arg => Ct (parent::Hist) child → Ct Hist parent

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
inductive ClosedTableau : History → TNode → Type
  -- Do a local tableau:
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, ClosedTableau (X::Hist) Y) → ClosedTableau Hist X
  -- TODO: should the history also track what happens "within" loc?
  -- The (M+) rule:
  | mrkL : (~⌈α⌉φ) ∈ L → Step ClosedTableau Hist (L, R, none)
                                                 (L.remove (~⌈α⌉φ), R, some (Sum.inl (toNegLoad α φ)))
  | mrkR : (~⌈α⌉φ) ∈ R → Step ClosedTableau Hist (L, R, none)
                                                 (L, R.remove (~⌈α⌉φ), some (Sum.inr (toNegLoad α φ)))
  -- The (At) rule:
  -- TODO: can we avoid the four cases?
  | atmL   {A X χ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inl (~'⌊·A⌋(χ : LoadFormula)))⟩
                                                              (projection A L, projection A R, some (Sum.inl (~'χ)))
  | atmL'  {A X φ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                                              (projection A L ++ [~φ], projection A R, none)
  | atmR   {A X χ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inr (~'⌊·A⌋(χ : LoadFormula)))⟩
                                                              (projection A L, projection A R, some (Sum.inr (~'χ)))
  | atmR'  {A X φ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                                              (projection A L, projection A R ++ [~φ], none)
  | repeat {X Hist} (rep : isCondSixRepeat X Hist) : ClosedTableau Hist X
  --
  -- NOTE: If we want only finite tableaux then "repeat" may have to be eager?
  -- Would we need to add its negation in all other rules? For now, leave it.

inductive Provable : Formula → Prop
  | byTableauL {φ : Formula} : ClosedTableau [] ⟨[~φ], [], none⟩ → Provable φ
  | byTableauR {φ : Formula} : ClosedTableau [] ⟨[], [~φ], none⟩ → Provable φ

-- MB: Definition 17, page 30
def Inconsistent : List Formula → Prop
  | X => ∃ L R, L ++ R = X ∧ Nonempty (ClosedTableau [] ⟨L, R, none⟩)

def Consistent : List Formula → Prop
  | X => ¬Inconsistent X
