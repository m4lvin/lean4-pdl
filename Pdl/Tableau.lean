import Mathlib.Data.List.ReduceOption

import Pdl.LocalTableau

/-! # PDL-Tableaux (Section 4) -/

open HasLength

/-! ## Projections -/

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

/-- A history is a list of Sequents.
This only tracks "big" steps, hoping we do not need steps within a local tableau.
The head of the first list is the newest Sequent. -/
abbrev History : Type := List Sequent

/-- We have a repeat iff the history contains a node that is `setEqTo` the current node. -/
def rep (Hist : History) (X : Sequent) : Prop := ∃ Y ∈ Hist, Y.setEqTo X

/-- A lpr means we can go `k` steps back in the history to
reach an equal node, and all nodes on the way are loaded.
Note: `k=0` means the first element of `Hist` is the companion. -/
def LoadedPathRepeat (Hist : History) (X : Sequent) : Type :=
  Subtype (fun k => (Hist.get k).setEqTo X ∧ ∀ m ≤ k, (Hist.get m).isLoaded)

theorem LoadedPathRepeat_comp_isLoaded (lpr : LoadedPathRepeat Hist X) : (Hist.get lpr.val).isLoaded := by
  rcases lpr with ⟨j, claim⟩
  apply claim.2 j (le_refl j)

theorem LoadedPathRepeat_rep_isLoaded (lpr : LoadedPathRepeat Hist X) : X.isLoaded := by
  rcases lpr with ⟨k, claim⟩
  rw [← setEqTo_isLoaded_iff claim.1]
  exact claim.2 k (le_refl k)

/-! ## The PDL rules -/

/-- A rule to go from Γ to Δ. Note the four variants of the modal rule. -/
inductive PdlRule : (Γ : Sequent) → (Δ : Sequent) → Type
  -- The (L+) rule:
  | loadL : (~⌈⌈δ⌉⌉⌈α⌉φ) ∈ L → PdlRule (L, R, none)
                                       (L.erase (~⌈⌈δ⌉⌉⌈α⌉φ), R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊α⌋φ))))
  | loadR : (~⌈⌈δ⌉⌉⌈α⌉φ) ∈ R → PdlRule (L, R, none)
                                       (L, R.erase (~⌈⌈δ⌉⌉⌈α⌉φ), some (Sum.inr (~'(⌊⌊δ⌋⌋⌊α⌋φ))))
  -- The (L-) rule:
  | freeL : PdlRule (L, R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊α⌋(φ : Formula)))))
                    (L.insert (~⌈⌈δ⌉⌉⌈α⌉φ), R, none)
  | freeR : PdlRule (L, R, some (Sum.inr (~'(⌊⌊δ⌋⌋⌊α⌋(φ : Formula)))))
                    (L, R.insert (~⌈⌈δ⌉⌉⌈α⌉φ), none)
  -- The (M) rule:
  | modL   {A X ξ} : X = ⟨L, R, some (Sum.inl (~'⌊·A⌋(ξ : AnyFormula)))⟩ → PdlRule X
                         ( match ξ with
                         | .normal φ => ⟨(~φ) :: projection A L, projection A R, none⟩
                         | .loaded χ => ⟨projection A L, projection A R, some (Sum.inl (~'χ))⟩ )
  | modR   {A X ξ} : X = ⟨L, R, some (Sum.inr (~'⌊·A⌋(ξ : AnyFormula)))⟩ → PdlRule X
                         ( match ξ with
                         | .normal φ => ⟨projection A L, (~φ) :: projection A R, none⟩
                         | .loaded χ => ⟨projection A L, projection A R, some (Sum.inr (~'χ))⟩ )

/--
The `Tableau [parent, grandparent, ...] child` type.

A closed tableau for X is either of:
- a local tableau for X followed by closed tableaux for all end nodes,
- a PDL rule application
- a successful loaded repeat (MB condition six)
-/
inductive Tableau : History → Sequent → Type
  | loc {X} (nrep : ¬ rep Hist X) (nbas : ¬ X.basic) (lt : LocalTableau X)
            (next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y) : Tableau Hist X
  | pdl {X Y} (nrep : ¬ rep Hist X) (bas : X.basic) (r : PdlRule X Y)
              (next : Tableau (X :: Hist) Y) : Tableau Hist X
  | lrep {X Hist} (lpr : LoadedPathRepeat Hist X) : Tableau Hist X

def Tableau.isLrep : (Tableau Hist X) → Prop
  | .loc .. => False
  | .pdl .. => False
  | .lrep .. => True

inductive provable : Formula → Prop
  | byTableauL {φ : Formula} : Tableau .nil ⟨[~φ], [], none⟩ → provable φ
  | byTableauR {φ : Formula} : Tableau .nil ⟨[], [~φ], none⟩ → provable φ

/-- A Sequent is inconsistent if there exists a closed tableau for it. -/
def inconsistent : Sequent → Prop
  | LR => Nonempty (Tableau .nil LR)

/-- A `Sequent` is consistent iff it is not inconsistent. -/
def consistent : Sequent → Prop
  | LR => ¬inconsistent LR
