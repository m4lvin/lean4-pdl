import Std.Data.List.Lemmas
import Aesop
import Mathlib.Tactic.Tauto

-- This file is not part of PDL, but just a playground for
-- representing trees with repeats / back-pointers.

-- Instead of formulas, here we use Nat.
-- This type allows arbitrary trees with Nat entries.
inductive Tree
| Node : Nat → List Tree → Tree

-- But suppose only want trees formed using three rules
--
--  k        k          j+k
-- ---(up)  ---(down)  -----(split)
-- k+1      k-2        j   k
--
-- and such that leafs must be either 0 or *repeats*.

-- * DEFINITIONS

inductive Step : Nat → List Nat → Type
| up    : Step k     [k+1]
| down  : Step (k+2) [k]
| split : Step (j+k) [j,k]

inductive HisTree : (List Nat) → Nat → Type
| leaf : HisTree H 0
| step : Step n ms → (∀ m ∈ ms, HisTree (n :: H) m) → HisTree H n
| rep : m ∈ H → HisTree H m

open Step HisTree

def helper : HisTree H j → ((m : Nat) → m ∈ [j] → HisTree H m) := by
  intro t m m_def
  simp at *
  subst m_def
  exact t

-- * EXAMPLES

/-
   4
   2
   0 -/
example : HisTree [] 4 := by
  apply step down
  apply helper
  apply step down
  apply helper
  apply leaf

/-
    4
   2 2
   0 0 -/
example : HisTree [] 4 := by
  apply step (@split 2 2)
  intro m m_def; simp at *; subst m_def -- same goal because same sub-tree!!
  apply step down
  apply helper
  apply leaf


def helperSplit j1 j2 : HisTree H j1 → HisTree H j2 → (∀ m ∈ [j1, j2], HisTree H m) := by
  intro t1 t2 m m_def
  simp at m_def
  -- Here "cases m_def" does not work, but is there a more elegant way?
  if h : m = j1 then
    subst h; exact t1
  else
    if h : m = j2 then
     subst h; exact t2
   else
     exfalso; aesop

/-
    4
   1 3
   2 4*
   0    -/
example : HisTree [] 4 := by
  apply step (@split 1 3)
  apply helperSplit
  · apply step up
    apply helper
    apply step down
    apply helper
    apply leaf
  · apply step up
    apply helper
    apply rep -- Tadaa!
    aesop

-- * CLAIMS

-- What properties of the HisTree type could now be tricky to prove?
-- Ideally it should be similar to "loadedDiamondPaths" for PDL.


-- * FURTHER IDEAS

/-
- Change repeat condition to say that a split must have been on the way?
  This needs to also keep track of rules in history?!
- ...
-/
