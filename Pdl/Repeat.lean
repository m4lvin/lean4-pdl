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
| split j k : Step (j+k) [j,k]

inductive HisTree : (List Nat) → Nat → Type
| leaf : HisTree H 0
| step : Step n ms → (∀ {m}, m ∈ ms → HisTree (n :: H) m) → HisTree H n
| rep : m ∈ H → HisTree H m

open Step HisTree

def helper (t : HisTree H j) (m_def : m ∈ [j]) : HisTree H m :=
  (List.mem_singleton.1 m_def) ▸ t

-- * EXAMPLES

example : HisTree [] 4 :=
  -- 4
  step down $ helper $
  -- 2
  step down $ helper
  -- 0
  leaf


def helperSplit (m_def : m ∈ [j1, j2]) (t1 : HisTree H j1) (t2 : HisTree H j2) : (HisTree H m) :=
  if h1 : m = j1 then
    h1 ▸ t1
  else if h2 : m = j2 then
    h2 ▸ t2
  else
    by exfalso; aesop

example : HisTree [] 4 :=
  --   4
  step (split 2 2) $
  -- 2   2
  (fun m_in =>
    let two_to_zero := (step down $ helper $ leaf)
  -- 0   0
    helperSplit m_in
    two_to_zero
    two_to_zero)

example : HisTree [] 4 :=
  --      4
  step (split 1 3) $
  --    1   3
  (fun m_in =>
    helperSplit m_in
    (step up $ helper $
     -- 2
     step down $ helper $
     -- 0
     leaf)
           (step up $
           -- 4 ( repeat)
           helper $ rep $
           by aesop)
  )

-- * CLAIMS

-- What properties of the HisTree type could now be tricky to prove?
-- Ideally it should be similar to "loadedDiamondPaths" for PDL.


-- * FURTHER IDEAS

/-
- Change repeat condition to say that a split must have been on the way?
  This needs to also keep track of rules in history?!
- ...
-/
