import Std.Data.List.Lemmas
import Aesop
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Convert

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
| up    : Step k     [k+2]
| split : Step (k+1) [1,k]

inductive HisTree : List Nat → Nat → Type
| leaf : HisTree H 1
| step : {ms : _} → Step n ms → (∀ {m}, m ∈ ms → HisTree (n :: H) m) → HisTree H n
| rep : m ∈ H → HisTree H m

open Step HisTree

def helper (t : HisTree H j) (m_def : m ∈ [j]) : HisTree H m :=
  (List.mem_singleton.1 m_def) ▸ t

-- * EXAMPLES

def helperSplit (t1 : HisTree H j1) (t2 : HisTree H j2) (m_def : m ∈ [j1, j2]) : (HisTree H m) :=
  if h1 : m = j1 then
    h1 ▸ t1
  else if h2 : m = j2 then
    h2 ▸ t2
  else
    by exfalso; aesop

def bla : HisTree [] 4 :=
  --      4
  step split $ helperSplit
    -- 1    3
    leaf $
    step split $ helperSplit
    --    1   2
      leaf
      --      4
      (step up $ helper $ rep (by aesop))

-- * NEW: PATHS, inductively and hopefully better than the unsafe verson below

inductive PathIn : (Σ H n, HisTree H n) → Type
| nil : PathIn ht
| cons m (m_in : m ∈ ms) (rest : PathIn ⟨n :: H, m, next m_in⟩) : PathIn ⟨H, n, step s next⟩

def PathIn.toList : PathIn ⟨H, m, ht⟩ → List Nat
| nil => []
| cons m _ rest => m :: toList rest

def treeAt : PathIn ⟨H, n, ht⟩ → (Σ H n, HisTree H n)
| PathIn.nil => ⟨H, n, ht⟩
| PathIn.cons _ _ rest => treeAt rest -- wow, that is much simpler than treeAt' :-)

def isPrefixOf : PathIn ⟨H, n, ht⟩ → PathIn ⟨H, n, ht⟩ → Prop
| PathIn.nil, _ => true
| PathIn.cons m _ rest, PathIn.cons m' _ rest' => (meq : m = m') → isPrefixOf rest (meq.symm ▸ rest')
| PathIn.cons _ _ _, PathIn.nil => false

-- Example of a statement about repeats that should be tricky to prove now:
-- Any path to a repeat must have a prefix to a split.
-- (This may or may not be similar enough to condition 6a for PDL.)
theorem rep_needs_split_above
    (p : PathIn ⟨[], m, ht⟩)
    (p_is_rep : treeAt p = ⟨Hp, mp, rep k_in⟩)
  : ∃ (k : Nat) (Hp' : List Nat) (next : _) (p' : PathIn ⟨[], m, ht⟩),
      isPrefixOf p' p ∧ (treeAt p' = ⟨Hp', k+1, step (@split k) next⟩) :=
  by
  sorry


-- TODO: define loopy-paths succ relation including steps via back-loops


-- TODO: theorem that there is always a loopy-path to a leaf!?



-- * OLD: POINTERS AND PATHS, naively - unsafe and safe but (probably) annoyinf to use version

def unsafePointer := (Σ H n, HisTree H n) × List Nat

example : unsafePointer := ⟨⟨_,_,bla⟩, [4,1,(2:Nat)]⟩

def isPathIn : (Σ H n, HisTree H n) → List Nat → Bool
| _, [] => True
| ⟨_, k, _⟩, [n]          => n == k
| ⟨_, 1, leaf⟩,  (_::_::_   ) => False
| ⟨_, k, rep _, ⟩, (n::_::_   ) => n == k
| ⟨_, k, @step _ _ ms _ next⟩, (n::m::rest) => n == k ∧ ∃ m_in : m ∈ ms, (isPathIn ⟨_, _, next m_in⟩ (m::rest) )

def SafePathIn (t : Σ H n, HisTree H n) := Subtype (fun l => isPathIn t l)

-- Given a SafePathIn, treeAt' should always return some something, never none.

def treeAt' : List Nat → (Σ H n, HisTree H n) → Option (Σ H n, HisTree H n)
| [], t => t
| [n], ⟨H, k, t⟩ => if n == k then some ⟨H,k,t⟩ else none
| (_::_::_   ), ⟨_, 1,leaf⟩ => none
| (n::_::_   ), ⟨H, k, rep r⟩ => if n == k then some ⟨H,k, rep r⟩ else none
| (n::m::rest), ⟨_, k, @step _ _ ms _ next⟩ =>
  if n == k then
    if m_in : m ∈ ms then
      treeAt' (m::rest) ⟨_, _, next m_in⟩
    else
      none
  else
    none

-- Now, given a SafePathIn leading to a repeat, how do we move back up to the companion?
-- May need the assumption that H = [], or at least that it is at least as long as the companion-repeat path.

def Pointer := (Σ H n, HisTree H n) × List Nat

-- * CLAIMS

-- What properties of the HisTree type could now be tricky to prove?
-- Ideally it should be similar to "loadedDiamondPaths" for PDL.


-- * FURTHER IDEAS

/-
- Change repeat condition to say that a split must have been on the way?
  This needs to also keep track of rules in history?!
- ...
-/
