import Std.Data.List.Lemmas
import Aesop
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Use

-- This file is not part of PDL, but just a playground for
-- representing trees with repeats / back-pointers.

-- Instead of formulas, here we use Nat.
-- The following type would allows arbitrary trees with Nat entries.
-- inductive Tree
-- | Node : Nat → List Tree → Tree

-- But suppose we only want trees formed using these three rules:
--
--  k        k          j+k
-- ---(up)  ---(down)  -----(split)
-- k+1      k-2        j   k
--
-- and such that leafs must be either 1 or *repeats*.

-- * DEFINITIONS

inductive Step : Nat → List Nat → Type
| up    : Step k     [k+2]
| split : Step (k+1) [1,k]

def SomeStep := Σ n ms, Step n ms

abbrev History := List SomeStep
-- (Not using "def" because we want typeclass inference to see through this.)

inductive HisTree : History → Nat → Type
| leaf : HisTree H 1
| step : {ms : _} → (s : Step n ms) → (next : ∀ {m}, m ∈ ms → HisTree (⟨_,_,s⟩ :: H) m) → HisTree H n
| rep : (s : Step n ms) → ⟨_,_,s⟩ ∈ H → HisTree H m

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
      (step up $ helper $ by apply rep split; aesop)

-- * NEW: PATHS, inductively and hopefully better than the unsafe verson below

inductive PathIn : HisTree H n → Type
| nil : PathIn ht
| cons m (m_in : m ∈ ms) (s : Step n ms) next (rest : PathIn (next m_in)) : PathIn (step s next)

def PathIn.length : PathIn ht → Nat
| nil => 0
| cons _ _ _ _ rest => 1 + rest.length

-- Convert a path to a list of Nats, where the last path element will be the head.
def PathIn.toList {ht : HisTree H m} : PathIn ht → List Nat
| nil => []
| cons _ _ _ _ rest => toList rest ++ [m]

-- Convert a path to a list of Steps, where the last path element will be the head.
def PathIn.toSteps : PathIn ht → List SomeStep
| nil => []
| @cons _ _ _ _ _ s _ rest => toSteps rest ++ [⟨_,_,s⟩]

theorem PathIn.length_eq_toListLength H n (ht : HisTree H n) (p : PathIn ht):
  p.length = p.toList.length := by
  induction p -- now works, and termination too. Maybe because PathIn.cons now has more arguments to keep track of?
  · simp [PathIn.toList, PathIn.length]
  case cons H ms n m m_in s next rest IH =>
    simp [PathIn.toList, PathIn.length]
    rw [IH]
    omega

def treeAt : PathIn ht → (Σ H n, HisTree H n)
| PathIn.nil => ⟨_,_,ht⟩
| PathIn.cons _ _ _ _ rest => treeAt rest -- wow, that is much simpler than treeAt' below :-)

-- A better version to also give us the determined history:
def treeAtP {ht : HisTree H n} : (p : PathIn ht) → (Σ n, HisTree (p.toSteps ++ H) n)
| PathIn.nil =>
    have : H = (PathIn.nil.toSteps ++ H) := by simp [PathIn.toSteps]
    ⟨n, this ▸ ht⟩
| PathIn.cons m m_in s next rest =>
    have : rest.toSteps ++ ⟨_,_,s⟩ :: H = (PathIn.cons m m_in s next rest).toSteps ++ H := by
      simp [PathIn.toSteps]
    this ▸ treeAtP rest
termination_by
  x => sizeOf x

-- Or, as a proof above treeAt:
theorem treeAtH_is H n {ht : HisTree H n} (p : PathIn ht) : (treeAt p).1 = (p.toSteps ++ H) := by
  cases p
  · simp [PathIn.toSteps, treeAt]
  case cons ms m m_in s next rest =>
    let ht := next m_in
    have IH := treeAtH_is (⟨n,ms,s⟩ :: H) m rest
    simp [PathIn.toSteps, treeAt]
    -- have forTermination : rest.length < (PathIn.cons m m_in s next rest).length := by simp[PathIn.length]; omega
    exact IH
termination_by
  sizeOf p
decreasing_by
  simp_wf;
  subst_eqs
  simp at *
  -- Why do I now have different "rest" and "next"?
  all_goals sorry

-- def goUp : PathIn ⟨H, m, ht⟩ → Option PathIn ⟨H, _, ht⟩ -- TODO??

def isRep : (Σ H n, HisTree H n) → Prop
| ⟨_, _, rep _ _⟩ => True
| _ => False

def isSplit : (Σ H n, HisTree H n) → Prop
| ⟨_, _, step split _⟩ => True
| _ => False

def isPrefixOf : PathIn ht → PathIn ht → Prop
| PathIn.nil, _ => true
| PathIn.cons m _ _ _ rest, PathIn.cons m' _ _ _ rest' => (meq : m = m') → isPrefixOf rest (meq.symm ▸ rest')
| PathIn.cons _ _ _ _ _, PathIn.nil => false

-- Example of a statement about repeats that should be tricky to prove now:
-- Any path to a repeat must have a prefix to a split.
-- (This may or may not be similar enough to condition 6a for PDL.)
theorem rep_needs_split_above
    {ht : HisTree [] n}
    (p : PathIn ht)
    (p_is_rep : isRep (treeAt p))
  : ∃ p', isPrefixOf p' p ∧ isSplit (treeAt p') :=
  by
  unfold isRep at *
  rcases treeAt p with ⟨H',n',ht⟩
  cases n'
  case zero =>
    -- This should be impossible, a 0 cannot be repeated.
    by_contra hyp
    simp at hyp
    sorry
  case succ mp_pred =>
    -- TODO: should "rep" contain the information how long ago the repeat is?
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
| ⟨_, k, rep _ _, ⟩, (n::_::_   ) => n == k
| ⟨_, k, @step _ _ ms _ next⟩, (n::m::rest) => n == k ∧ ∃ m_in : m ∈ ms, (isPathIn ⟨_, _, next m_in⟩ (m::rest) )

def SafePathIn (t : Σ H n, HisTree H n) := Subtype (fun l => isPathIn t l)

-- Given a SafePathIn, treeAt' should always return some something, never none.

def treeAt' : List Nat → (Σ H n, HisTree H n) → Option (Σ H n, HisTree H n)
| [], t => t
| [n], ⟨H, k, t⟩ => if n == k then some ⟨H,k,t⟩ else none
| (_::_::_   ), ⟨_, 1,leaf⟩ => none
| (n::_::_   ), ⟨H, k, rep s r⟩ => if n == k then some ⟨H,k, rep s r⟩ else none
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
