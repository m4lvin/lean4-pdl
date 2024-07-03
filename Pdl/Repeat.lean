import Aesop
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import Mathlib.Data.List.Basic

-- This file is not part of PDL, but just a playground for
-- representing trees with repeats / back-pointers.

-- Instead of formulas, here we use Nat.

/-! ### Minimal Binary Tree examples -/

-- The following type allows arbitrary binary trees Nat entries.
inductive MyTree
| Leaf : Nat → MyTree
| Node : Nat → MyTree → MyTree → MyTree

-- But suppose now we only want to allow trees such that for all
-- `Leaf k` the value `k` has occurred somewhere *above* it.
--
-- BAD:
--   Leaf 4  -- no history at all, not allowed
--   Node 3 (Leaf 4) (Leaf 3)  -- 3 is fine, but 4 not allowed
--
-- NICE:
--   Node 3 (Leaf 3) (Leaf 3)
--   Node 3 (Node 2 (Leaf 3) (Leaf 2)) (Leaf 3)
--   -- here 2 is an immediate repeat, but the 3 is longer ago

def isNiceAfter (ns : List Nat) : (t : MyTree) → Prop
| MyTree.Leaf k => k ∈ ns
| MyTree.Node k c1 c2 => isNiceAfter (k :: ns) c1 ∧ isNiceAfter (k :: ns) c2

def isNice : MyTree → Prop := isNiceAfter []

-- So the type I want is then in fact:
def niceTrees := Subtype isNice

-- But I would like a direct, inductive definition of this.
-- For this we add the Nat list as a type parameter:

inductive NiceTree : List Nat → Type
| Node : (k : Nat) → NiceTree (k :: N) → NiceTree (k :: N) → NiceTree N
| Leaf : (k : Nat) → k ∈ N → NiceTree N

notation "lf " k => NiceTree.Leaf k (by simp)

-- NICE examples:
example : NiceTree [] := .Node 3 (lf 3) (lf 3)
example : NiceTree [] := .Node 3 (.Node 2 (lf 3) (lf 2)) (lf 3)

-- BAD examples:
example : NiceTree [] := NiceTree.Leaf 4 (sorry : 4 ∈ []) -- impossible, as we want it to be
example : NiceTree [] := .Node 3 (.Leaf 4 sorry) (lf 3)  --  also impossible

-- So this works, but I am wondering if there is a better way.
-- Especially, because saying and proving things like the following seems hard/impossible:

-- "Whenever we have a leaf, there must be a node above it with the same value."
-- How do I even say this theorem in Lean?

theorem find_predecessor_of_leaf :
    (h : t = NiceTree.Leaf k k_in_N)
      → ∃ s : NiceTree [], sorry -- here I want to say "s is above"
    :=
  sorry

-- In general, once I am given a thing like `NiceTree.Leaf k k_in_N` then
-- too much information is lost, and it seems very tricky to "jump back up"
-- and get the whole tree again.

-- Saying "s is above t" is possible, for that I have a definition of
-- Paths, somewhat like this
inductive PathIn : NiceTree H → Type
| nil : PathIn ht
| goLeft (c1 c2 : NiceTree (k :: rest)) (tail : PathIn c1) : PathIn (NiceTree.Node k c1 c2)
| goRight (c1 c2 : NiceTree (k :: rest)) (tail : PathIn c2) : PathIn (NiceTree.Node k c1 c2)



/-! ### OLDER, more complicated toy example with rules -/

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
deriving Repr

def SomeStep := Σ n ms, Step n ms

abbrev History := List Nat
-- (Not using "def" because we want typeclass inference to see through this.)

inductive HisTree : History → Nat → Type
| leaf : HisTree H 1
| step : {ms : _} → (s : Step n ms) → (next : ∀ {m}, m ∈ ms → HisTree (n :: H) m) → HisTree H n
| rep : (k : Nat) → some k = H.indexOf? m → HisTree H m
-- TODO: deriving Repr -- not working?

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
      (step up $ helper $ by apply rep; aesop)

-- * NEW: PATHS, inductively and hopefully better than the unsafe verson below

/-- A path in a tree. Note that in `cons` the `m` is the child we move to. -/
inductive PathIn : HisTree H n → Type
| nil : PathIn ht
| cons m (m_in : m ∈ ms) (s : Step n ms) next (rest : PathIn (next m_in)) : PathIn (step s next)
-- is the "cons" above generating something bad in proofs below?

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
| cons _ _ s _ rest => toSteps rest ++ [⟨_,_,s⟩]

def blaPath : PathIn bla := by
  apply PathIn.cons 3 (by aesop)
  simp [helperSplit]
  apply PathIn.cons 2 (by aesop)
  simp [helperSplit]
  apply PathIn.cons 4 (by aesop)
  apply PathIn.nil

example : blaPath.toList == [2,3,4] := by rfl

def PathIn.dropAtEnd (p : PathIn ht) (k : Nat) (h : k ≤ p.length) : PathIn ht :=
  if _ : k = p.length then nil else
    match p with
    | nil => by simp only [length, nonpos_iff_eq_zero] at *; absurd h; assumption
    | cons m m_in s next rest => by
        have newRest := rest.dropAtEnd k (by simp [PathIn.length] at *; omega)
        exact cons m m_in s next newRest

-- #eval blaPath.length

-- #eval (blaPath.dropAtEnd 1 (by simp [PathIn.length])).toSteps

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

theorem length_is_good {ht : HisTree H n} (p : PathIn ht) :
    (treeAt p).1.length = H.length + p.length := by
  induction p
  case nil =>
    simp [treeAt, PathIn.length]
  case cons _ _ _ _ _ _ _ _ IH =>
    simp only [treeAt, PathIn.length]
    rw [IH]
    simp
    omega

-- maybe not needed?
def Environment (root : HisTree H n) : Type := PathIn root → PathIn root

/-- Like `treeAt` but "jumping back" to companions. -/
-- NOTE: Only works for H=[] to ensure the repeat k does not jump too far above!
-- TODO: rewrite in term-mode
def unravelAt {root : HisTree [] n} : PathIn root → PathIn root := by
  intro p
  let ⟨Hp,m,htp⟩ := treeAt p
  cases htp
  case leaf =>
    exact p
  case step =>
    exact p
  case rep k k_eq =>
    -- roll back the path p by k steps!
    apply p.dropAtEnd k
    have Hp_len_def := length_is_good p
    have : k < Hp.length := sorry -- List.indexOf_le_length
    -- rw [Hp_len_def] at this
    -- TODO: too strong goal here, need to also add the length of H still?!?!??!
    -- linarith
    -- omega
    sorry

/-- Like `treeAt` but "jumping back" to companions. -/
-- TODO: rewrite in term-mode
def unravelAt' {root : HisTree H n} : PathIn root → PathIn root := by
  intro p
  let ⟨Hp,m,htp⟩ := treeAt p
  cases htp
  case leaf =>
    exact p
  case step =>
    exact p
  case rep k k_eq =>
    -- roll back the path p by k steps!
    apply p.dropAtEnd k
    have Hp_len_def := length_is_good p
    have : k < Hp.length := sorry -- List.indexOf_le_length
    -- rw [Hp_len_def] at this
    -- TODO: too strong goal here, need to also add the length of H still?!?!??!
    -- linarith
    -- omega
    sorry

-- A potentialy better version of treeAt to also give us the determined history:
def treeAtP {ht : HisTree H n} : (p : PathIn ht) → (Σ n, HisTree (p.toList ++ H) n)
| PathIn.nil =>
    have : H = (PathIn.nil.toList ++ H) := by simp [PathIn.toList]
    ⟨n, this ▸ ht⟩
| PathIn.cons m m_in s next rest =>
    have : rest.toList ++ n :: H = (PathIn.cons m m_in s next rest).toList ++ H := by
      simp [PathIn.toList]
    this ▸ treeAtP rest
termination_by
  x => sizeOf x

-- def goUp : PathIn ⟨H, m, ht⟩ → Option PathIn ⟨H, _, ht⟩ -- TODO??

@[simp]
def isRep : (Σ H n, HisTree H n) → Prop
| ⟨_, _, rep _ _⟩ => True
| _ => False

@[simp]
def isSplit : (Σ H n, HisTree H n) → Prop
| ⟨_, _, step split _⟩ => True
| _ => False

@[simp]
def isPrefixOf : PathIn ht → PathIn ht → Prop
| PathIn.nil, _ => true
| PathIn.cons m _ _ _ rest, PathIn.cons m' _ _ _ rest' => (meq : m = m') → isPrefixOf rest (meq.symm ▸ rest')
| PathIn.cons _ _ _ _ _, PathIn.nil => false

@[simp]
def sameNode : PathIn ht1 → PathIn ht2 → Prop
| p1, p2 => (treeAtP p1).fst = (treeAtP p2).fst

theorem sameNode_cons {rest rest'} :
    sameNode rest rest' →
    sameNode (PathIn.cons m m_in_ms st next rest) (PathIn.cons m m_in_ms st next rest') := by
  intro hyp
  simp_all [treeAtP]
  sorry


-- Example of an easier statement about repeats.
-- Any path to a repeat must have a prefix to the same thing,
-- (This should be implied by the def of condition 6a for PDL.)
theorem rep_needs_same_above
    {ht : HisTree [] n}
    (p : PathIn ht)
    (p_is_rep : isRep (treeAt p))
  : ∃ p', isPrefixOf p' p ∧ sameNode p p'  :=
  by
  cases p
  case nil =>
    simp [treeAt, treeAtP] at *
    cases ht
    all_goals simp at *
    case rep _ _in_empty =>
      exfalso
      cases _in_empty
  case cons ms m m_in_ms st next rest =>
    -- now want to use an induction hypothesis, but need it for a non-empty history!
    sorry

theorem rep_needs_same_above_general
    {H n}
    {ht : HisTree H n}
    (p : PathIn ht)
    (p_is_rep : isRep (treeAt p))
  : ∃ p', isPrefixOf p' p ∧ sameNode p p'  :=
  by
  cases H -- induction does not allow us to generalize n
  case nil =>
    cases p
    case nil =>
      simp [treeAt, treeAtP] at *
      cases ht
      all_goals simp at *
      case rep _ _in_empty =>
        exfalso
        cases _in_empty
    case cons ms m m_in_ms st next rest =>
      -- now want to use an induction hypothesis, but need it for a non-empty history!
      have IH_rest := rep_needs_same_above_general rest p_is_rep
      rcases IH_rest with ⟨q', q_claim⟩
      use PathIn.cons m m_in_ms st _ q' -- ??
      constructor
      · simp
        exact q_claim.1
      · exact sameNode_cons q_claim.2

  -- MYSTERY: where and when do we really need that the repeat is within p ??

  case cons st H =>
    cases p
    case nil =>
      simp [treeAt, treeAtP] at *
      cases ht
      all_goals simp at *
      case rep _ _in_empty =>
        -- TODO: is the repeat one ore more steps ago?
        sorry
    case cons ms m m_in_ms st next rest =>
      -- now want to use an induction hypothesis, but need it for a non-empty history!

      -- TODO need something for termination here!
      -- have : H.length + p.length < H.length + p.length := sorry
      have IH_rest := rep_needs_same_above_general rest (by sorry)
      rcases IH_rest with ⟨q', q_claim⟩
      use PathIn.cons m m_in_ms st _ q' -- ??
      constructor
      · simp
        exact q_claim.1
      · exact sameNode_cons q_claim.2

termination_by
  H.length + p.length
decreasing_by
  · simp_wf
    subst_eqs
    -- why the different "rest" and "p" here?!
    sorry
  · simp_wf
    subst_eqs
    sorry

-- Example of a statement about repeats that should be tricky to prove now:
-- Any path to a repeat must have a prefix to a split.
-- (This may or may not be similar enough to condition 6a for PDL.)
theorem rep_needs_split_above
    {ht : HisTree [] n}
    (p : PathIn ht)
    (p_ht_def : p_ht = treeAt p)
    (p_is_rep : isRep p_ht)
  : ∃ p', isPrefixOf p' p ∧ isSplit (treeAt p') :=
  by
  unfold isRep at *
  rcases p_ht with ⟨H',n',ht⟩
  induction ht
  case leaf =>
    -- Impossible, a leaf is not a repeat.
    exfalso
    simp at *
  case rep =>
    cases p
    case nil _ _ _ _in_H' =>
      subst_eqs
    case cons _in_H ms m m_in s next rest=> -- n' ks n'_ks n'_ks_in_H' ms m m_in_ms n_ms next rest IH foo
      sorry
  case step =>
    -- Impossible, a step is not a repeat.
    exfalso
    simp at p_is_rep

-- TODO: should "rep" contain the information how long ago the repeat is?

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
