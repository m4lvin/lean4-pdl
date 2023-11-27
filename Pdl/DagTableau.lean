import Mathlib.Data.Finset.Basic

import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics
import Pdl.Star

-- IDEA: adjust the type to forbid atomic program on (neg)top level?

inductive DagFormula : Type
  | bottom : DagFormula
  | atom_prop : Char → DagFormula
  | neg : DagFormula → DagFormula
  | and : DagFormula → DagFormula → DagFormula
  | box : Program → DagFormula → DagFormula
  | dag : Program → DagFormula → DagFormula
  deriving Repr

def DagFormula.boxes : List Program → DagFormula → DagFormula
  | [], f => f
  | (p :: ps), f => DagFormula.box p (DagFormula.boxes ps f)

/-
def decDagFormula (f g : DagFormula) : Decidable (f = g) :=
  match f,g with
  | DagFormula.atom_prop A, DagFormula.atom_prop B =>
    dite (A = B) (fun h => isTrue (by rw [h])) (fun h => isFalse (by simp; exact h))
  | DagFormula.atom_prop _, _ => isFalse (by intro; contradiction)

-- TODO: many many cases
-/
instance : DecidableEq DagFormula := sorry -- decDagFormula? - or can a newer Lean version derive this?


local notation "·" c => DagFormula.atom_prop c
local prefix:11 "~" => DagFormula.neg

local notation "⊥" => DagFormula.bottom
local infixr:66 "⋀" => DagFormula.and
local infixr:60 "⋁" => DagFormula.or

local notation "⌈" α "⌉" P => DagFormula.box α P
local notation "⌈⌈" α "⌉⌉" P => DagFormula.boxes α P
local notation "⌈" α "†⌉" P => DagFormula.dag α P

-- THE f FUNCTION
-- | Borzechowski's f function, sort of.

def undag : DagFormula → Formula
  | ⊥ => ⊥
  | ~f => ~(undag f)
  | ·c => ·c
  | φ⋀ψ => undag φ ⋀ undag ψ
  | ⌈α⌉ φ => ⌈α⌉ (undag φ)
  | ⌈α†⌉ φ => ⌈∗α⌉ (undag φ)

-- instance : Coe Nat Int := ⟨Int.ofNat⟩

@[simp]
def inject : Formula → DagFormula
  | ⊥ => ⊥
  | ~f => ~ inject f
  | ·c => ·c
  | φ⋀ψ => inject φ ⋀ inject ψ
  | ⌈α⌉φ => ⌈α⌉(inject φ)

-- | Borzechowski's f function, sort of.
@[simp]
def containsDag : DagFormula → Bool
  | ⊥ => False
  | ~f => containsDag f
  | ·_ => False
  | φ⋀ψ => containsDag φ ∧ containsDag ψ
  | ⌈_⌉φ => containsDag φ
  | ⌈_†⌉ _ => True

@[simp]
lemma undag_inject {f} : undag (inject f) = f :=
  by
  cases f
  all_goals simp [undag]
  case neg f =>
    rw [@undag_inject f]
  case and f g =>
    rw [@undag_inject f]
    rw [@undag_inject g]
    exact ⟨rfl,rfl⟩
  case box a f =>
    apply undag_inject

@[simp]
lemma inject_never_containsDag : ∀ f, containsDag (inject f) = false :=
  by
  apply Formula.rec
  case bottom => simp
  case atom_prop => simp
  case neg =>
    intro f
    simp
  case and =>
    intro g h
    simp [containsDag]
    tauto
  case box =>
    intro a f
    simp
  -- The recursor introduces program cases which we do not care about.
  case motive_2 =>
    intro _
    exact True
  all_goals { simp }

-- MEASURE
@[simp]
def mOfDagFormula : DagFormula → Nat
    | ⊥ => 0
    | ~⊥ => 0
    | ·_ => 0 -- missing in borze?
    | ~·_ => 0
    | ~~φ => 1 + mOfDagFormula φ
    | φ⋀ψ => 1 + mOfDagFormula φ + mOfDagFormula ψ
    | ~φ⋀ψ => 1 + mOfDagFormula (~φ) + mOfDagFormula (~ψ)
    | ⌈α⌉ φ => mOfProgram α + mOfDagFormula φ
    | ⌈_†⌉φ => mOfDagFormula φ
    | ~⌈α⌉ φ => mOfProgram α + mOfDagFormula (~φ)
    | ~⌈_†⌉φ => mOfDagFormula (~φ)

-- Daggered Tableau

structure DagTabNode where
  fs : Finset Formula
  dfs : Finset DagFormula -- for diamond this is actually a singleton?
  deriving DecidableEq

inductive dagRule : DagTabNode → Finset (DagTabNode) → Type
  -- Diamond rules
  | notUndag (h : ((~⌈·A⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs ∪ {undag (~⌈·A⌉φ)}, X.dfs \ {~⌈·A⌉φ}⟩ }

  | notUnion {α β φ} (h : ((~⌈α⋓β⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, X.dfs \ {~⌈α ⋓ b⌉φ} ∪ {~⌈α⌉φ}⟩
              , ⟨X.fs, X.dfs \ {~⌈α ⋓ b⌉φ} ∪ {~⌈β⌉φ}⟩ }

  | notTest (h : ((⌈?'ψ⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs ∪ {ψ}, X.dfs \ {⌈?'ψ⌉φ} ∪ {φ}⟩ }

  | notSequence (h : ((~⌈α;'β⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, X.dfs \ {~⌈α⌉⌈b⌉φ}⟩ }

  | notStar (h : ((~⌈∗α⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, X.dfs \ {~⌈∗α⌉φ} ∪ {~⌈α⌉φ}⟩
              , ⟨X.fs, X.dfs \ {~⌈∗α⌉φ} ∪ {~⌈α⌉⌈α†⌉φ}⟩ }

  | notDag (h : ((~⌈α†⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X {  } -- ×, i.e. delete branch

  -- Box rules
  | undag (h : ((⌈·A⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs ∪ {undag (⌈·A⌉φ)}, X.dfs \ {⌈·A⌉φ}⟩ }

  | union {α β φ} (h : ((⌈α⋓β⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, X.dfs \ {⌈α ⋓ b⌉φ} ∪ {⌈α⌉φ, ⌈β⌉φ}⟩ }

  | test (h : ((⌈?'ψ⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs ∪ {~ψ}, X.dfs \ {⌈?'ψ⌉φ}⟩
              , ⟨X.fs, X.dfs \ {⌈?'ψ⌉φ} ∪ {φ}⟩ }

  | sequence (h : ((⌈α;'β⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, X.dfs \ {⌈α⌉⌈b⌉φ}⟩ }

  | star (h : ((~⌈∗α⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, X.dfs \ {~⌈∗α⌉φ} ∪ {~⌈α⌉φ}⟩
              , ⟨X.fs, X.dfs \ {~⌈∗α⌉φ} ∪ {~⌈α⌉⌈α†⌉φ}⟩ }

inductive DagTab : DagTabNode → Type
  | byRule {X B} (_ : dagRule X B) (next : ∀ Y ∈ B, DagTab Y) : DagTab X
  | stop {X} (_ : X.dfs = ∅) : DagTab X

def endNodesOf : DagTab X -> List (List Formula) := sorry -- TODO
--   (or have it -> List (DagTabNode) and prove that dfs will be empty?

-- Given a proper dagger formula, define the *unique* DagTab for it?
-- More generally, given a DagTabNode, how to continue?
def theTabFor (N : DagTabNode) : DagTab N := sorry

-- all weak successors of a node in a DagTab, i.e. itself, immediate and later successors.
def successors : (t : DagTab N) → Finset DagTabNode
  | @DagTab.byRule X B (_ : dagRule X B) next => {N} ∪ B.attach.biUnion (fun ⟨Y, h⟩ => successors (next Y h))
  | DagTab.stop _ => {N}

instance modelCanSemImplyDagTabNode {W : Type} : vDash (KripkeModel W × W) (DagTabNode) :=
  vDash.mk (λ ⟨M,w⟩ Δ => ∀ φ ∈ Δ.fs ∪ (Δ.dfs.image undag) , @evaluate W M w φ)


theorem notStarSoundness M (a : Program) (v w : W) (Δ : DagTabNode)
    (φ : DagFormula) (in_D : (~⌈a⌉φ) ∈ Δ.dfs) (t : DagTab Δ)
    -- TODO: containsDag φ -- needed?
    (v_D : (M, v) ⊨ Δ) (v_a_w : relate M a v w) (w_nP : (M, w) ⊨ (~undag φ)) :
    ∃ Γ ∈ successors t,
      (M, v) ⊨ Γ ∧ ( ( ∃ (a : Char) (as : List Program), (~ ⌈·a⌉⌈⌈as⌉⌉(undag φ)) ∈ Γ.fs
                       ∧ relate M (Program.steps ([Program.atom_prog a] ++ as)) v w )
                   ∨ ((~φ) ∈ Γ.dfs ∧ v = w) ) := by
  cases a
  case atom_prog A =>
    -- NOTE: do we really want Γ = Δ here, what about the step done by "undag" rule?
    use Δ
    constructor
    · cases t
      all_goals simp [successors]
    · constructor
      · assumption
      · left
        use A, []
        simp at *
        constructor
        ·
          -- TODO: by contradiction / do not allow A in dfs?
          sorry
        · exact v_a_w

  case sequence α β =>
    sorry

  case union α β =>
    -- NOTE: how to ensure that notUnion is "eventually" applied in t (: DagTab Δ)?
    -- May need to redefine DagTab to make it fully deterministic.
    -- That should work here, but probably not for boxes?
    simp at v_a_w
    cases v_a_w
    · have := notStarSoundness M α v w ?_ φ
      · sorry
      sorry
    · have := notStarSoundness M α v w ?_ φ
      · sorry
      sorry

  case star α =>
    sorry
 
  case test ψ =>
    sorry
