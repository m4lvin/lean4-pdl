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

-- Daggered Tableau, only for diamonds at the moment.

structure DagTabNode where
  fs : Finset Formula
  dfs : Option DagFormula -- for diamond this is a singleton, but box needs more here
  deriving DecidableEq

inductive dagRule : DagTabNode → Finset (DagTabNode) → Type
  -- Diamond rules
  | notUndag (h : ((~⌈·A⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs ∪ {undag (~⌈·A⌉φ)}, none⟩ }

  | notUnion {α β φ} (h : ((~⌈α⋓β⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, some (~⌈α⌉φ)⟩
              , ⟨X.fs, some (~⌈β⌉φ)⟩ }

  | notTest (h : ((⌈?'ψ⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs ∪ {ψ}, some φ⟩ }

  | notSequence (h : ((~⌈α;'β⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, none⟩ }

  | notStar (h : ((~⌈∗α⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X { ⟨X.fs, some (~φ)⟩
              , ⟨X.fs, some (~⌈α⌉⌈α†⌉φ)⟩ }

  | notDag (h : ((~⌈α†⌉φ : DagFormula) ∈ X.dfs)) :
    dagRule X {  } -- ×, i.e. delete branch

/-
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
    dagRule X { ⟨X.fs, X.dfs \ {~⌈∗α⌉φ} ∪ {~φ}⟩
              , ⟨X.fs, X.dfs \ {~⌈∗α⌉φ} ∪ {~⌈α⌉⌈α†⌉φ}⟩ }
-/

inductive DagTab : DagTabNode → Type
  | byRule {X B} (_ : dagRule X B) (next : ∀ Y ∈ B, DagTab Y) : DagTab X
  | stop {X} (_ : X.dfs = none) : DagTab X

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
  vDash.mk (λ ⟨M,w⟩ Δ => ∀ φ ∈ Δ.fs ∪ (Δ.dfs.map undag).toFinset, evaluate M w φ)


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

@[simp]
def dagNext : (Finset Formula × Option DagFormula) → Finset (Finset Formula × Option DagFormula)
  | (fs, some (~⌈·A⌉φ)) => { (fs ∪ {undag (~⌈·A⌉φ)}, none) }
  | (fs, some (~⌈α⋓β⌉φ)) => { (fs, some (~⌈α⌉φ))
                            , (fs, some (~⌈β⌉φ)) }
  | (fs, some (~⌈?'ψ⌉φ)) => { (fs ∪ {ψ}, some (~φ)) }
  | (fs, some (~⌈α;'β⌉φ)) => { (fs, some (~⌈α⌉⌈β⌉φ)) }
  | (fs, some (~⌈∗α⌉φ)) => { (fs, some (~φ))
                           , (fs, some (~⌈α⌉⌈α†⌉φ)) }
  | (_, some (~⌈_†⌉_)) => {  } -- delete branch
  | (_, some _) => { }  -- bad catch-all fallback, and maybe wrong?
  | (_, none) => { }  -- maybe wrong?

def dagNextTransRefl : (Finset Formula × Option DagFormula) → Finset (Finset Formula × Option DagFormula)
  | (fs, mdf) => {(fs,mdf)} ∪ ((dagNext (fs,mdf)).biUnion dagNextTransRefl)
decreasing_by sorry

inductive DagTabNext : (Finset Formula × Option DagFormula) → Type
  | step fs f (next : ∀ Y ∈ dagNext (fs, some f), DagTabNext Y) : DagTabNext (fs, some f)
  | stop fs : DagTabNext (fs, none)

instance modelCanSemImplyDagTabNodeNext {W : Type} : vDash (KripkeModel W × W) (Finset Formula × Option DagFormula) :=
  vDash.mk (λ ⟨M,w⟩ (fs, mf) => ∀ φ ∈ fs ∪ (mf.map undag).toFinset, evaluate M w φ)

-- all weak successors of a node in a DagTab, i.e. itself, immediate and later successors.
@[simp]
-- NOTE: do we actually need it to be reflexive?
def successorsNext : (t : DagTabNext N) → Finset (Finset Formula × Option DagFormula)
  | DagTabNext.step fs f next => {N} ∪ (dagNext (fs, some f)).attach.biUnion (fun ⟨Y, h⟩ => successorsNext (next Y h))
  | DagTabNext.stop _ => {N}


theorem notStarSoundnessNext (a : Program) M (v w : W) (fs)
    (φ : DagFormula)
    -- TODO: containsDag φ -- needed?
    (v_D : (M, v) ⊨ (fs, some (~⌈a⌉φ)))
    (v_a_w : relate M a v w)
    (w_nP : (M, w) ⊨ (~undag φ)) :
    ∃ Γ ∈ dagNextTransRefl (fs, ~⌈a⌉φ),
      (M, v) ⊨ Γ ∧ ( ( ∃ (a : Char) (as : List Program), (~ ⌈·a⌉⌈⌈as⌉⌉(undag φ)) ∈ Γ.1
                       ∧ relate M (Program.steps ([Program.atom_prog a] ++ as)) v w )
                   ∨ ((~φ) ∈ Γ.2 ∧ v = w) ) := by
  cases a
  case atom_prog A =>
    use (fs ∪ {undag (~⌈·A⌉φ)}, none) -- unique successor by the "undag" rule
    constructor
    · simp [dagNextTransRefl,successorsNext]
    · constructor
      · intro f
        aesop
      · left
        use A, []
        simp at *
        constructor
        · right
          simp [undag]
        · exact v_a_w

  case star β =>
    simp at v_a_w
    have := starCases v_a_w
    cases this
    case inl v_is_w =>
      use (fs, some (~φ))
      constructor
      · rw [dagNextTransRefl]
        simp
        right
        rw [dagNextTransRefl]
        simp
      · constructor
        · intro f
          aesop
        · right
          aesop
    case inr claim =>
      -- Here we follow the (fs, some (~⌈β⌉⌈β†⌉φ)) branch.
      rcases claim with ⟨v_neq_w, ⟨u, v_neq_u, v_b_u, u_bS_w⟩⟩
      have := notStarSoundnessNext β M v u fs (⌈β†⌉φ)
      specialize this _ v_b_u _
      · sorry -- should be easy?
      · sorry -- should be easy
      rcases this with ⟨Γ, Γ_in, v_Γ, split⟩
      use Γ
      cases split
      case inl one =>
        constructor
        · rw [dagNextTransRefl]; simp; tauto
        · constructor
          · exact v_Γ
          · simp
            left
            simp [undag] at one
            rcases one with ⟨a,as,aasbs_in_Γ, y, a_v_y, y_as_u⟩
            use a, as ++ [∗β]
            constructor
            · sorry -- should be easy
            · use y
              constructor
              · assumption
              · simp [relate_steps]
                use u
      case inr two =>
        absurd two.right
        simp at v_neq_u
        exact v_neq_u

  case sequence α β =>
    sorry -- TODO

  case union α β =>
    simp at v_a_w
    cases v_a_w
    case inl v_a_w =>
      have := notStarSoundnessNext α M v w fs φ
      specialize this _ v_a_w w_nP
      · intro f
        simp
        rintro (f_in_fs | fDef)
        · exact v_D f (by aesop)
        · subst fDef
          simp only [evaluate, not_forall, exists_prop, undag]
          use w
          simp [modelCanSemImplyForm,vDash] at w_nP
          tauto
      rcases this with ⟨Γ, Γ_in, v_Γ, split⟩
      use Γ
      constructor
      · rw [dagNextTransRefl]; simp; tauto
      · exact ⟨v_Γ, split⟩
    case inr v_b_w => -- completely analogous
      have := notStarSoundnessNext β M v w fs φ
      specialize this _ v_b_w w_nP
      · intro f
        simp
        rintro (f_in_fs | fDef)
        · exact v_D f (by aesop)
        · subst fDef
          simp only [evaluate, not_forall, exists_prop, undag]
          use w
          simp [modelCanSemImplyForm,vDash] at w_nP
          tauto
      rcases this with ⟨Γ, Γ_in, v_Γ, split⟩
      use Γ
      constructor
      · rw [dagNextTransRefl]; simp; tauto
      · exact ⟨v_Γ, split⟩

  case test ψ =>
    use (fs ∪ {ψ}, some (~φ)) -- unique successor by the "undag" rule
    constructor
    · rw [dagNextTransRefl]
      simp [successorsNext]
      right
      rw [dagNextTransRefl]
      simp
    · constructor
      · intro f; aesop
      · right; aesop


termination_by
  notStarSoundnessNext α M v w fs φ v_D v_a_w w_nP => mOfProgram α


-- Box notes for later:

-- how to ensure that union rule is "eventually" applied?
-- May need to redefine DagTab to make it fully deterministic, even in box cases?
-- Was not a problem for diamonds above.
