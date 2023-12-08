import Mathlib.Data.Finset.Basic

import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics
import Pdl.Star
import Pdl.Closure

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

def mOfDagNode : (Finset Formula × Option DagFormula) → ℕ
  | ⟨_, none⟩ => 0
  | ⟨_, some df⟩ => 1 + mOfDagFormula df

-- -- -- DIAMONDS -- -- --

-- Immediate sucessors of a node in a Daggered Tableau, for diamonds.
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

theorem mOfDagNode.isDec (x y : Finset Formula × Option DagFormula) (y_in : y ∈ dagNext x) :
    mOfDagNode y < mOfDagNode x := by
  rcases x with ⟨_, _|dfx⟩
  case none =>
    simp [mOfDagNode]
    cases y_in
  case some =>
    simp [mOfDagNode]
    rcases y with ⟨_, _|dfy⟩
    case none =>
      simp
    case some =>
      simp
      cases dfx
      all_goals (try simp [dagNext]; try cases y_in)
      case neg g =>
        cases g
        all_goals (try simp [dagNext]; try cases y_in)
        case box a =>
          cases a
          all_goals (cases dfy)
          all_goals (simp [dagNext])
          all_goals sorry
          -- There must be a nicer way to do this?!

@[simp]
def dagNextTransRefl : (Finset Formula × Option DagFormula) → Finset (Finset Formula × Option DagFormula) :=
  ftr dagNext instDecidableEqProd mOfDagNode mOfDagNode.isDec

instance modelCanSemImplyDagTabNodeNext {W : Type} : vDash (KripkeModel W × W) (Finset Formula × Option DagFormula) :=
  vDash.mk (λ ⟨M,w⟩ (fs, mf) => ∀ φ ∈ fs ∪ (mf.map undag).toFinset, evaluate M w φ)

theorem notStarSoundnessAux (a : Program) M (v w : W) (fs)
    (φ : DagFormula)
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
    · unfold dagNextTransRefl; rw [ftr.iff]; right; simp; rw [ftr.iff]; simp
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
      · unfold dagNextTransRefl; rw [ftr.iff]; right; simp; rw [ftr_iff]; simp
      · constructor
        · intro f
          aesop
        · right
          aesop
    case inr claim =>
      -- Here we follow the (fs, some (~⌈β⌉⌈β†⌉φ)) branch.
      rcases claim with ⟨v_neq_w, ⟨u, v_neq_u, v_b_u, u_bS_w⟩⟩
      have := notStarSoundnessAux β M v u fs (⌈β†⌉φ)
      specialize this _ v_b_u _
      · sorry -- should be easy?
      · sorry -- should be easy
      rcases this with ⟨Γ, Γ_in, v_Γ, split⟩
      use Γ
      cases split
      case inl one =>
        constructor
        · unfold dagNextTransRefl; rw [ftr.iff]; simp; tauto
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

  case sequence β γ =>
    simp at v_a_w
    rcases v_a_w with ⟨u, v_β_u, u_γ_w⟩
    have u_nGphi : (M,u) ⊨ (~⌈γ⌉undag φ) := by sorry -- should be easy
    have := notStarSoundnessAux β M v u fs (⌈γ⌉φ)
    specialize this _ v_β_u u_nGphi
    · intro f
      simp
      intro f_in
      sorry -- should be easy
    rcases this with ⟨S, S_in, v_S, (⟨a,as,aasG_in_S,v_aas_u⟩ | ⟨ngPhi_in_S, v_is_u⟩)⟩ -- Σ
    · use S -- "If (1), then we are done."
      constructor
      · unfold dagNextTransRefl; rw [ftr.iff]; simp; tauto
      · constructor
        · exact v_S
        · left
          simp
          use a, as ++ [γ]
          constructor
          · simp [undag] at  aasG_in_S
            rw [boxes_last]
            exact aasG_in_S
          · simp at v_aas_u
            rcases v_aas_u with ⟨y, v_a_y, y_asg_w⟩
            use y
            rw [relate_steps]
            constructor
            · exact v_a_y
            · use u
              aesop
    · -- TODO "If (2) ..."
      -- subst v_is_u
      have := notStarSoundnessAux γ M u w S.1 φ -- not use "fs" here!
      specialize this _ u_γ_w w_nP
      · intro f
        sorry -- should be easy
      rcases this with ⟨Γ, Γ_in, v_Γ, split⟩
      -- need transitivity here
      have also_in_prev : Γ ∈ dagNextTransRefl (fs, some (~⌈β;'γ⌉φ)) := by
        apply ftr.Trans Γ S (fs, some (~⌈β;'γ⌉φ))
        · convert Γ_in
        · rw [ftr.iff]; simp; right; exact S_in
      use Γ
      subst v_is_u
      constructor
      · exact also_in_prev
      · constructor
        · exact v_Γ
        · tauto --

  case union α β =>
    simp at v_a_w
    cases v_a_w
    case inl v_a_w =>
      have := notStarSoundnessAux α M v w fs φ
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
      · unfold dagNextTransRefl; rw [ftr.iff]; simp; tauto
      · exact ⟨v_Γ, split⟩
    case inr v_b_w => -- completely analogous
      have := notStarSoundnessAux β M v w fs φ
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
      · unfold dagNextTransRefl; rw [ftr.iff]; simp; tauto
      · exact ⟨v_Γ, split⟩

  case test ψ =>
    use (fs ∪ {ψ}, some (~φ)) -- unique successor
    constructor
    · unfold dagNextTransRefl; rw [ftr.iff]; right; simp; rw [ftr.iff]; simp
    · constructor
      · intro f; aesop
      · right; aesop


termination_by
  notStarSoundnessAux α M v w fs φ v_D v_a_w w_nP => mOfProgram α


-- -- -- BOXES -- -- --

-- Notes for later:
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



-- how to ensure that union rule is "eventually" applied?
-- May need to redefine DagTab to make it fully deterministic, even in box cases?
-- Was not a problem for diamonds above.
