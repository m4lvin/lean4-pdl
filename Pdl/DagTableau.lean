import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics
import Pdl.Star
import Pdl.Closure

inductive DagFormula : Type
  | dag : Program → Formula → DagFormula
  | box : Program → DagFormula → DagFormula
  deriving Repr, DecidableEq

@[simp]
def DagFormula.boxes : List Program → DagFormula → DagFormula
  | [], f => f
  | (p :: ps), f => DagFormula.box p (DagFormula.boxes ps f)

inductive NegDagFormula : Type
  | neg : DagFormula → NegDagFormula
  deriving Repr, DecidableEq

local notation "⌈" a "†⌉" f => DagFormula.dag a f
local notation "⌈" a "⌉" df => DagFormula.box a df
local notation "⌈⌈" ps "⌉⌉" df => DagFormula.boxes ps df

local notation "~" df => NegDagFormula.neg df

-- Borzechowski's function "f".
class Undag (α : Type) where
  undag : α → Formula

open Undag

@[simp]
def undagDagFormula
  | (⌈a†⌉f) => (Formula.box (∗a) f)
  | (⌈p⌉df) => (Formula.box p (undagDagFormula df))

@[simp]
instance UndagDagFormula : Undag DagFormula := Undag.mk undagDagFormula

@[simp]
def undagNegDagFormula : NegDagFormula → Formula
  | (~ df) => ~ undag df
@[simp]
instance UndagNegDagFormula : Undag NegDagFormula := Undag.mk undagNegDagFormula

@[simp]
def inject : List Program → Program → Formula → DagFormula
  | ps, a, f => (DagFormula.boxes ps (DagFormula.dag a f))

@[simp]
theorem undag_boxes : undagDagFormula (⌈⌈ps⌉⌉df) = ⌈⌈ps⌉⌉(undag df) :=
  by
  cases ps
  simp
  simp
  apply undag_boxes

@[simp]
lemma undag_inject {f} : undag (inject ps a f) = (⌈⌈ps⌉⌉(⌈∗ a⌉f)) :=
  by
  simp

-- MEASURE
@[simp]
def mOfDagFormula : DagFormula → Nat
  | ⌈_†⌉_ => 0 -- TO CHECK: is this correct?
  | ⌈a⌉df => mOfProgram a + mOfDagFormula df

@[simp]
def mOfNegDagFormula : NegDagFormula → Nat
  | ~df => mOfDagFormula df

def mOfDagNode : Finset Formula × Option NegDagFormula → ℕ
  | ⟨_, none⟩ => 0
  | ⟨_, some df⟩ => 1 + mOfNegDagFormula df

-- -- -- DIAMONDS -- -- --

-- Immediate sucessors of a node in a Daggered Tableau, for diamonds.
@[simp]
def dagNext : (Finset Formula × Option NegDagFormula) → Finset (Finset Formula × Option NegDagFormula)
  | (fs, some (~⌈·A⌉df)) => { (fs ∪ {undag (~⌈·A⌉df)}, none) }
  | (fs, some (~⌈α⋓β⌉df)) => { (fs, some (~⌈α⌉df))
                            , (fs, some (~⌈β⌉df)) }
  | (fs, some (~⌈?'ψ⌉df)) => { (fs ∪ {ψ}, some (~df)) }
  | (fs, some (~⌈α;'β⌉df)) => { (fs, some (~⌈α⌉⌈β⌉df)) }
  | (fs, some (~⌈∗α⌉df)) => { (fs, some (~df))
                            , (fs, some (~⌈α⌉⌈α†⌉(undag df))) } -- only have one (top most) dagger at a time
  | (_, some (~⌈_†⌉_)) => {  } -- delete branch
  -- | (_, some _) => { }  -- bad catch-all fallback, and maybe wrong? -- Yeah, no more needed now :-)
  | (_, none) => { }  -- maybe wrong?

theorem mOfDagNode.isDec {x y : Finset Formula × Option NegDagFormula} (y_in : y ∈ dagNext x) :
    mOfDagNode y < mOfDagNode x := by
  rcases x with ⟨_, _|dfx⟩
  case none =>
    simp [mOfDagNode]
    cases y_in
  case some =>
    simp [mOfDagNode]
    rcases y with ⟨_, _|dfy⟩
    all_goals simp
    case some =>
      cases dfx
      all_goals (try cases y_in)
      case neg g =>
        cases g
        all_goals (try cases y_in)
        case box a f =>
          cases a
          all_goals (simp [dagNext] at *)
          case sequence =>
            rcases y_in with ⟨l,r⟩
            subst l
            subst r
            simp
            linarith
          case union a b =>
            rcases y_in with ⟨l,r⟩|⟨l,r⟩
            all_goals (subst l; subst r; simp; linarith)
          case star a =>
            rcases y_in with ⟨l,r⟩|⟨l,r⟩
            all_goals (subst l; subst r; simp <;> linarith)
          case test f =>
            rcases y_in with ⟨l,r⟩
            subst l
            subst r
            simp

@[simp]
def dagNextTransRefl : (Finset Formula × Option NegDagFormula) → Finset (Finset Formula × Option NegDagFormula) :=
  ftr dagNext instDecidableEqProd mOfDagNode @mOfDagNode.isDec

instance modelCanSemImplyDagTabNode {W : Type} : vDash (KripkeModel W × W) (Finset Formula × Option NegDagFormula) :=
  vDash.mk (λ ⟨M,w⟩ (fs, mf) => ∀ φ ∈ fs ∪ (mf.map undag).toFinset, evaluate M w φ)

-- Similar to Borzechowski's Lemma 4
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
        specialize v_D f
        aesop
      · left
        use A, []
        simp at *
        exact v_a_w

  case star β =>
    simp at v_a_w
    have := starCases v_a_w
    cases this
    case inl v_is_w =>
      use (fs, some (~φ))
      constructor
      · unfold dagNextTransRefl; rw [ftr.iff]; right; simp; rw [ftr.iff]; simp
      · constructor
        · intro f
          specialize v_D f
          sorry -- was: aesop
        · right
          aesop
    case inr claim =>
      -- Here we follow the (fs, some (~⌈β⌉⌈β†⌉φ)) branch.
      rcases claim with ⟨v_neq_w, ⟨u, v_neq_u, v_b_u, u_bS_w⟩⟩
      have := notStarSoundnessAux β M v u fs (⌈β†⌉(undag φ))
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
    · -- "If (2) ..."
      have := notStarSoundnessAux γ M u w S.1 φ -- not use "fs" here!
      specialize this _ u_γ_w w_nP
      · intro f
        sorry -- should be easy
      rcases this with ⟨Γ, Γ_in, v_Γ, split⟩
      have also_in_prev : Γ ∈ dagNextTransRefl (fs, some (~⌈β;'γ⌉φ)) := by
        -- Here we use transitivity of "being a successor" in a dagger tableau.
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
      · intro f f_in
        simp at *
        cases f_in
        · apply v_D
          simp
          tauto
        · specialize v_D (~⌈?'ψ⌉undagDagFormula φ)
          simp at v_D
          aesop
      · right; aesop

termination_by
  notStarSoundnessAux α M v w fs φ v_D v_a_w w_nP => mOfProgram α

def dagEndNodes : (Finset Formula × Option NegDagFormula) → Finset (Finset Formula)
  | (fs, none) => { fs }
  | (fs, some df) => (dagNext (fs, some df)).attach.biUnion
      (fun ⟨gsdf, h⟩ =>
        have : mOfDagNode gsdf < mOfDagNode (fs, some df) := mOfDagNode.isDec h
        dagEndNodes gsdf)
termination_by
  dagEndNodes fs => mOfDagNode fs
decreasing_by simp_wf; assumption

theorem dagEnd_subset_next :
    Ω ∈ dagNext Γ → dagEndNodes Ω ⊆ dagEndNodes Γ := by
  sorry

theorem dagEnd_subset_trf {Ω Γ} :
    Ω ∈ dagNextTransRefl Γ → dagEndNodes Ω ⊆ dagEndNodes Γ := by
  intro O_in
  unfold dagNextTransRefl at O_in
  rw [ftr.iff] at O_in
  cases O_in
  · aesop
  case inr hyp =>
    rcases hyp with ⟨S, S_in, O_in⟩
    have := dagEnd_subset_next S_in
    have := dagEnd_subset_trf O_in
    tauto
termination_by
  dagEnd_subset_trf Ω Γ hyp  => mOfDagNode Γ
decreasing_by simp_wf; apply mOfDagNode.isDec; assumption

-- Similar to Borzechowski's Lemma 5
-- (This is actually soundness AND invertibility.)
theorem notStarSoundness (M : KripkeModel W) (v : W) S
    :
    (M, v) ⊨ S ↔ ∃ Γ ∈ dagEndNodes S, (M, v) ⊨ Γ := by
  constructor
  · intro lhs -- left to right: soundness
    rcases S with ⟨S, none|ndf⟩
    · simp [dagEndNodes]
      intro f
      simp [modelCanSemImplyDagTabNode] at lhs
      apply lhs
    · cases ndf
      case neg f =>
        cases f
        case box a g =>
            have := lhs (undag (~⌈a⌉g))
            simp [undag] at this
            rcases this with ⟨w, v_aS_w, w_nPhi⟩
            -- Now apply Lemma 4
            have := notStarSoundnessAux a M v w S g lhs v_aS_w
            specialize this _
            · simp [modelCanSemImplyForm, undag]
              exact w_nPhi
            rcases this with ⟨Ω, O_in_trf, v_O, whatever⟩

            -- ALTERNATIVE: distinguish the cases of "whatever" here?

            -- NOTE: Now we do induction within notStarSoundness!
            rw [notStarSoundness M v Ω] at v_O
            -- PROBLEM: for termination we must avoid the case where Ω is the same as S :-/

            rcases v_O with ⟨Γ, foo⟩
            use Γ
            constructor
            · apply dagEnd_subset_trf -- this is what connects trf and endNodes
              exact O_in_trf
              tauto
            · tauto

        case dag a f =>
            simp [dagEndNodes]
            -- False -- BIG PROBLEM: What if undag is applied to S itself?
            sorry

  · rintro ⟨Γ, Γ_in, v_Γ⟩ -- right to left: inveritbility
    intro f f_in
    simp at f_in
    cases f_in
    ·
      sorry
    ·
      sorry
termination_by
  notStarSoundness M v S => mOfDagNode S
decreasing_by simp_wf; apply mOfDagNode.isDec; sorry -- assumption



-- -- -- BOXES -- -- --

-- Here we need a List DagFormula, because of the ⋓ rule.

-- Immediate sucessors of a node in a Daggered Tableau, for diamonds.
@[simp]
def boxDagNext : (Finset Formula × List DagFormula) → Finset (Finset Formula × List DagFormula)
  | (fs, (⌈·A⌉φ)::rest) => { (fs ∪ {undag (⌈·A⌉φ)}, rest) }
  | (fs, (⌈α⋓β⌉φ)::rest) => { (fs, (⌈α⌉φ)::(⌈β⌉φ)::rest ) }
  | (fs, (⌈?'ψ⌉φ)::rest) => { (fs ∪ {~ψ}, rest)
                            , (fs, φ::rest) }
  | (fs, (⌈α;'β⌉φ)::rest) => { (fs, (⌈α⌉⌈β⌉φ)::rest) }
  | (fs, (⌈∗α⌉φ)::rest) => { (fs, φ::(⌈α⌉⌈α†⌉(undag φ))::rest) } -- NOT splitting!
  | (fs, (⌈_†⌉_)::rest) => { (fs, rest) } -- delete formula, but keep branch!
  | (_, []) => { }  -- maybe wrong? no, good that we stop!

instance modelCanSemImplyBoxDagTabNode {W : Type} : vDash (KripkeModel W × W) (Finset Formula × List DagFormula) :=
  vDash.mk (λ ⟨M,w⟩ (fs, mf) => ∀ φ ∈ fs ∪ (mf.map undag).toFinset, evaluate M w φ)

def mOfBoxDagNode : (Finset Formula × List DagFormula) → ℕ
  | ⟨_, []⟩ => 0
  | ⟨_, dfs⟩ => 1 + (dfs.map mOfDagFormula).sum

theorem mOfBoxDagNode.isDec {x y : Finset Formula × List DagFormula} (y_in : y ∈ boxDagNext x) :
    mOfBoxDagNode y < mOfBoxDagNode x := by sorry

def boxDagEndNodes : (Finset Formula × List DagFormula) → Finset (Finset Formula)
  | (fs, []) => { fs }
  | (fs, df::rest) => (boxDagNext (fs, df::rest)).attach.biUnion
      (fun ⟨gsdf, h⟩ =>
        have : mOfBoxDagNode gsdf < mOfBoxDagNode (fs, df::rest) := mOfBoxDagNode.isDec h
        boxDagEndNodes gsdf)
termination_by
  boxDagEndNodes fs => mOfBoxDagNode fs
decreasing_by simp_wf; assumption

-- how to ensure that union rule is "eventually" applied?
-- May need to redefine DagTab to make it fully deterministic, even in box cases?
-- Was not a problem for diamonds above.

-- Analogon of Borzechowski's Lemma 5 for boxes, was missing.
-- (This is actually soundness AND invertibility.)
theorem starSoundness (M : KripkeModel W) (v : W) :
    (M, v) ⊨ S ↔ ∃ Γ ∈ boxDagEndNodes S, (M, v) ⊨ Γ := by
  sorry
