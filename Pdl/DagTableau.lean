import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics
import Pdl.Star
import Pdl.Closure

inductive DagFormula : Type
  | dag : Program → Formula → DagFormula -- ⌈α†⌉φ
  | box : Program → DagFormula → DagFormula  -- ⌈α⌉ψ
  deriving Repr, DecidableEq

@[simp]
def DagFormula.boxes : List Program → DagFormula → DagFormula
  | [], ψ => ψ
  | (α :: rest), ψ => DagFormula.box α (DagFormula.boxes rest ψ)

inductive NegDagFormula : Type
  | neg : DagFormula → NegDagFormula
  deriving Repr, DecidableEq

local notation "⌈" α "†⌉" φ => DagFormula.dag α φ
local notation "⌈" α "⌉" ψ => DagFormula.box α ψ
local notation "⌈⌈" ps "⌉⌉" df => DagFormula.boxes ps df

local notation "~" ψ => NegDagFormula.neg ψ

-- Borzechowski's function "f".
class Undag (α : Type) where
  undag : α → Formula

open Undag

@[simp]
def undagDagFormula
  | (⌈α†⌉f) => (Formula.box (∗α) f)
  | (⌈α⌉df) => (Formula.box α (undagDagFormula df))

@[simp]
instance UndagDagFormula : Undag DagFormula := Undag.mk undagDagFormula

@[simp]
def undagNegDagFormula : NegDagFormula → Formula
  | (~ ψ) => ~ undag ψ
@[simp]
instance UndagNegDagFormula : Undag NegDagFormula := Undag.mk undagNegDagFormula

@[simp]
def inject : List Program → Program → Formula → DagFormula
  | ps, α, φ => (DagFormula.boxes ps (DagFormula.dag α φ))

@[simp]
theorem undag_boxes : undagDagFormula (⌈⌈ps⌉⌉df) = ⌈⌈ps⌉⌉(undag df) :=
  by
  cases ps
  simp
  simp
  apply undag_boxes

@[simp]
lemma undag_inject {φ} : undag (inject ps α φ) = (⌈⌈ps⌉⌉(⌈∗ α⌉φ)) :=
  by
  simp

-- MEASURE
@[simp]
def mOfDagFormula : DagFormula → Nat
  | ⌈_†⌉_ => 0 -- TO CHECK: is this correct?
  | ⌈α⌉ψ => mOfProgram α + mOfDagFormula ψ

instance : LT DagFormula := ⟨λ ψ1 ψ2 => mOfDagFormula ψ1 < mOfDagFormula ψ2⟩

def mOfDagNode : Finset Formula × Option NegDagFormula → ℕ
  | ⟨_, none⟩ => 0
  | ⟨_, some (~ψ)⟩ => 1 + mOfDagFormula ψ

-- -- -- DIAMONDS -- -- --

-- Immediate sucessors of a node in a Daggered Tableau, for diamonds.
@[simp]
def dagNext : (Finset Formula × Option NegDagFormula) → Finset (Finset Formula × Option NegDagFormula)
  | (fs, some (~⌈·a⌉ψ)) => { (fs ∪ {undag (~⌈·a⌉ψ)}, none) }
  | (fs, some (~⌈α⋓β⌉ψ)) => { (fs, some (~⌈α⌉ψ))
                            , (fs, some (~⌈β⌉ψ)) }
  | (fs, some (~⌈?'φ⌉ψ)) => { (fs ∪ {φ}, some (~ψ)) }
  | (fs, some (~⌈α;'β⌉ψ)) => { (fs, some (~⌈α⌉⌈β⌉ψ)) }
  | (fs, some (~⌈∗α⌉ψ)) => { (fs, some (~ψ))
                            , (fs, some (~⌈α⌉⌈α†⌉(undag ψ))) } -- only keep top-most dagger
  | (_, some (~⌈_†⌉_)) => {  } -- delete branch
  | (_, none) => { } -- end node of dagger tableau

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
                       ∧ relate M (Program.steps ([Program.atom_prog a] ++ as)) v w
                       ∧ Γ.2 = none )
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
      subst v_is_w
      use (fs, some (~φ))
      constructor
      · unfold dagNextTransRefl; rw [ftr.iff]; right; simp; rw [ftr.iff]; simp
      · constructor
        · intro f
          specialize v_D f
          intro f_in
          simp at f_in
          cases f_in
          · aesop
          case inr f_def =>
            subst f_def
            apply w_nP
        · right
          aesop
    case inr claim =>
      -- Here we follow the (fs, some (~⌈β⌉⌈β†⌉φ)) branch.
      rcases claim with ⟨_, ⟨u, v_neq_u, v_b_u, u_bS_w⟩⟩
      have := notStarSoundnessAux β M v u fs (⌈β†⌉(undag φ))
      specialize this _ v_b_u _
      · simp [modelCanSemImplyDagTabNode]
        intro f f_in
        simp [modelCanSemImplyForm] at *
        cases f_in
        case inl f_in =>
          apply v_D
          simp
          left
          assumption
        case inr f_eq =>
          subst f_eq
          simp
          use u
          constructor
          · exact v_b_u
          · use w
      · simp [modelCanSemImplyForm] at *
        use w
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
            rcases one with ⟨a, as, ⟨aasbs_in_, ⟨⟨y, a_v_y, y_as_u⟩, Γ_normal⟩⟩⟩
            use a, as ++ [∗β]
            constructor
            · rw [boxes_append]
              exact aasbs_in_
            · constructor
              · use y
                constructor
                · assumption
                · simp [relate_steps]
                  use u
              · assumption
      case inr two =>
        absurd two.right
        simp at v_neq_u
        exact v_neq_u

  case sequence β γ =>
    simp at v_a_w
    rcases v_a_w with ⟨u, v_β_u, u_γ_w⟩
    have u_nGphi : (M,u) ⊨ (~⌈γ⌉undag φ) := by
      simp [modelCanSemImplyForm] at *
      use w
    have := notStarSoundnessAux β M v u fs (⌈γ⌉φ)
    specialize this _ v_β_u u_nGphi
    · intro f
      simp
      intro f_in
      cases f_in
      case inl f_in =>
        apply v_D
        simp
        exact Or.inl f_in
      case inr f_eq =>
        rw [f_eq]
        simp
        simp [modelCanSemImplyForm] at u_nGphi
        use u
    rcases this with ⟨S, S_in, v_S, (⟨a,as,aasG_in_S,v_aas_u,Γ_normal⟩ | ⟨ngPhi_in_S, v_is_u⟩)⟩ -- Σ
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
            constructor
            · use y
              rw [relate_steps]
              constructor
              · exact v_a_y
              · use u
                aesop
            · assumption
    · -- "If (2) ..."
      have := notStarSoundnessAux γ M u w S.1 φ -- not use "fs" here!
      specialize this _ u_γ_w w_nP
      · intro f
        simp
        intro f_in
        cases f_in
        case inl f_in =>
          rw [v_is_u] at v_S
          apply v_S
          simp
          exact Or.inl f_in
        case inr f_eq =>
          rw [f_eq]
          exact u_nGphi
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

theorem dagEnd_subset_next
    (O_in : Ω ∈ dagNext Γ) : dagEndNodes Ω ⊆ dagEndNodes Γ := by
  intro e
  rcases Γ with ⟨fs, mdf⟩
  rcases mdf with none | ⟨df⟩
  · simp [dagNext] at O_in
  · intro e_in
    unfold dagEndNodes
    simp
    simp at O_in
    use Ω.1
    use Ω.2

theorem dagEndOfSome_iff_step : Γ ∈ dagEndNodes (fs, some (~⌈a⌉f)) ↔
    ∃ S ∈ dagNext (fs, some (~⌈a⌉f)), Γ ∈ dagEndNodes S := by
  cases a
  all_goals try (simp [dagEndNodes]; done)
  case union a b =>
    constructor
    · intro lhs
      simp [dagNext]
      unfold dagEndNodes at lhs
      simp at lhs
      cases lhs
      · left
        tauto
      case inr hyp =>
        rcases hyp with ⟨fs, mdf, claim⟩
        aesop
    · intro rhs
      rcases rhs with ⟨S, S_in, Γ_in⟩
      exact dagEnd_subset_next S_in Γ_in
  case star a => -- exact same as union case
    constructor
    · intro lhs
      simp [dagNext]
      unfold dagEndNodes at lhs
      simp at lhs
      cases lhs
      · left
        tauto
      case inr hyp =>
        rcases hyp with ⟨fs, mdf, claim⟩
        aesop
    · intro rhs
      rcases rhs with ⟨S, S_in, Γ_in⟩
      exact dagEnd_subset_next S_in Γ_in

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

-- A normal successor in a diamond dagger tableau is an end node.
theorem dagNormal_is_dagEnd
    (Γ_in : Γ ∈ dagNextTransRefl S)
    (Γ_normal : Γ.2 = none)
    :
    (Γ.1 ∈ dagEndNodes S) := by
  have := dagEnd_subset_trf Γ_in
  apply this
  rcases Γ with ⟨fs,odf⟩
  subst Γ_normal
  simp [dagEndNodes]

theorem notStarInvertAux (M : KripkeModel W) (v : W) S :
    (∃ Γ ∈ dagNext S, (M, v) ⊨ Γ) → (M, v) ⊨ S := by
  intro hyp
  rcases hyp with ⟨Γ, Γ_in, v_Γ⟩
  rcases S with ⟨fs, none | ⟨⟨df⟩⟩⟩
  · simp [dagNext] at Γ_in
  · cases df
    case box a df =>
      cases a
      all_goals (simp at Γ_in; try cases Γ_in; all_goals try subst Γ_in)
      all_goals (intro f f_in; simp at f_in)
      case atom_prog =>
        cases f_in
        · apply v_Γ; simp at *; tauto
        case inr hyp => subst hyp; apply v_Γ; simp
      case sequence a b =>
        cases f_in
        · apply v_Γ; simp at *; tauto
        case inr hyp => subst hyp; specialize v_Γ (~⌈a⌉⌈b⌉(undag df)); aesop
      case union.inl a b Γ_is =>
        cases f_in
        · apply v_Γ; simp at *; aesop
        case inr hyp => subst hyp; specialize v_Γ (~⌈a⌉(undag df)); aesop
      case union.inr a b Γ_is =>
        cases f_in
        · apply v_Γ; simp at *; aesop
        case inr hyp => subst hyp; specialize v_Γ (~⌈b⌉(undag df)); aesop
      case star.inl a Γ_is =>
        cases f_in
        · apply v_Γ; simp at *; aesop
        case inr hyp =>
          subst hyp; subst Γ_is; specialize v_Γ (undag (~df)); simp at *
          use v
      case star.inr a Γ_is =>
        cases f_in
        · apply v_Γ; subst Γ_is; simp at *; aesop
        case inr hyp =>
          subst hyp; subst Γ_is;
          specialize v_Γ (~⌈a⌉⌈∗a⌉(undag df))
          simp at *
          rcases v_Γ with ⟨x, v_a_x, y, x_aS_y, y_nf⟩
          use y
          exact ⟨Relation.ReflTransGen.head v_a_x x_aS_y, y_nf⟩
      case test.refl g =>
        cases f_in
        · apply v_Γ; simp at *; aesop
        case inr hyp =>
          subst hyp
          simp
          constructor
          · specialize v_Γ g; aesop
          · specialize v_Γ (~(undag df)); simp at v_Γ; aesop
    case dag =>
      simp [dagNext] at Γ_in

-- Invertibility for nSt
theorem notStarInvert (M : KripkeModel W) (v : W) S
    :
    (∃ Γ ∈ dagEndNodes S, (M, v) ⊨ Γ) → (M, v) ⊨ S := by
  rintro ⟨Γ, Γ_in, v_Γ⟩
  rcases S_eq : S with ⟨fs, mdf⟩ -- explicit hypotheses in rcases are needed to prove termination
  subst S_eq
  cases mdf_eq : mdf
  case none =>
    subst mdf
    simp [dagEndNodes] at Γ_in
    subst Γ_in
    simp [modelCanSemImplyDagTabNode]
    exact v_Γ
  case some ndf =>
    subst mdf
    rcases ndf_eq : ndf with ⟨df⟩
    subst ndf_eq
    cases df_eq : df
    case dag =>
      subst df_eq
      simp [dagEndNodes] at Γ_in
    case box a f =>
      subst df_eq
      rw [dagEndOfSome_iff_step] at Γ_in
      rcases Γ_in with ⟨T, T_in, Γ_in⟩
      have v_T := notStarInvert M v T ⟨Γ, ⟨Γ_in, v_Γ⟩⟩ -- recursion!
      exact notStarInvertAux M v (fs , ~⌈a⌉f) ⟨_, ⟨T_in, v_T⟩⟩
termination_by
  notStarInvert M v S claim => mOfDagNode S
decreasing_by simp_wf; apply mOfDagNode.isDec; aesop


-- -- -- BOXES -- -- --

-- Here we need a List DagFormula, because of the ⋓ rule.

def mOfBoxDagNode : (Finset Formula × List DagFormula) → ℕ
  | ⟨_, []⟩ => 0
  | ⟨_, dfs⟩ => 1 + (dfs.map mOfDagFormula).sum + (dfs.map mOfDagFormula).length

-- Immediate sucessors of a node in a Daggered Tableau, for boxes.
-- Note that this is still fully deterministic.
@[simp]
def boxDagNext : (Finset Formula × List DagFormula) → Finset (Finset Formula × List DagFormula)
  | (fs, (⌈·A⌉φ)::rest) => { (fs ∪ {undag (⌈·A⌉φ)}, rest) }
  | (fs, (⌈α⋓β⌉φ)::rest) => { (fs, (⌈α⌉φ)::(⌈β⌉φ)::rest ) }
  | (fs, (⌈?'ψ⌉φ)::rest) => { (fs ∪ {~ψ}, rest)
                            , (fs, φ::rest) }
  | (fs, (⌈α;'β⌉φ)::rest) => { (fs, (⌈α⌉⌈β⌉φ)::rest) }
  | (fs, (⌈∗α⌉φ)::rest) => { (fs, φ::(⌈α⌉⌈α†⌉(undag φ))::rest) } -- NOT splitting!
  | (fs, (⌈_†⌉_)::rest) => { (fs, rest) } -- delete formula, but keep branch!
  | (_, []) => { } -- end node of dagger tableau

theorem mOfBoxDagNode.isDec {x y : Finset Formula × List DagFormula} (y_in : y ∈ boxDagNext x) :
    mOfBoxDagNode y < mOfBoxDagNode x := by
  rcases x with ⟨fs, _|⟨df,rest⟩⟩
  case nil =>
    simp at y_in
  case cons =>
    cases df
    case dag =>
      simp at y_in
      subst y_in
      cases rest
      · simp [mOfBoxDagNode]
      · simp [mOfBoxDagNode] -- added "length" in "mOfBoxDagNode" to solve this.
    case box a f =>
          cases a
          all_goals (simp [boxDagNext] at *)
          case atom_prog A =>
            subst y_in; simp [mOfBoxDagNode]; cases rest; all_goals simp
            sorry -- needs mOfDagFormula > 1
          case sequence =>
            subst y_in; simp [mOfBoxDagNode]; linarith
          case union a b =>
            subst y_in; simp [mOfBoxDagNode]; sorry -- PROBLEM! linarith fails here, change mOfBoxDagNode above?
          case star a =>
            subst y_in; simp [mOfBoxDagNode]; sorry -- PROBLEM: linarith worked before, now broken with "length"
          case test f =>
            rcases y_in with l|r
            subst l; simp [mOfBoxDagNode]; sorry -- same?
            subst r; simp [mOfBoxDagNode]

@[simp]
def boxDagNextTransRefl : (Finset Formula × List DagFormula) → Finset (Finset Formula × List DagFormula) :=
  ftr boxDagNext instDecidableEqProd mOfBoxDagNode @mOfBoxDagNode.isDec

instance modelCanSemImplyBoxDagTabNode {W : Type} : vDash (KripkeModel W × W) (Finset Formula × List DagFormula) :=
  vDash.mk (λ ⟨M,w⟩ (fs, mf) => ∀ φ ∈ fs ∪ (mf.map undag).toFinset, evaluate M w φ)

def boxDagEndNodes : (Finset Formula × List DagFormula) → Finset (Finset Formula)
  | (fs, []) => { fs }
  | (fs, df::rest) => (boxDagNext (fs, df::rest)).attach.biUnion
      (fun ⟨gsdf, h⟩ =>
        have : mOfBoxDagNode gsdf < mOfBoxDagNode (fs, df::rest) := mOfBoxDagNode.isDec h
        boxDagEndNodes gsdf)
termination_by
  boxDagEndNodes fs => mOfBoxDagNode fs
decreasing_by simp_wf; assumption

theorem boxDagEnd_subset_next
    (O_in : Ω ∈ boxDagNext Γ) : boxDagEndNodes Ω ⊆ boxDagEndNodes Γ := by
  intro e
  rcases Γ with ⟨fs, mdf⟩
  rcases mdf with none | ⟨df⟩
  · simp [dagNext] at O_in
  · intro e_in
    unfold boxDagEndNodes
    simp
    simp at O_in
    use Ω.1
    use Ω.2

theorem boxDagEnd_subset_trf {Ω Γ} :
    Ω ∈ boxDagNextTransRefl Γ → boxDagEndNodes Ω ⊆ boxDagEndNodes Γ := by
  intro O_in
  unfold boxDagNextTransRefl at O_in
  rw [ftr.iff] at O_in
  cases O_in
  · aesop
  case inr hyp =>
    rcases hyp with ⟨S, S_in, O_in⟩
    have := boxDagEnd_subset_next S_in
    have := boxDagEnd_subset_trf O_in
    tauto
termination_by
  boxDagEnd_subset_trf Ω Γ hyp  => mOfBoxDagNode Γ
decreasing_by simp_wf; apply mOfBoxDagNode.isDec; assumption

-- A normal successor in a box dagger tableau is an end node.
theorem boxDagNormal_is_dagEnd
    (Γ_in : Γ ∈ boxDagNextTransRefl S)
    (Γ_normal : Γ.2 = [])
    :
    (Γ.1 ∈ boxDagEndNodes S) := by
  have := boxDagEnd_subset_trf Γ_in
  apply this
  rcases Γ with ⟨fs,odf⟩
  subst Γ_normal
  simp [boxDagEndNodes]


-- TODO starInvertAux ?


-- Invertibility for th box star rule.
theorem starInvert (M : KripkeModel W) (v : W) S
    :
    (∃ Γ ∈ boxDagEndNodes S, (M, v) ⊨ Γ) → (M, v) ⊨ S := by
  rintro ⟨Γ, Γ_in, v_Γ⟩
  -- TODO: use starInvertAux and recursive calls here?!
  sorry

-- Soundness for the the box star rule.
-- This Lemma was missing in Borzechowski.
theorem starSoundness (M : KripkeModel W) (v : W) S :
    (M, v) ⊨ S → ∃ Γ ∈ boxDagEndNodes S, (M, v) ⊨ Γ := by

  sorry
