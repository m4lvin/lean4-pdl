-- TABLEAU

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Option

import Pdl.Syntax
import Pdl.Measures
import Pdl.Setsimp
import Pdl.Semantics
import Pdl.Discon
import Pdl.DagTableau -- replaces Pdl.Unravel

open Undag

-- HELPER FUNCTIONS

@[simp]
def listsToSets : List (List Formula) → Finset (Finset Formula)
| LS => (LS.map List.toFinset).toFinset

-- LOCAL TABLEAU

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def Closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X

-- Local rules: given this set, we get these sets as child nodes
inductive localRule : Finset Formula → Finset (Finset Formula) → Type
  -- PROP LOGIC
  -- closing rules:
  | bot {X    } (h : (⊥ : Formula) ∈ X) : localRule X ∅
  | not {X φ  } (h : φ ∈ X ∧ (~φ) ∈ X) : localRule X ∅
  -- one-child rules:
  | neg {X φ  } (h : (~~φ)      ∈ X) : localRule X { X \ {~~φ}    ∪ {φ}   }
  | con {X φ ψ} (h : φ ⋀ ψ      ∈ X) : localRule X { X \ {φ⋀ψ}    ∪ {φ,ψ} }
  -- splitting rule:
  | nCo {X φ ψ} (h : (~(φ ⋀ ψ)) ∈ X) : localRule X { X \ {~(φ⋀ψ)} ∪ {~φ}
                                                   , X \ {~(φ⋀ψ)} ∪ {~ψ}  }
  -- PROGRAMS
  -- Single-branch rules:
  | nTe {X φ ψ} (h : (~⌈?'φ⌉ψ) ∈ X) : localRule X { X \ {~⌈?'φ⌉ψ} ∪ {φ, ~ψ} } -- TODO should remove marking ?
  | nSe {X a b f} (h : (~⌈a;'b⌉f) ∈ X) : localRule X { X \ {~⌈a;'b⌉f} ∪ {~⌈a⌉⌈b⌉f} }
  | uni {X a b f} (h : (⌈a⋓b⌉f) ∈ X) : localRule X { X \ {⌈a⋓b⌉f} ∪ {⌈a⌉ f, ⌈b⌉ f} }
  | seq {X a b f} (h : (⌈a;'b⌉f) ∈ X) : localRule X { X \ {⌈a;'b⌉f} ∪ {⌈a⌉⌈b⌉f} }
  -- Splitting rules:
  | tes {X f g} (h : (⌈?'f⌉g) ∈ X) : localRule X { X \ {⌈?'f⌉g} ∪ {~f}
                                                 , X \ {⌈?'f⌉g} ∪ {g} }
  | nUn {a b f} (h : (~⌈a⋓b⌉f) ∈ X) : localRule X { X \ {~⌈a ⋓ b⌉f} ∪ {~⌈a⌉f}
                                                    , X \ {~⌈a ⋓ b⌉f} ∪ {~⌈b⌉f} }
  -- STAR
  -- NOTE: we "manually" already make the first unravel/dagger step here to satisfy the (Neg)DagFormula type.
  | sta {X a f} (h : (⌈∗a⌉f) ∈ X) : localRule X (boxDagEndNodes (X \ {⌈∗a⌉f} ∪ {f}, [ inject [a] a f ]))
  | nSt {a f}  (h : (~⌈∗a⌉f) ∈ X) : localRule X ( { X \ {~⌈∗a⌉f} ∪ {~f} }
                                                ∪ dagEndNodes (X \ {~⌈∗a⌉f}, NegDagFormula.neg (inject [a] a f)))

  -- TODO which rules need and modify markings?
  -- TODO only apply * if there is a marking.

-- Like Lemma 5 of MB
lemma localRuleTruth {W} {M : KripkeModel W} {w : W} {X B} :
  localRule X B → ((∃ Y ∈ B, (M,w) ⊨ Y) ↔ (M,w) ⊨ X) :=
  by
  intro locR
  cases locR
  all_goals try simp only [Finset.mem_singleton, Finset.union_insert, Finset.mem_union, Finset.mem_sdiff, Finset.not_mem_empty]
  -- PROPOSITIONAL LOGIC
  case bot bot_in_a =>
    constructor
    · intro ⟨_, Y_in, _⟩; simp at Y_in
    · intro w_sat_a
      by_contra
      let w_sat_bot := w_sat_a ⊥ bot_in_a
      simp at w_sat_bot
  case not f hyp =>
    constructor
    · intro ⟨_, fls, _⟩
      exfalso
      exact fls
    · intro w_sat_a
      by_contra
      have w_sat_f : evaluate M w f := w_sat_a f hyp.left
      have w_sat_not_f : evaluate M w (~f) :=  w_sat_a (~f) hyp.right
      simp at w_sat_not_f
      exact absurd w_sat_f w_sat_not_f
  case neg f hyp =>
    constructor
    · simp
      intro lhs g g_in
      cases em (g = (~~f))
      case inl g_is_notnotf =>
        subst g_is_notnotf
        simp only [evaluate, not_not]
        apply lhs
        simp
      case inr g_is_not_notnotf =>
        specialize lhs g
        simp at lhs
        apply lhs
        left
        exact ⟨g_in,g_is_not_notnotf⟩
    · intro w_sat_a
      have w_sat_f : evaluate M w f :=
        by
        specialize w_sat_a (~~f) hyp
        simp at w_sat_a
        exact w_sat_a
      use X \ {~~f} ∪ {f}
      simp
      intro g
      simp
      intro g_in
      cases g_in
      case inl hyp =>
        apply w_sat_a
        exact hyp.left
      case inr g_is_f => subst g_is_f; exact w_sat_f
  case con f g hyp =>
    constructor
    · simp
      intro lhs h h_in
      cases em (h = f⋀g)
      case inl h_is_fandg =>
        subst h_is_fandg
        simp
        constructor
        all_goals (apply lhs; simp)
      case inr h_is_not_fandg =>
        specialize lhs h
        simp at lhs
        apply lhs
        right
        left
        exact ⟨h_in, h_is_not_fandg⟩
    · intro w_sat_a
      use X \ {f⋀g} ∪ {f, g}
      simp
      intro h
      simp
      intro h_in
      cases h_in
      case inl h_is_f =>
        rw [h_is_f]
        specialize w_sat_a (f⋀g) hyp
        simp at w_sat_a
        exact w_sat_a.left
      case inr whatever =>
        cases whatever
        case inr h_is_g =>
          rw [h_is_g]
          specialize w_sat_a (f⋀g) hyp
          simp at w_sat_a
          exact w_sat_a.right
        case inl h_in_X => exact w_sat_a h h_in_X.left
  case nCo f g notfandg_in_a =>
    constructor
    · simp
      intro lhs h h_in
      cases em (h = (~(f⋀g)))
      case inl h_is_notforg =>
        subst h_is_notforg
        simp
        have : evaluate M w (~f) ∨ evaluate M w (~g) := by
          cases lhs
          case inl w_nf =>
            left
            specialize w_nf (~f)
            simp at w_nf
            simp
            exact w_nf
          case inr w_ng =>
            right
            specialize w_ng (~g)
            simp at w_ng
            simp
            exact w_ng
        simp at this
        tauto
      case inr h_is_not_notforg =>
        cases' lhs with hyp hyp
        all_goals
          apply hyp
          simp
          left
          exact ⟨h_in,h_is_not_notforg⟩
    · intro w_sat_a
      let w_sat_phi := w_sat_a (~(f⋀g)) notfandg_in_a
      simp at w_sat_phi
      rw [imp_iff_not_or] at w_sat_phi
      cases' w_sat_phi with not_w_f not_w_g
      · use X \ {~(f⋀g)} ∪ {~f}
        simp
        intro h h_in
        simp at *
        cases h_in
        case inl h_in_X => exact w_sat_a _ h_in_X.left
        case inr h_is_notf => rw [h_is_notf]; simp; exact not_w_f
      · use X \ {~(f⋀g)} ∪ {~g}
        simp
        intro h h_in
        simp at h_in
        cases h_in
        case inl h_in_X => exact w_sat_a _ h_in_X.left
        case inr h_is_notf => rw [h_is_notf]; simp; exact not_w_g
  -- STAR RULES
  case nSt a f naSf_in_X =>
    constructor
    · simp
      intro branchSat
      cases branchSat
      case inl _ => sorry -- should be easy
      case inr hyp =>
        rw [← notStarSoundness] at hyp -- using Lemma about DagTableau
        simp [vDash,modelCanSemImplyDagTabNode] at hyp
        intro φ phi_in
        cases em (φ = (~⌈∗a⌉f))
        case inl phi_def =>
          subst phi_def
          simp
          specialize hyp (~⌈a⌉⌈∗a⌉f)
          simp at hyp
          rcases hyp with ⟨z, w_a_z, y, z_aS_x, y_nf⟩
          use y
          constructor
          · apply Relation.ReflTransGen.head
            all_goals aesop
          · assumption
        case inr => aesop
    · intro Mw_X
      simp
      have := Mw_X (~⌈∗a⌉f) naSf_in_X
      simp at this
      rcases this with ⟨y, x_rel_y, y_nf⟩
      cases Relation.ReflTransGen.cases_head x_rel_y
      · left
        intro g g_in
        aesop
      case inr hyp =>
        rcases hyp with ⟨z, w_aS_z, z_a_y⟩
        right

        -- IDEA A: use notStarSoundnessAux (like Lemma 4) directly here?
        have := notStarSoundnessAux a M w z (X \ {~⌈∗a⌉f}) (DagFormula.box a (DagFormula.dag a f))
        specialize this _ w_aS_z _
        · sorry
        · sorry -- z ⊨ ...
        -- now missing connection between dagNextTransRefl and endNodes Of ...

        -- IDEA B: use the still to be proven Lemma (like 5) about DagTableau
        rw [← notStarSoundness]
        intro f f_in
        simp at f_in
        cases f_in
        · apply Mw_X
          tauto
        case inr f_def =>
          subst f_def
          simp
          aesop
  case sta a f aSf_in_X =>
    rw [Iff.comm]
    convert starSoundness M w -- using the Box version of Lemma 5
    constructor
    · intro Mw_X φ phi_in
      simp [vDash, undag, modelCanSemImplyDagTabNode, inject] at phi_in
      cases phi_in
      · apply Mw_X
        tauto
      case inr phi_defs =>
        specialize Mw_X (⌈∗a⌉f) aSf_in_X
        cases phi_defs
        case inl phi_is_f =>
            subst phi_is_f
            simp at *
            apply Mw_X
            apply Relation.ReflTransGen.refl
        case inr phi_is_aaSf =>
            subst phi_is_aaSf
            simp at *
            sorry -- should be easy
    · intro Mw_X φ phi_in
      apply Mw_X
      cases em (φ = (⌈∗a⌉f))
      all_goals sorry

  -- OTHER PDL RULES
  case nTe φ ψ in_X =>
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      cases Classical.em (f = (~⌈?'φ⌉ψ))
      case inl f_def =>
        subst f_def
        simp
        constructor
        · apply w_Y; simp
        · specialize w_Y (~ψ); simp at w_Y; exact w_Y
      case inr f_not => apply w_Y; simp; tauto
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      rcases f_in with f_is_phi | ⟨f_in_X, _⟩ | f_is_notPsi
      · subst f_is_phi
        specialize w_X _ in_X
        simp at w_X
        tauto
      · exact w_X _ f_in_X
      · subst f_is_notPsi
        specialize w_X _ in_X
        simp at *
        tauto
  case nSe a b φ nabf_in_X => -- { X \ {~⌈a;'b⌉f} ∪ {~⌈a⌉⌈b⌉f} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      cases Classical.em (f = (~⌈a;'b⌉φ))
      case inl f_def =>
        subst f_def
        specialize w_Y (~⌈a⌉⌈b⌉φ) (by simp)
        simp at w_Y
        simp
        tauto
      case inr f_not => apply w_Y; simp; tauto
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      rcases f_in with ⟨f_in_X, _⟩ | f_is_notabPhi
      · exact w_X _ f_in_X
      · subst f_is_notabPhi
        specialize w_X (~(⌈a;'b⌉φ)) nabf_in_X
        simp at *
        tauto
  case uni a b φ aubPhi_in_X => -- { X \ {⌈a⋓b⌉f} ∪ {⌈a⌉ f, ⌈b⌉ f} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      cases Classical.em (f = (⌈a⋓b⌉φ))
      case inl f_def =>
        subst f_def
        have := w_Y (⌈a⌉φ) (by simp)
        have := w_Y (⌈b⌉φ) (by simp)
        simp at *
        tauto
      case inr f_not => apply w_Y; simp; tauto
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      rcases f_in with f_is_aPhi | ⟨f_in_X, _⟩ | f_is_bPhi
      · subst f_is_aPhi
        specialize w_X (⌈a⋓b⌉φ) aubPhi_in_X
        simp at *
        aesop
      · exact w_X _ f_in_X
      · subst f_is_bPhi
        specialize w_X (⌈a⋓b⌉φ) aubPhi_in_X
        simp at *
        aesop
  case seq a b φ abPhi_in_X => -- { X \ {⌈a;'b⌉f} ∪ {⌈a⌉⌈b⌉f} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      cases em (f = ⌈a;'b⌉φ)
      case inl f_def =>
        subst f_def
        specialize w_Y (⌈a⌉⌈b⌉φ) (by simp)
        simp at w_Y
        simp
        tauto
      case inr f_not => apply w_Y; simp; tauto
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      rcases f_in with ⟨f_in_X, _⟩ | f_is_abPhi
      · exact w_X _ f_in_X
      · subst f_is_abPhi
        specialize w_X (⌈a;'b⌉φ) abPhi_in_X
        simp at *
        tauto
  -- Splitting rules:
  case tes ψ φ tPsiPhi_in_X => -- { X \ {⌈?'f⌉g} ∪ {~f} , X \ {⌈?'f⌉g} ∪ {g} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      simp at Y_in
      intro f f_inX
      cases em (f = (⌈?'ψ⌉φ))
      case inl f_is_tPsiPhi =>
        subst f_is_tPsiPhi
        cases Y_in
        case inl Y_def =>
          subst Y_def
          simp
          intro w_Phi
          specialize w_Y (~ψ) (by simp)
          simp at w_Y
          tauto
        case inr Y_def =>
          subst Y_def
          specialize w_Y φ
          simp at *
          tauto
      case inr f_neq_tPsiPhi =>
        specialize w_Y f
        aesop
    · intro w_X
      simp
      have := w_X (⌈?'ψ⌉φ) tPsiPhi_in_X
      simp at this
      rw [imp_iff_not_or] at this
      cases this
      case inl w_notPsi =>
        left
        intro f f_in
        simp at f_in
        cases f_in
        case inl f_hyp =>
          exact w_X f f_hyp.left
        case inr f_def =>
          subst f_def
          simp
          exact w_notPsi
      case inr w_Phi =>
        right
        intro f f_in
        simp at f_in
        cases f_in
        case inl f_hyp =>
          exact w_X f f_hyp.left
        case inr f_def =>
          subst f_def
          exact w_Phi
  case nUn a b φ naubPhi_in_X => -- { X \ {~⌈a ⋓ b⌉φ} ∪ {~⌈a⌉φ}, X \ {~⌈a ⋓ b⌉φ} ∪ {~⌈b⌉φ} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      simp at Y_in
      intro f f_inX
      cases em (f = (~⌈a ⋓ b⌉φ))
      case inl f_def =>
        subst f_def
        cases Y_in
        case inl Y_def =>
          subst Y_def
          simp
          specialize w_Y (~⌈a⌉φ)
          simp at w_Y
          aesop
        case inr Y_def =>
          subst Y_def
          simp
          specialize w_Y (~⌈b⌉φ)
          simp at w_Y
          aesop
      case inr f_neq =>
        specialize w_Y f
        apply w_Y
        aesop
    · intro w_X
      simp
      have := w_X (~⌈a ⋓ b⌉φ) naubPhi_in_X
      simp at this
      rcases this with ⟨v, w_a_v | w_b_v, not_v_Phi⟩
      case inl =>
        left
        intro f f_in
        simp at f_in
        cases f_in
        case inl f_hyp =>
          exact w_X f f_hyp.left
        case inr f_def =>
          subst f_def
          simp
          use v
      case inr =>
        right
        intro f f_in
        simp at f_in
        cases f_in
        case inl f_hyp =>
          exact w_X f f_hyp.left
        case inr f_def =>
          subst f_def
          simp
          use v

-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
@[simp]
def SimpleForm : Formula → Bool
  | ⊥ => True -- TODO: change to False, covered by bot rule?
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | ⌈·_⌉_ => True
  | ~⌈·_⌉_ => True
  | _ => False

def Simple : Finset Formula → Bool
  | X => ∀ P ∈ X, SimpleForm P

-- Definition 8, page 14
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau for X, must be maximal
inductive LocalTableau : Finset Formula → Type
  | byLocalRule {X B} (_ : localRule X B) (next : ∀ Y ∈ B, LocalTableau Y) : LocalTableau X
  | sim {X} : Simple X → LocalTableau X

open LocalTableau

open HasLength

-- needed for endNodesOf
instance localTableauHasSizeof : SizeOf (Σ X, LocalTableau X) :=
  ⟨fun ⟨X, _⟩ => lengthOf X⟩

-- TODO: is this even going to be true for our new system?
-- Maybe use a different measure than lengthOf?
theorem localRulesDecreaseLength {X : Finset Formula} {B : Finset (Finset Formula)}
    (r : localRule X B) : ∀ Y ∈ B, lengthOf Y < lengthOf X :=
  by
  cases r
  all_goals intro β inB; simp at *
  -- TODO: see Bml, first enable additional simps in Pdl.Setsimp
  all_goals sorry

-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, LocalTableau X) → Finset (Finset Formula)
  | ⟨X, @byLocalRule _ B lr next⟩ =>
    B.attach.biUnion fun ⟨Y, h⟩ =>
      have : lengthOf Y < lengthOf X := localRulesDecreaseLength lr Y h
      endNodesOf ⟨Y, next Y h⟩
  | ⟨X, sim _⟩ => {X}

-- PROJECTIONS

@[simp]
def formProjection : Char → Formula → Option Formula
  | A, ⌈·B⌉φ => if A == B then some φ else none
  | _, _ => none

def projection : Char → Finset Formula → Finset Formula
  | A, X => X.biUnion fun x => (formProjection A x).toFinset

@[simp]
theorem proj : g ∈ projection A X ↔ (⌈·A⌉g) ∈ X :=
  by
  rw [projection]
  simp
  constructor
  · intro lhs
    rcases lhs with ⟨boxg, boxg_in_X, projboxg_is_g⟩
    cases boxg
    repeat' aesop
  · intro rhs
    use ⌈·A⌉g
    simp
    exact rhs

theorem projSet : projection A X = {ϕ | (⌈·A⌉ϕ) ∈ X} :=
  by
  ext1
  simp

-- TABLEAUX

-- Definition 16, page 29
-- TODO: do we want a ClosedTableau or more general Tableau type?
-- If more general, do we want an "open" constructor with(out) arguments/proofs?
inductive ClosedTableau : List (Finset Formula) → Finset Formula → Type
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, ClosedTableau Hist Y) → ClosedTableau Hist X
  | atm {A X ϕ} : (~⌈·A⌉ϕ) ∈ X → Simple X → ClosedTableau (X :: Hist) (projection A X ∪ {~ϕ}) → ClosedTableau Hist X
  | repeat {X} : X ∈ Hist → ClosedTableau Hist X

inductive Provable : Formula → Prop
  | byTableau {φ : Formula} : ClosedTableau _ {~φ} → Provable φ

-- Definition 17, page 30
def Inconsistent : Finset Formula → Prop
  | X => Nonempty (ClosedTableau [] X)

def Consistent : Finset Formula → Prop
  | X => ¬Inconsistent X
