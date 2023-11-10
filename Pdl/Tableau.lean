-- TABLEAU

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Option

import Pdl.Syntax
import Pdl.Measures
import Pdl.Setsimp
import Pdl.Semantics
import Pdl.Discon
import Pdl.Unravel

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
  | sta {X a f} (h : (⌈∗a⌉f) ∈ X) : localRule X ({ X \ {⌈∗a⌉f} } ⊎ (listsToSets (unravel (inject (⌈∗a⌉f)))))
  | nSt {a f} (h : (~⌈∗a⌉f) ∈ X) : localRule X ({ X \ {~⌈∗a⌉f} } ⊎ (listsToSets (unravel (inject (~⌈∗a⌉f)))))

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
    · intro ⟨Y,Y_in,w_Y⟩; simp at Y_in
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
      have w_sat_f : evaluate M w f := by
        apply w_sat_a
        exact hyp.left
      have w_sat_not_f : evaluate M w (~f) :=
        by
        apply w_sat_a (~f)
        exact hyp.right
      simp at *
      exact absurd w_sat_f w_sat_not_f
  case neg f hyp =>
    constructor
    · simp
      intro lhs g g_in
      cases em (g = (~~f))
      case inl g_is_notnotf =>
        subst g_is_notnotf
        simp  only [evaluate, not_not]
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
        aesop
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
        · apply lhs
          simp
        · apply lhs
          simp
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
        simp at *
        exact w_sat_a.left
      case inr whatever =>
        cases whatever
        case inr h_is_g =>
          rw [h_is_g]
          specialize w_sat_a (f⋀g) hyp
          simp at *
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
            simp at *
            exact w_nf
          case inr w_ng =>
            right
            specialize w_ng (~g)
            simp at *
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
    · rintro ⟨Y, Y_in, MwY⟩ -- invertibility
      simp at Y_in
      rcases Y_in with ⟨FS,FS_in,Y_def⟩
      subst Y_def
      intro g g_in_X
      cases em (g = (~⌈∗a⌉f))
      case inl g_is_nsSf =>
        subst g_is_nsSf
        simp
        cases FS_in
        case inl FS_is_nf =>
          have : (FS : List Formula) = {~f} := by cases FS_is_nf; rfl; tauto
          subst this
          use w
          constructor
          · exact Relation.ReflTransGen.refl
          · specialize MwY (~f)
            simp at MwY
            apply MwY
            right
            exact List.mem_of_mem_head? rfl
        case inr FS_in_unrav =>
          simp [unravel] at FS_in_unrav
          sorry
      case inr g_neq_nsSf =>
        apply MwY
        sorry
    · intro Mw_X -- soundness
      have w_adiamond_f := Mw_X (~⌈∗a⌉f) naSf_in_X
      simp at w_adiamond_f
      rcases w_adiamond_f with ⟨v, w_aS_v, v_nF⟩
      -- NOTE: Borze also makes a distinction whether a is atomic. Not needed?
      -- We still distinguish cases whether v = w
      cases Classical.em (w = v)
      case inl w_is_v =>
        -- Same world, we can use the left branch.
        subst w_is_v
        use (X \ {~⌈∗a⌉f} ∪ {~f})
        constructor
        · apply union_elem_uplus
          simp
          unfold unravel
          simp
          use {~f}
          constructor
          · left
            exact List.mem_of_mem_head? rfl
          · rfl
        · intro g g_in
          simp at g_in
          cases g_in
          · tauto
          case h.right.inr hyp =>
            subst hyp
            unfold evaluate
            assumption
      case inr w_neq_v =>
        -- Different world, we use the right branch and Lemma 4 here:
        have lemFour := likeLemmaFour M (∗ a) w v X.toList (inject f) w_neq_v
        simp [vDash, modelCanSemImplyForm, modelCanSemImplyList] at lemFour
        specialize lemFour _ w_aS_v v_nF
        · intro g g_in
          apply Mw_X
          cases g_in
          case a.inl => assumption
          case a.inr h => convert naSf_in_X
        rcases lemFour with ⟨Z, Z_in, Mw_ZX, ⟨as, nBasf_in, w_as_v⟩⟩
        use (X \ {~⌈∗a⌉f}) ∪ Z.toFinset
        constructor
        · exact union_elem_uplus (by simp) (by simp; use Z)
        · intro g g_in; simp at g_in; apply Mw_ZX; tauto
  case sta a f aSf_in_X =>
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩ -- invertibility
      simp at Y_in
      rcases Y_in with ⟨Z, Z_in_unrav, Y_def⟩
      subst Y_def
      intro g g_in_X
      cases Classical.em (g = (⌈∗a⌉f))
      case inl g_def =>
        subst g_def
        simp
        intro v w_a_v
        sorry
      case inr g_not =>
        apply w_Y
        simp
        tauto
    · intro w_X -- soundness
      simp
      have := lemmaFourAndThreeQuarters M -- use here?
      sorry

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
      rcases f_in with f_is_phi | ⟨f_in_X, not_f⟩ | f_is_notPsi
      · subst f_is_phi
        specialize w_X _ in_X
        simp at w_X
        tauto
      · exact w_X _ f_in_X
      · subst f_is_notPsi
        specialize w_X _ in_X
        simp at *
        tauto
  case nSe a b φ nabf_in_X => -- {X a b f} (h : (~⌈a;'b⌉f) ∈ X) : localRule X { X \ {~⌈a;'b⌉f} ∪ {~⌈a⌉⌈b⌉f} }
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
      rcases f_in with ⟨f_in_X, not_f⟩ | f_is_notabPhi
      · exact w_X _ f_in_X
      · subst f_is_notabPhi
        specialize w_X (~(⌈a;'b⌉φ)) nabf_in_X
        simp at *
        tauto
  case uni a b φ aubPhi_in_X => -- {X a b f} (h : (⌈a⋓b⌉f) ∈ X) : localRule X { X \ {⌈a⋓b⌉f} ∪ {⌈a⌉ f, ⌈b⌉ f} }
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
      rcases f_in with f_is_aPhi | ⟨f_in_X, f_is_not_aubPhi⟩ | f_is_bPhi
      · subst f_is_aPhi
        specialize w_X (⌈a⋓b⌉φ) aubPhi_in_X
        simp at *
        aesop
      · exact w_X _ f_in_X
      · subst f_is_bPhi
        specialize w_X (⌈a⋓b⌉φ) aubPhi_in_X
        simp at *
        aesop
  case seq a b φ abPhi_in_X => -- {X a b f} (h : (⌈a;'b⌉f) ∈ X) : localRule X { X \ {⌈a;'b⌉f} ∪ {⌈a⌉⌈b⌉f} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      cases Classical.em (f = ⌈a;'b⌉φ)
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
      rcases f_in with ⟨f_in_X, not_f⟩ | f_is_abPhi
      · exact w_X _ f_in_X
      · subst f_is_abPhi
        specialize w_X (⌈a;'b⌉φ) abPhi_in_X
        simp at *
        tauto
  -- Splitting rules:
  case tes => -- {X f g} (h : (⌈?'f⌉g) ∈ X) : localRule X { X \ {⌈?'f⌉g} ∪ {~f} , X \ {⌈?'f⌉g} ∪ {g} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      simp at Y_in
      intro f f_inX
      cases Y_in
      · sorry
      · sorry
    · intro w_X
      simp
      -- split TODO!
      sorry
  case nUn => -- {a b f} (h : (~⌈a ⋓ b⌉f) ∈ X) : localRule X { X \ {~⌈a ⋓ b⌉f} ∪ {~⌈a⌉f}, X \ {~⌈a ⋓ b⌉f} ∪ {~⌈b⌉f} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      simp at Y_in
      intro f f_inX
      cases Y_in
      · sorry
      · sorry
    · intro w_X
      simp
      -- split TODO
      sorry

-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
@[simp]
def SimpleForm : Formula → Bool
  | ⊥ => True
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
