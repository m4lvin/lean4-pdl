-- TABLEAU

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Option

import Pdl.Syntax
import Pdl.Measures
import Pdl.Setsimp
import Pdl.Semantics
import Pdl.Discon
import Pdl.DagTableau

open Undag

open HasLength

-- Some thoughts about the TNode type:
-- - one formula may be loaded
-- - loading is not changed in local tableaux, but must be tracked through it.
-- - each (loaded) formula is left/right/both --> annotation or actually have two sets X1 and X2 here?
-- - also need to track loading and side "through" dagger tableau. (loading only for diamond dagger?)

-- LOCAL TABLEAU

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def Closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X

-- Local rules replace a given set of formulas by other sets, one for each branch.
-- (In Haskell this is "ruleFor" in Logic.PDL.Prove.Tree.)
inductive OneSidedLocalRule : Finset Formula → List (Finset Formula) → Type
  -- PROP LOGIC
  -- closing rules:
  | bot                  : OneSidedLocalRule {⊥}      ∅
  | not (φ   : Formula) : OneSidedLocalRule {φ, ~φ}  ∅
  | neg (φ   : Formula) : OneSidedLocalRule {~~φ}    [{φ}]
  | con (φ ψ : Formula) : OneSidedLocalRule {φ ⋀ ψ}  [{φ,ψ}]
  | nCo (φ ψ : Formula) : OneSidedLocalRule {~(φ⋀ψ)} [{~φ}, {~ψ}]
  -- PROGRAMS
  -- one-child rules:
  | nTe (φ ψ)   : OneSidedLocalRule {~⌈?'φ⌉ψ}  [ {φ, ~ψ} ]
  | nSe (a b f) : OneSidedLocalRule {~⌈a;'b⌉f} [ {~⌈a⌉⌈b⌉f} ]
  | uni (a b f) : OneSidedLocalRule {⌈a⋓b⌉f}   [ {⌈a⌉f, ⌈b⌉f} ]
  | seq (a b f) : OneSidedLocalRule {⌈a;'b⌉f}  [ {⌈a⌉⌈b⌉f} ]
  -- splitting rules:
  | tes (f g)   : OneSidedLocalRule {⌈?'f⌉g}    [ {~f}, {g} ]
  | nUn (a b f) : OneSidedLocalRule {~⌈a ⋓ b⌉f} [ {~⌈a⌉f}, {~⌈b⌉f} ]
  -- STAR
  -- NOTE: we "manually" already make the first unravel/dagger step here to satisfy the (Neg)DagFormula type.
  -- TODO: avoid "toList" - rewrite DagTableau to already use lists?
  | sta (a f) : OneSidedLocalRule {⌈∗a⌉f} (boxDagEndNodes ({f}, [ inject [a] a f ])).toList
  | nSt (a f) : OneSidedLocalRule {~⌈∗a⌉f} ([ {~f} ] ++ (dagEndNodes (X \ {~⌈∗a⌉f}, NegDagFormula.neg (inject [a] a f))).toList)

-- LOADED rule applications
-- Only the local rules ¬u, ¬; ¬* and ¬? may be applied to loaded formulas (MB page 19).
-- Each rule replaces the loaded formula by:
-- - either one other loaded formula,
-- - or a list of normal formulas.
-- It's annoying to need each rule twice here (due to the definition of LoadFormula).
inductive LoadRule : NegLoadFormula → List (Finset Formula × Option NegLoadFormula) → Type
  | nUn'  {a b χ} : LoadedRule (~'⌊a⋓b ⌋(χ : LoadFormula)) [ (∅, some (~'⌊α⌋χ)), (∅, some (~'⌊β⌋χ)) ]
  | nUn'' {a b φ} : LoadedRule (~'⌊a⋓b ⌋(φ : Formula    )) [ (∅, some (~'⌊α⌋φ)), (∅, some (~'⌊β⌋φ)) ]
  | nSe'  {a b χ} : LoadedRule (~'⌊a;'b⌋(χ : LoadFormula)) [ (∅, some (~'⌊a⌋⌊b⌋χ)) ]
  | nSe'' {a b φ} : LoadedRule (~'⌊a;'b⌋(φ : Formula    )) [ (∅, some (~'⌊a⌋⌊b⌋φ)) ]
  -- TODO: Need dagger diamond tableau for loaded formula below!
  -- use this:  dagEndNodes (X, NegDagFormula.neg (inject [a] a f)))
  | nSt'  {a χ}   : LoadedRule (~'⌊∗a  ⌋(χ : LoadFormula)) ( [ (∅, some (~'χ)) ] ++ sorry)
  | nSt'' {a φ}   : LoadedRule (~'⌊∗a  ⌋(φ : Formula    )) ([ ({~φ}, none) ] ++ sorry)
  | nTe'  {φt χ}  : LoadedRule (~'⌊?'φt⌋(χ : LoadFormula)) [ ({φt}, some (~'χ)) ]
  | nTe'' {φt φ}  : LoadedRule (~'⌊?'φt⌋(φ : Formula    )) [ ({φt, ~φ}, none) ]


def SubPair := Finset Formula × Finset Formula × Option (Sum NegLoadFormula NegLoadFormula)
deriving DecidableEq

-- formulas can be in four places now: left, right, loaded left, loaded right

inductive LocalRule : SubPair → List SubPair → Type
  | oneSidedL (orule : OneSidedLocalRule precond ress) : LocalRule (precond,∅,none) $ ress.map $ λ res => (res,∅,none)
  | oneSidedR (orule : OneSidedLocalRule precond ress) : LocalRule (∅,precond,none) $ ress.map $ λ res => (∅,res,none)
  | LRnegL (ϕ : Formula) : LocalRule ({ϕ}, {~ϕ}, none) ∅ --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ({~ϕ}, {ϕ}, none) ∅ -- ~ϕ occurs on the left side,  ϕ on the right
  -- NOTE: do we need neg rules for ({~ unload χ}, ∅, some (Sum.inl ~χ)) and (∅, {~ unload χ}, some (Sum.inr ~χ)), ..here???
  | loadedL (χ : LoadFormula) (lrule : LoadRule (~'χ) ress) :
      LocalRule (∅,∅, some (Sum.inl (~'χ))) $ ress.map $ λ res => (∅,res,none)

inductive localRule : TNode → Finset TNode → Type -- use List TNode ?!

-- TABLEAU nodes

-- A tableau node has a set of formulas and one or no negated loaded formula.
def TNode := Finset Formula × Finset Formula × Option (Sum NegLoadFormula NegLoadFormula) -- ⟨L, R, o⟩
  deriving DecidableEq -- TODO Repr

instance modelCanSemImplyTNode : vDash (KripkeModel W × W) TNode :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, o⟩ => ∀ f ∈ L ∪ R ∪ (o.map (Sum.elim negUnload negUnload)).toFinset, evaluate M w f)

@[simp]
def applyLocalRule (_ : LocalRule (Lcond, Rcond) C) : TNode → List TNode
  | ⟨L, R, o⟩ => C.map $ λc => (L \ Lcond ∪ c.1, R \ Rcond ∪ c.2, o)

inductive LocalRuleApp : TNode → List TNode → Type
  | mk {L R : Finset Formula}
       {C : List SubPair}
       (Lcond Rcond : Finset Formula)
       (rule : LocalRule (Lcond,Rcond) C)
       (preconditionProof : Lcond ⊆ L ∧ Rcond ⊆ R)
       : LocalRuleApp (L,R,o) $ applyLocalRule rule (L,R,o)

-- Like Lemma 5 of MB
lemma localRuleTruth {W} {M : KripkeModel W} {w : W} {X B} :
  localRule X B → ((∃ Y ∈ B, (M,w) ⊨ Y) ↔ (M,w) ⊨ X) :=
  by
  intro locR
  cases locR
  all_goals simp at * -- only [Finset.mem_singleton, Finset.union_insert, Finset.mem_union, Finset.mem_sdiff, Finset.not_mem_empty]
  -- PROPOSITIONAL LOGIC
  case bot bot_in_a =>
      intro w_sat_a
      specialize w_sat_a ⊥
      aesop
  case not f hyp =>
      intro w_sat_a
      have := w_sat_a f (by simp at *; tauto)
      have := w_sat_a (~f) (by simp at *; tauto)
      aesop
  case neg f hyp =>
    constructor
    · intro lhs g g_in
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
        aesop
    · intro w_sat_a
      have w_sat_f : evaluate M w f :=
        by
        specialize w_sat_a (~~f)
        aesop
      intro g g_in
      aesop
  case con f g hyp =>
    constructor
    · intro lhs h h_in
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
        aesop
    · intro w_sat_a
      intro h h_in
      simp at h_in
      cases h_in
      case inl h_is_f =>
        rw [h_is_f]
        specialize w_sat_a (f⋀g)
        aesop
      case inr whatever =>
        cases whatever
        case inr hyp =>
          cases hyp
          case inl h_is_g =>
            rw [h_is_g]
            specialize w_sat_a (f⋀g)
            aesop
          case inr h_in_o =>
            apply w_sat_a
            aesop
        case inl h_in_X => apply w_sat_a h; aesop
  case nCo f g notfandg_in_a =>
    constructor
    · intro lhs h h_in
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
        aesop
    · intro w_sat_a
      let w_sat_phi := w_sat_a (~(f⋀g)) (by aesop)
      simp at w_sat_phi
      rw [imp_iff_not_or] at w_sat_phi
      cases' w_sat_phi with not_w_f not_w_g
      · left
        intro h h_in
        aesop
      · right
        intro h h_in
        aesop

  -- STAR RULES
  case nSt a f naSf_in_X =>
    constructor
    · -- invertibility
      intro branchSat
      cases branchSat
      case inl Mw_X  =>
        intro φ phi_in
        cases em (φ = (~⌈∗a⌉f))
        case inl phi_def =>
          subst phi_def
          simp at *
          use w
          constructor
          · exact Relation.ReflTransGen.refl
          · specialize Mw_X (~f)
            simp at Mw_X
            assumption
        case inr hyp =>
          apply Mw_X
          simp
          aesop
      case inr hyp =>
        -- want to use notStarInvert, but that does not know/care about loading.
        rename_i X o -- TODO why are X and o no longer in scope/named here?!
        have : ∃ Γ ∈ dagEndNodes (X \ {~⌈∗a⌉f}, some (NegDagFormula.neg (DagFormula.box a (DagFormula.dag a f)))), (M, w)⊨Γ := by
          sorry -- should be easy, use hyp?
        have := notStarInvert M w _ this
        simp [vDash, modelCanSemImplyDagTabNode] at this
        intro φ phi_in
        cases em (φ = (~⌈∗a⌉f))
        case inl phi_def =>
          subst phi_def
          simp
          specialize this (~⌈a⌉⌈∗a⌉f)
          simp at this
          rcases this with ⟨z, w_a_z, y, z_aS_x, y_nf⟩
          use y
          constructor
          · apply Relation.ReflTransGen.head
            all_goals aesop
          · assumption
        case inr => aesop
    · -- soundness
      intro Mw_X
      have := Mw_X (~⌈∗a⌉f) (by aesop) -- naSf_in_X
      simp at this
      rcases this with ⟨y, x_rel_y, y_nf⟩
      cases starCases x_rel_y -- NOTE: Relation.ReflTransGen.cases_head without ≠ was not enough here ...
      · left
        intro g g_in
        aesop
      case inr hyp =>
        right
        -- (... because we need to get the in-equality here to get the contradiction below.)
        rcases hyp with ⟨_, z, w_neq_z, w_a_z, z_aS_y⟩
        -- MB now distinguishes whether a is atomic, we don't care.
        rename_i X o w_neq_y -- TODO avoid this
        have := notStarSoundnessAux a M w z (X \ {~⌈∗a⌉f}) (DagFormula.dag a f)
        specialize this _ w_a_z _
        · intro g g_in
          simp at g_in
          cases g_in
          · apply Mw_X; aesop
          case inr g_def =>
            subst g_def
            simp
            exact ⟨z, ⟨w_a_z, ⟨y, ⟨z_aS_y, y_nf⟩⟩⟩⟩
        · simp [vDash,modelCanSemImplyForm]
          use y
        rcases this with ⟨Γ, Γ_in, w_Γ, caseOne | caseTwo⟩
        · rcases caseOne with ⟨A, as, _, _, Γ_normal⟩
          use Γ.1
          constructor
          · exact dagNormal_is_dagEnd Γ_in Γ_normal
          · intro f f_in
            aesop
        · absurd caseTwo.2 -- contradiction!
          exact w_neq_z

  case sta a f aSf_in_X =>
    constructor
    · -- invertibility
      intro hyp
      rename_i X o -- TODO: avoid this!
      have Mw_X := starInvert M w (X \ {⌈∗a⌉f} ∪ {f}, [inject [a] a f]) sorry -- hyp
      intro φ phi_in
      cases em (φ = (⌈∗a⌉f))
      case inl phi_def =>
        subst phi_def
        simp at *
        intro v w_aS_v
        cases Relation.ReflTransGen.cases_head w_aS_v
        case inl w_is_v =>
          subst w_is_v
          specialize Mw_X f
          simp at Mw_X
          exact Mw_X
        case inr hyp =>
          rcases hyp with ⟨z, w_a_z, z_aS_v⟩
          specialize Mw_X (⌈a⌉⌈∗a⌉f)
          simp at Mw_X
          exact Mw_X z w_a_z v z_aS_v
      case inr hyp =>
        apply Mw_X
        simp
        aesop -- sorry -- tauto
    · -- soundness
      intro Mw_X
      rename_i X o -- TODO: avoid this!
      apply starSoundness M w (X \ {⌈∗a⌉f} ∪ {f}, [inject [a] a f])
      intro φ phi_in
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
            exact Mw_X _ Relation.ReflTransGen.refl
        case inr phi_is_aaSf =>
            subst phi_is_aaSf
            simp at *
            intro v w_a_v z v_a_z
            exact Mw_X _ (Relation.ReflTransGen.head w_a_v v_a_z)

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

def nodeSimple : TNode → Bool
  | (X, none) => ∀ P ∈ X, SimpleForm P
  | (X, some (~'χ)) => SimpleForm (~ unload χ) ∧ ∀ P ∈ X, SimpleForm P


-- Definition 8, page 14
-- a local tableau for X, must be maximal
inductive LocalTableau : TNode → Type
  | byLocalRule {X B} (_ : localRule X B) (next : ∀ Y ∈ B, LocalTableau Y) : LocalTableau X
  | sim {X} : nodeSimple X → LocalTableau X

open LocalTableau

-- LOCAL END NODES AND TERMINATION

@[simp]
def lengthOfTNode : TNode -> ℕ
  | (X, none) => lengthOf X
  | (X, some (~'χ)) => lengthOf X + lengthOf (~ unload χ)

@[simp]
instance tnodeHasLength : HasLength TNode := ⟨lengthOfTNode⟩

-- needed for endNodesOf
instance localTableauHasSizeof : SizeOf (Σ X, LocalTableau X) :=
  ⟨fun ⟨X, _⟩ => lengthOf X⟩

-- TODO: is this even going to be true for our new system?
-- Maybe use a different measure than lengthOf? Also Dershowitz-Manna?
theorem localRulesDecreaseLength {X : TNode} {B : Finset TNode}
    (r : localRule X B) : ∀ Y ∈ B, lengthOf Y < lengthOf X :=
  by
  cases r
  all_goals intro β inB; simp at *
  -- TODO: see Bml, first enable additional simps in Pdl.Setsimp
  all_goals sorry

-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, LocalTableau X) → Finset TNode
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

-- (MB: Definition 16, page 29)
-- TODO: do we want a ClosedTableau or more general Tableau type?
-- If more general, do we want an "open" constructor with(out) arguments/proofs?

-- A tableau for X is either of:
-- - a local tableau for X followed by tableaux for all end nodes,
-- - a (M+) loading rule application
-- - a (At) modal rule application (two cases due to LoadFormula type)
-- - a good repeat (MB condition six)

inductive ClosedTableau : List TNode → TNode → Type
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, ClosedTableau Hist Y) → ClosedTableau Hist X
  | atm'  {A X χ} : Simple X → ClosedTableau (⟨X, ~'⌊·A⌋(χ : LoadFormula)⟩ :: Hist) (projection A X, some (~'χ)) → ClosedTableau Hist (X, ~'⌊·A⌋χ)
  | atm'' {A X φ} : Simple X → ClosedTableau (⟨X, ~'⌊·A⌋(φ : Formula)⟩ :: Hist) (projection A X ∪ {~φ}, none) → ClosedTableau Hist (X, ~'⌊·A⌋φ)
  | repeat {X} : X ∈ Hist → ClosedTableau Hist X

inductive Provable : Formula → Prop
  | byTableau {φ : Formula} : ClosedTableau [] ⟨{~φ}, none⟩ → Provable φ

-- MB: Definition 17, page 30
def Inconsistent : Finset Formula → Prop
  | X => Nonempty (ClosedTableau [] ⟨X, none⟩)

def Consistent : Finset Formula → Prop
  | X => ¬Inconsistent X
