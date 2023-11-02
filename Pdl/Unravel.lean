import Mathlib.Data.Finset.Basic

import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics
import Pdl.Star

inductive DagFormula : Type
  | bottom : DagFormula
  | atom_prop : Char → DagFormula
  | neg : DagFormula → DagFormula
  | and : DagFormula → DagFormula → DagFormula
  | box : Program → DagFormula → DagFormula
  | dag : Program → DagFormula → DagFormula
  deriving Repr

local notation "·" c => DagFormula.atom_prop c
local prefix:11 "~" => DagFormula.neg

local notation "⊥" => DagFormula.bottom
local infixr:66 "⋀" => DagFormula.and
local infixr:60 "⋁" => DagFormula.or

local notation "⌈" α "⌉" P => DagFormula.box α P
local notation "⌈" α "†⌉" P => DagFormula.dag α P

-- THE f FUNCTION
-- | Borzechowski's f function, sort of.
@[simp]
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
  all_goals simp
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

-- UNRAVELING
-- | New Definition 10
@[simp]
def unravel : DagFormula → List (List Formula)
  -- diamonds: ⋓
  | ~⌈·a⌉P => [[~⌈·a⌉ (undag P)]] -- undag aka "the f"
  | ~⌈a ⋓ b⌉P => unravel (~⌈a⌉P) ∪ unravel (~⌈b⌉P)
  | ~⌈?'Q⌉P => [[Q]] ⊎ unravel (~P)
  | ~⌈a;'b⌉P => unravel (~⌈a⌉⌈b⌉P)
  | ~⌈_†⌉_ => ∅
  | ~⌈∗a⌉P =>
      -- omit {{~P}} if P contains dagger
      if containsDag P then unravel (~⌈a⌉(⌈a†⌉P))
      else {{~(undag P)}} ∪ unravel (~⌈a⌉(⌈a†⌉P))
  -- boxes:
  | ⌈·a⌉P => [[⌈·a⌉ (undag P)]]
  | ⌈a ⋓ b⌉ P => unravel (⌈a⌉P) ⊎ unravel (⌈b⌉P)
  | ⌈?'Q⌉P => [[~Q]] ∪ unravel P
  | ⌈a;'b⌉P => unravel (⌈a⌉⌈b⌉P)
  | ⌈_†⌉_ => {∅}
  | ⌈∗a⌉P =>
      -- omit {{P}} when P contains dagger
      if containsDag P then unravel (⌈a⌉(⌈a†⌉P))
      else { {undag P} } ⊎ unravel (⌈a⌉(⌈a†⌉P))
  -- all other formulas we do nothing, but let's pattern match them all.
  | ·c => [[·c]]
  | ~·c => [[~·c]]
  | ~⊥ => [[~⊥]]
  | ⊥ => [[⊥]]
  | ~~f => [[~~undag f]]
  | f⋀g => [[undag f⋀ undag g]]
  | ~f⋀g => [[~undag f⋀ undag g]]
termination_by
  unravel f => mOfDagFormula f

-- Like Lemma 4 from Borzechowski, but using "unravel" instead of a local tableau with n-nodes.
-- This is used in the proof that the (¬∗) rule is sound.
-- See https://is.gd/borzepdl#lemma.4 for the original.
-- TODO: rename to:
-- - diamondStarSound <<<
-- - diamondStarInvert
-- - boxStarSound
-- - boxStarInvert
theorem likeLemmaFour :
  ∀ M (a : Program) (w v : W) (X' : List Formula) (P : DagFormula),
    w ≠ v →
      (M, w) ⊨ (X' ++ [~⌈a⌉(undag P)]) → relate M a w v → (M, v)⊨(~undag P) →
        ∃ Y ∈ {X'} ⊎ unravel (~⌈a⌉P), (M, w)⊨Y
          ∧ ∃ (a : Char) (as : List Program), (~ ⌈·a⌉ (Formula.boxes as (undag P))) ∈ Y
            ∧ relate M (Program.steps ([Program.atom_prog a] ++ as)) w v :=
  by
  intro M a
  -- no 'induction', but using recursive calls instead
  cases a
  case atom_prog A =>
    intro w v X' P w_neq_v w_sat_X w_a_v v_sat_nP
    use X' ++ [(~⌈Program.atom_prog A⌉(undag P))] -- "The claim holds with Y = X" says MB.
    unfold unravel
    simp
    constructor
    · assumption
    · use A
      use []
      unfold Formula.boxes
      simp at *
      exact w_a_v
  case sequence b c =>
    intro w v X' P w_neq_v w_sat_X w_bc_v v_sat_nP
    unfold relate at w_bc_v
    rcases w_bc_v with ⟨u, w_b_u, u_c_v⟩
    simp [vDash.SemImplies, modelCanSemImplyForm] at *
    cases Classical.em (w = u)
    case inr w_neq_u =>
      have IHb := likeLemmaFour M b w u X' (⌈c⌉P) w_neq_u
      specialize IHb _ w_b_u _
      · intro f lhs
        simp at lhs
        cases' lhs with f_in_X f_def
        · apply w_sat_X f
          left
          exact f_in_X
        · subst f_def
          simp
          use u
          constructor
          · exact w_b_u
          · use v
      · simp [vDash.SemImplies, modelCanSemImplyForm]
        use v
      rcases IHb with ⟨Y, Y_in, w_conY, a, as, nBascP_in_Y, w_as_u⟩
      simp at Y_in
      rcases Y_in with ⟨L,⟨L_in_unrav,Ydef⟩⟩
      use L
      constructor
      · exact L_in_unrav
      · constructor
        · intro f lhs
          apply w_conY
          rw [← Ydef]
          simp
          exact lhs
        · use a, (as ++ [c])
          constructor
          · rw [boxes_append]
            rw [← Ydef] at nBascP_in_Y
            simp at nBascP_in_Y
            exact nBascP_in_Y
          · rw [relate_steps] at w_as_u
            rcases w_as_u with ⟨w', w_a_w', w'_as_u⟩
            simp at w_a_w'
            use w'
            rw [relate_steps]
            constructor
            · exact w_a_w'
            · use u
              simp
              exact ⟨w'_as_u,u_c_v⟩
    case inl w_is_u =>
      subst w_is_u -- now u is gone, just say w
      have IHb := likeLemmaFour M c w v X' (P) w_neq_v
      specialize IHb _ u_c_v _
      · intro f lhs
        simp at lhs
        cases' lhs with f_in_X f_def
        · apply w_sat_X f
          left
          exact f_in_X
        · subst f_def
          simp
          use v
      · simp [vDash.SemImplies, modelCanSemImplyForm]
        exact v_sat_nP
      rcases IHb with ⟨Y, Y_in, w_conY, a, as, nBascP_in_Y, w_as_u⟩
      simp at Y_in
      rcases Y_in with ⟨L,⟨L_in_unrav,Ydef⟩⟩
      use L
      constructor
      · sorry -- mismatch:  unravel (~⌈c⌉P) ≠ unravel (~⌈b⌉⌈c⌉P)  ???
      · constructor
        · intro f lhs
          apply w_conY
          rw [← Ydef]
          simp
          exact lhs
        · use a, as
          constructor
          · rw [← Ydef] at nBascP_in_Y
            simp at nBascP_in_Y
            exact nBascP_in_Y
          · rw [relate_steps] at w_as_u
            rcases w_as_u with ⟨w', w_a_w', w'_as_u⟩
            simp at w_a_w'
            use w'

  case union a b =>
    intro w v X' P w_neq_v w_sat_X w_aub_v v_sat_nP
    unfold relate at w_aub_v
    cases w_aub_v
    case inl w_a_v =>
      have IH := likeLemmaFour M a w v X'
      specialize IH P w_neq_v _ w_a_v _
      · unfold vDash.SemImplies at *
        unfold modelCanSemImplyList at *
        unfold modelCanSemImplyForm at *
        simp at *
        intro f f_in
        cases f_in
        case inl f_in_X' =>
          apply w_sat_X f
          left
          exact f_in_X'
        case inr f_is_naP =>
          subst f_is_naP
          simp
          use v
      · exact v_sat_nP
      rcases IH with ⟨Y, Y_in, w_conY, a, as, nBasP_in_Y, w_as_v⟩
      use Y
      constructor
      · simp at *
        rcases Y_in with ⟨Z, Z_in, Ydef⟩
        use Z
        tauto
      · constructor
        · exact w_conY
        · use a, as
    case inr w_b_v =>
      have IH := likeLemmaFour M b w v X' P
      specialize IH w_neq_v _ w_b_v _
      · unfold vDash.SemImplies at *
        unfold modelCanSemImplyList at *
        unfold modelCanSemImplyForm at *
        simp at *
        intro f f_in
        cases f_in
        case inl f_in_X' =>
          apply w_sat_X f
          left
          exact f_in_X'
        case inr f_is_nbP =>
          subst f_is_nbP
          simp
          use v
      · exact v_sat_nP
      rcases IH with ⟨Y, Y_in, w_conY, a, as, nBasP_in_Y, w_as_v⟩
      use Y
      constructor
      · simp at *
        rcases Y_in with ⟨Z, Z_in, Ydef⟩
        use Z
        tauto
      · constructor
        · exact w_conY
        · use a, as
  case star a =>
    intro w v X' P w_neq_v w_sat_X w_aS_v v_sat_nP
    unfold vDash.SemImplies at v_sat_nP -- mwah
    unfold modelCanSemImplyForm at v_sat_nP
    simp at v_sat_nP
    unfold relate at w_aS_v
    have := starCases w_aS_v
    cases this
    case inl w_is_v =>
      absurd w_neq_v
      assumption
    case inr hyp =>
      rcases hyp with ⟨w_neq_v, ⟨y, w_neq_y, w_a_y, y_aS_v⟩⟩
      -- w -a-> y -a*-> v
      -- S      U       T  (in Borzechowski)
      -- dagger here, yes!
      have IHa := likeLemmaFour M a w y X' (⌈a†⌉P) w_neq_y
      specialize IHa _ w_a_y _
      · intro f
        simp
        intro f_in
        cases f_in
        case inl f_in_X' =>
          apply w_sat_X
          simp
          left
          exact f_in_X'
        case inr f_def =>
          subst f_def
          simp
          use y
          constructor
          · exact w_a_y
          · use v
      · unfold vDash.SemImplies
        unfold modelCanSemImplyForm
        simp
        use v
      rcases IHa with ⟨Y, Y_in, w_conY, A, as, nBasaSP_in_Y, w_as_y⟩
      use Y
      constructor
      · simp
        simp at Y_in
        rcases Y_in with ⟨L, L_in_unrav, defY⟩
        use L
        constructor
        · cases Classical.em (containsDag P)
          case inl hyp =>
            rw [hyp]
            simp
            exact L_in_unrav
          case inr hyp =>
            simp at hyp
            rw [hyp]
            simp
            right
            exact L_in_unrav
        · exact defY
      · constructor
        · assumption
        · use A, (as ++ [∗ a])
          rw [boxes_append]
          simp
          constructor
          · exact nBasaSP_in_Y
          · rw [relate_steps] at w_as_y
            rcases w_as_y with ⟨y', y_foo⟩
            use y'
            rw [relate_steps]
            simp at y_foo
            constructor
            · tauto
            · use y
              constructor
              · tauto
              · simp
                exact y_aS_v
  case test f =>
    intro w v X' P w_neq_v w_sat_X w_tf_v v_sat_nP
    unfold relate at w_tf_v
    rcases w_tf_v with ⟨w_is_v, w_f⟩
    subst w_is_v
    absurd w_neq_v
    rfl

-- Analogous to Lemma 4 we need one for the box case.
-- This is used in the proof that the (∗) rule is sound.
-- TODO statement is probably still a messy mixture of box and diamond case.
theorem lemmaFourAndThreeQuarters :
  ∀ M (a : Program) (w v : W) (X' : List Formula) (P : DagFormula),
    w ≠ v → -- change this?
      (M, w) ⊨ (X' ++ [⌈a⌉(undag P)]) → relate M a w v → (M, v)⊨(~undag P) →
        ∃ Y ∈ {X'} ∪ unravel (⌈a⌉P), (M, w)⊨Y
          ∧ ∃ (a : Char) (as : List Program), (~ ⌈·a⌉ (Formula.boxes as (undag P))) ∈ Y
            ∧ relate M (Program.steps ([Program.atom_prog a] ++ as)) w v :=
  by
  sorry
