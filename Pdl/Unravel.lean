import Mathlib.Data.Finset.Basic

import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics

-- UNRAVELING
-- | New Definition 10
@[simp]
def unravel : Formula → List (List Formula)
  -- diamonds:
  | ~⌈·a⌉ P => [[~⌈·a⌉ P]]
  | ~⌈Program.union p1 p2⌉ P => unravel (~⌈p1⌉ P) ∪ unravel (~⌈p2⌉ P) -- no theF here. fishy?
  | ~⌈✓ Q⌉ P => [[Q]]⊎unravel (~P)
  | ~⌈a;b⌉ P => unravel (~⌈a⌉ (⌈b⌉ P))
  | ~†_ => ∅
  | ~⌈∗a⌉ P => unravel (~P) ∪ unravel (~⌈a⌉ (†⌈∗a⌉ P))
  -- boxes:
  | ⌈·a⌉P => [[⌈·a⌉ P]]
  | ⌈Program.union a b⌉ P => unravel (⌈a⌉ P)⊎unravel (⌈b⌉ P)
  | ⌈✓ Q⌉ P => [[~Q]] ∪ unravel P
  | ⌈a;b⌉ P => unravel (⌈a⌉ (⌈b⌉ P))
  | †P => {∅}
  | ⌈∗a⌉ P => unravel P⊎unravel (⌈a⌉ (†⌈∗a⌉ P))
  -- all other formulas we do nothing, but let's pattern match them all.
  | ·c => [[·c]]
  | ~·c => [[~·c]]
  | ~⊥ => [[~⊥]]
  | ⊥ => [[⊥]]
  | ~~f => [[~~f]]
  | f⋀g => [[f⋀g]]
  | ~f⋀g => [[~f⋀g]]
termination_by
  unravel f => mOfFormula f

@[simp]
def nsub : Formula → List Formula
  -- diamonds:
  | ~⌈_⌉ P => nsub P
  | ~†P => [~P]
  | †P => [P]
  -- boxes:
  | ⌈_⌉P => nsub P
  -- all other formulas:
  | ·_ => ∅
  | ~·_ => ∅
  | ~⊥ => ∅
  | ⊥ => ∅
  | ~~f => nsub f
  | f⋀g => nsub f ++ nsub g
  | ~f⋀g => nsub f ++ nsub g

theorem rel_steps_last {as} : ∀ v w,
  relate M (Program.steps (as ++ [a])) v w ↔
    ∃ mid, relate M (Program.steps as) v mid ∧ relate M a mid w :=
  by
  induction as
  case nil =>
    simp at *
  case cons a2 as IH =>
    intro s t
    simp at *
    constructor
    · intro lhs
      rcases lhs with ⟨next, s_a2_next, next_asa_t⟩
      rw [IH] at next_asa_t
      tauto
    · intro rhs
      rcases rhs with ⟨m,⟨y,yP,yP2⟩,mP⟩
      use y
      rw [IH]
      tauto

-- Like Lemma 4 from Borzechowski, but using "unravel" instead of a local tableau with n-nodes.
-- see https://malv.in/2020/borzechowski-pdl/Borzechowski1988-PDL-translation-Gattinger2020.pdf#lemma.4
-- TODO: maybe simplify by not having a context X' here / still as useful for showing soundness of ~* rule?
-- TODO: analogous lemma for the box case? and * rule?
theorem likeLemmaFour :
    ∀ M (a : Program) (w v : W) (X' X : List Formula) (P : Formula),
      X = X' ++ {~⌈a⌉ P} →
        (M, w)⊨Con X → relate M a w v → (M, v)⊨(~P) →
          ∃ Y ∈ {X'}⊎unravel (~⌈a⌉ P), (M, w)⊨Con Y
          ∧ ∃ as : List Program, (~ Formula.boxes as P) ∈ Y
            ∧ relate M (Program.steps as) w v :=
  by
  intro M a
  -- no 'induction', but using recursive calls instead
  cases a
  case atom_prog A =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP
    use X -- "The claim holds with Y = X" says MB.
    unfold unravel
    simp
    subst X_def
    constructor
    · rfl
    constructor
    · assumption
    · use [·A]
      unfold Formula.boxes
      simp at *
      constructor
      · right
        exact List.mem_of_mem_head? rfl
      · exact w_a_v
  case sequence b c =>
    intro w v X' X P X_def w_sat_X w_bc_v v_sat_nP
    unfold relate at w_bc_v
    rcases w_bc_v with ⟨u, w_b_u, u_c_v⟩
    subst X_def
    have IHb := likeLemmaFour M b w u X' -- get IH using a recursive call
    specialize IHb (X' ++ {~⌈b⌉ (⌈c⌉ P)}) (⌈c⌉ P) (by rfl) _ w_b_u _
    · convert_to (evaluate M w (Con (X' ++ {~⌈b⌉⌈c⌉P})))
      rw [conEval]
      unfold vDash.SemImplies at w_sat_X
      unfold modelCanSemImplyForm at w_sat_X
      simp at *
      rw [conEval] at w_sat_X
      intro f lhs
      cases' lhs with f_in_X other
      · apply w_sat_X f
        simp
        left
        exact f_in_X
      · simp at other
        specialize w_sat_X (~⌈b;c⌉P)
        cases other
        · specialize w_sat_X _
          · simp
            right
            exact List.mem_of_mem_head? rfl
          simp at *
          rcases w_sat_X with ⟨x,y,y_c_x,w_b_y,nP⟩
          use y
          tauto
        · tauto
    · unfold vDash.SemImplies at *
      unfold modelCanSemImplyForm at *
      simp at *
      use v
    rcases IHb with ⟨Y, Y_in, w_conY, as, nBascP_in_Y, w_as_u⟩
    use Y
    constructor
    · simp at *
      exact Y_in
    constructor
    · tauto
    · use as ++ [c]
      cases as
      case nil => -- n = 0, MB says we need IH again?
        simp at *
        rw [w_as_u]
        exact ⟨nBascP_in_Y,u_c_v⟩
      case cons a as => -- n > 0 in MB
        simp at *
        constructor
        · rw [boxes_last]
          exact nBascP_in_Y
        · rcases w_as_u with ⟨t, w_a_t, y_as_u⟩
          use t
          constructor
          · exact w_a_t
          · rw [rel_steps_last]
            use u
  case union a b =>
    intro w v X' X P X_def w_sat_X w_aub_v v_sat_nP
    unfold relate at w_aub_v
    subst X_def
    cases w_aub_v
    case inl w_a_v =>
      have IH := likeLemmaFour M a w v X' (X' ++ {~⌈a⌉ P}) (P) (by rfl)
      specialize IH _ w_a_v _
      · unfold vDash.SemImplies at *
        unfold modelCanSemImplyForm at *
        simp at *
        rw [conEval] at *
        intro f
        simp
        intro f_in
        cases f_in
        case inl f_in_X' =>
          apply w_sat_X f
          simp
          left
          exact f_in_X'
        case inr f_is_naP =>
          cases f_is_naP -- silly, why does simp not use Finset.mem_singleton here?
          · simp
            use v
          · exfalso
            tauto
      · exact v_sat_nP
      rcases IH with ⟨Y, Y_in, w_conY, as, nBasP_in_Y, w_as_v⟩
      use Y
      constructor
      · simp at *
        rcases Y_in with ⟨Z, Z_in, Ydef⟩
        use Z
        tauto
      · constructor
        · exact w_conY
        · use as
    case inr w_b_v =>
      have IH := likeLemmaFour M b w v X' (X' ++ {~⌈b⌉ P}) (P) (by rfl)
      specialize IH _ w_b_v _
      · unfold vDash.SemImplies at *
        unfold modelCanSemImplyForm at *
        simp at *
        rw [conEval] at *
        intro f
        simp
        intro f_in
        cases f_in
        case inl f_in_X' =>
          apply w_sat_X f
          simp
          left
          exact f_in_X'
        case inr f_is_nbP =>
          cases f_is_nbP -- silly, why does simp not use Finset.mem_singleton here?
          · simp
            use v
          · exfalso
            tauto
      · exact v_sat_nP
      rcases IH with ⟨Y, Y_in, w_conY, as, nBasP_in_Y, w_as_v⟩
      use Y
      constructor
      · simp at *
        rcases Y_in with ⟨Z, Z_in, Ydef⟩
        use Z
        tauto
      · constructor
        · exact w_conY
        · use as
  case star =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
  case test =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
