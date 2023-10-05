import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics

-- UNRAVELING
-- | New Definition 10
def unravel : Formula → List (List Formula)
  -- diamonds:
  | ~⌈·a⌉ P => [[~⌈·a⌉ P]]
  | ~⌈Program.union p1 p2⌉ P => unravel (~⌈p1⌉ P) ∪ unravel (~⌈p2⌉ P) -- remove theF here again. fishy? :-/
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
  |-- all other formulas we do nothing, but let's pattern match them all.
    ·c =>
    [[·c]]
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

theorem likeLemmaFour :
    ∀ (W M) (a : Program) (w v : W) (X' X : List Formula) (P : Formula),
      X = X' ++ {~⌈a⌉ P} →
        (M, w)⊨Con X → relate M a w v → (M, v)⊨(~P) →
          ∃ Y ∈ {X'}⊎unravel (~⌈a⌉ P), (M, w)⊨Con Y
          ∧ ∃ as : List Program, (~ Formula.boxes as P) ∈ Y
            ∧ relate M (Program.steps as) w v :=
  by
  intro W M a
  -- 'induction' tactic does not support mutually inductive types, ...
  -- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/induction.20for.20mutually.20inductive.20types
  -- instead, we use cases and make recursive calls, woohoo!
  cases a
  case atom_prog A =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP
    use X -- "The claim holds with Y = X" says MB.
    unfold unravel
    simp
    constructor
    · subst X_def
      rfl
    constructor
    · assumption
    · sorry
  case sequence -- a -- b c -- IHb
    b c =>
    intro w v X' X P X_def w_sat_X w_bc_v v_sat_nP
    unfold relate at w_bc_v
    rcases w_bc_v with ⟨u, w_b_u, u_c_v⟩
    subst X_def
    have IHb := likeLemmaFour W M b w u X' -- here we get an IH using a recursive call!
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
    · sorry -- need (M, u)⊨~⌈c⌉ P -- make and use IHc here ?
    rcases IHb with ⟨Y, Y_in, w_conY⟩
    use Y
    constructor
    sorry
    constructor
    · tauto
    · use [c]
      sorry
  case union =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
  case star =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
  case test =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
