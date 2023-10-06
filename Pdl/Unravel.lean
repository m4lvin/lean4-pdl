import Pdl.Syntax
import Pdl.Discon
import Pdl.Semantics

-- UNRAVELING
-- | New Definition 10
@[simp]
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

-- Like Lemma 4 from Borzechowski, but using "unravel" instead of a local tableau with n-nodes.
-- see https://malv.in/2020/borzechowski-pdl/Borzechowski1988-PDL-translation-Gattinger2020.pdf#lemma.4
-- TODO: maybe simplify by not having a context X' here / still as useful for showing soundness of ~* rule?
-- TODO: analogous lemma for the box case? and * rule?
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
    subst X_def
    constructor
    · rfl
    constructor
    · assumption
    · use [·A]
      unfold Formula.boxes
      simp
      constructor
      · right
        exact List.mem_of_mem_head? rfl
      · unfold Program.steps
        exact w_a_v
  case sequence b c =>
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
    · unfold vDash.SemImplies at *
      unfold modelCanSemImplyForm at *
      simp at *
      use v
    rcases IHb with ⟨Y, Y_in, w_conY, as, nBas_in_Y, w_as_u⟩
    use Y
    constructor
    simp at *
    assumption
    -- TODO "If n > 0 then we are done, otherwise again apply the IH to Z"
    constructor
    · tauto
    · use [c]
      constructor
      · sorry
      ·
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
