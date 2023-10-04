import Mathbin.Tactic.Linarith.Frontend
import Oneshot.Syntax
import Oneshot.Discon
import Oneshot.Semantics

#align_import unravel

-- UPLUS
-- UPLUS
@[simp]
def pairunion : List (List Formula) → List (List Formula) → List (List Formula)
  | xls, yls => List.join (xls.map fun xl => yls.map fun yl => xl ++ yl)
#align pairunion pairunion

def pairunionFinset : Finset (Finset Formula) → Finset (Finset Formula) → Finset (Finset Formula)
  | X, Y => {X.biUnion fun ga => Y.biUnion fun gb => ga ∪ gb}
#align pairunionFinset pairunionFinset

infixl:77 "⊎" => pairunion

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- UNRAVELING
-- | New Definition 10
def unravel : Formula → List (List Formula)
  |-- diamonds:
    ~⌈·a⌉ P =>
    [[~⌈·a⌉ P]]
  |-- remove theF here again. fishy? :-/
    ~⌈Program.union p1 p2⌉ P =>
    unravel (~⌈p1⌉ P) ∪ unravel (~⌈p2⌉ P)
  | ~⌈?Q⌉ P => [[Q]]⊎unravel (~P)
  | ~⌈a;b⌉ P => unravel (~⌈a⌉ (⌈b⌉ P))
  | ~†P => ∅
  | ~⌈∗a⌉ P => unravel (~P) ∪ unravel (~⌈a⌉ (†⌈∗a⌉ P))
  |-- boxes:
      ⌈·a⌉
      P =>
    [[⌈·a⌉ P]]
  | ⌈Program.union a b⌉ P => unravel (⌈a⌉ P)⊎unravel (⌈b⌉ P)
  | ⌈?Q⌉ P => [[~Q]] ∪ unravel P
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
termination_by' ⟨_, measure_wf mOfFormula⟩
#align unravel unravel

theorem disconAnd {XS YS} : discon (XS⊎YS)≡discon XS⋀discon YS :=
  by
  unfold SemEquiv
  intro W M w
  unfold Evaluate
  rw [disconEval XS (by rfl)]
  rw [disconEval YS (by rfl)]
  rw [disconEval (XS⊎YS) (by rfl)]
  unfold pairunion
  simp at *
  constructor
  · -- →
    intro lhs
    rcases lhs with ⟨XY, ⟨X, ⟨X_in, ⟨Y, Y_in, X_Y_is_XY⟩⟩⟩, satXY⟩
    rw [← X_Y_is_XY] at satXY 
    simp at satXY 
    constructor
    · use X; constructor; use X_in; intro f f_in; apply satXY; tauto
    · use Y; constructor; use Y_in; intro f f_in; apply satXY; tauto
  · -- ←
    intro rhs
    rcases rhs with ⟨⟨X, X_in, satX⟩, ⟨Y, Y_in, satY⟩⟩
    use X ++ Y
    use X; use X_in
    use Y; use Y_in
    intro f
    finish
#align disconAnd disconAnd

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
def nsub : Formula → List Formula
  |-- diamonds:
    ~⌈α⌉ P =>
    nsub P
  | ~†P => [~P]
  | †P => [P]
  |-- boxes:
      ⌈α⌉
      P =>
    nsub P
  |-- all other formulas:
    ·c =>
    ∅
  | ~·c => ∅
  | ~⊥ => ∅
  | ⊥ => ∅
  | ~~f => nsub f
  | f⋀g => nsub f ++ nsub g
  | ~f⋀g => nsub f ++ nsub g
#align nsub nsub

theorem likeLemmaFour :
    ∀ (W M) (a : Program) (w v : W) (X' X : List Formula) (P : Formula),
      X = X' ++ {~⌈a⌉ P} →
        (M, w)⊨Con X → Relate M a w v → (M, v)⊨(~P) → ∃ Y ∈ {X'}⊎unravel (~⌈a⌉ P), (M, w)⊨Con Y :=
  by
  -- TODO: ∧ ∃ a_1 ... a_n: ~⌈a_1⌉...⌈a_n⌉P ∈ Y ∧ relate M (a_1;…;a_n) w v
  intro W M a
  induction a
  case atom_prog A =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP
    use X
    -- "The claim holds with Y = X" says MB.
    unfold unravel
    simp
    constructor
    · use X'
      constructor
      fconstructor; rfl
      assumption
    assumption
  case sequence b c IHb
    IHc =>
    intro w v X' X P X_def w_sat_X w_bc_v v_sat_nP
    unfold Relate at w_bc_v 
    rcases w_bc_v with ⟨u, w_b_u, u_c_v⟩
    subst X_def
    specialize IHb w u X' (X' ++ {~⌈b⌉ (⌈c⌉ P)}) (⌈c⌉ P) (by rfl) _ w_b_u _
    · sorry
    · sorry
    -- need (M, u)⊨~⌈c⌉ P
    rcases IHb with ⟨Y, Y_in, w_conY⟩
    use Y
    constructor
    sorry
    exact w_conY
  case union =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
  case star =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
  case test =>
    intro w v X' X P X_def w_sat_X w_a_v v_sat_nP; subst X_def
    sorry
#align likeLemmaFour likeLemmaFour

theorem newLemmaTwo : ∀ N P, mOfFormula P = N → Tautology (Con (nsub P)↣P⟷discon (unravel P)) :=
  by
  intro N
  apply Nat.strong_induction_on N
  intro n IH
  unfold Tautology at *
  unfold EvaluatePoint at *
  intro P
  cases P
  case bottom => unfold Evaluate unravel; simp; unfold Evaluate; simp
  case atom_prop pchar => unfold Evaluate unravel; simp; unfold Evaluate; simp
  case neg
    f =>
    -- formula.neg
    unfold Evaluate
    simp at *
    cases f
    -- TODO: negated forms, hence splitting cases of f again here!
    all_goals sorry
  case and f
    g =>
    -- formula.and
    unfold Evaluate;
    simp at *
    unfold unravel
    rw [disconsingle]
    unfold Evaluate; simp
    tauto
  case box a
    f =>
    -- formula.box
    unfold Evaluate;
    simp at *
    cases a
    -- split cases for different programs
    case atom_prog a =>
      unfold unravel nsub Evaluate discon Con
      tauto
    case sequence α β =>
      unfold unravel Con nsub
      intro n_def
      intro W M w
      intro Mw_nsub_f
      specialize IH (mOfFormula (⌈α⌉ (⌈β⌉ f))) _;
      · unfold mOfFormula; rw [← n_def]; unfold mOfProgram; linarith
      specialize IH (⌈α⌉ (⌈β⌉ f)) (by rfl) W M w
      unfold Evaluate at IH 
      simp at *
      specialize IH Mw_nsub_f
      constructor
      · intro lhs
        cases' IH with IHa Ihb
        apply IHa
        unfold Relate at lhs 
        intro v w_a_v v1 v_b_v1
        specialize lhs v1
        apply lhs
        use v
        tauto
      · intro rhs v w_ab_v
        unfold Relate at w_ab_v 
        rcases w_ab_v with ⟨z, w_a_y, z_b_v⟩
        cases IH
        apply IH_right rhs
        use w_a_y
        use z_b_v
    case union α β =>
      unfold unravel Con nsub
      intro n_def
      intro W M w
      intro Mw_nsub_f
      rw [disconAnd]; unfold Evaluate
      have IHa :=
        IH (mOfFormula (⌈α⌉ f)) (by unfold mOfFormula; rw [← n_def]; unfold mOfProgram; linarith)
      have IHb :=
        IH (mOfFormula (⌈β⌉ f)) (by unfold mOfFormula; rw [← n_def]; unfold mOfProgram; linarith)
      specialize IHa (⌈α⌉ f) (by rfl) W M w
      specialize IHb (⌈β⌉ f) (by rfl) W M w
      unfold Evaluate at IHa IHb 
      simp at *
      specialize IHa Mw_nsub_f
      specialize IHb Mw_nsub_f
      cases' IHa with IHa1 IHa2
      cases' IHb with IHb1 IHb2
      constructor
      · intro lhs
        unfold Relate at lhs 
        constructor
        · apply IHa1; intro v w_a_v; apply lhs; tauto
        · apply IHb1; intro v w_b_v; apply lhs; tauto
      · intro af bf v w_ab_v
        unfold Relate at w_ab_v 
        cases' w_ab_v with w_a_v w_b_v
        · apply IHa2 (by tauto); tauto
        · apply IHb2 (by tauto); tauto
    case star =>
      unfold unravel Con nsub
      intro n_def
      intro W M w
      intro Mw_nsub_f
      rw [disconAnd]
      unfold Evaluate
      constructor
      -- LEFT TO RIGHT
      · intro box_astar_f
        constructor
        · have IHf :=
            IH (mOfFormula f) (by subst n_def; unfold mOfProgram; linarith) f (by rfl) W M w
          -- (1)
          unfold Evaluate at IHf ;
          simp at *
          specialize IHf Mw_nsub_f
          cases IHf
          apply IHf_left
          apply box_astar_f
          unfold Relate
          fconstructor
        · have IHf :=
            IH (mOfFormula (⌈a⌉ (†⌈∗a⌉ f))) (by subst n_def; unfold mOfFormula mOfProgram; linarith)
              (⌈a⌉ (†⌈∗a⌉ f)) (by rfl) W M w
          -- (2)
          unfold Evaluate at IHf ;
          simp at *
          unfold Evaluate at IHf 
          specialize IHf box_astar_f
          cases IHf
          apply IHf_left
          unfold Relate at *
          simp at *
          intro v w_a_v v' v_aS_v'
          apply box_astar_f
          fconstructor
          use v
          use w_a_v
          use v_aS_v'
      -- RIGHT TO LEFT
      · intro rhs v
        rcases rhs with ⟨w_unravel_f, w_aSaf⟩
        intro w_aS_v
        unfold Relate at w_aS_v 
        simp at w_aS_v 
        cases w_aS_v
        -- start = refl or at least one step
        case
          refl =>
          have IHf :=
            IH (mOfFormula f) (by subst n_def; unfold mOfProgram; linarith) f (by rfl) W M w
          -- (1)
          unfold Evaluate at IHf ;
          simp at *
          specialize IHf Mw_nsub_f
          cases IHf
          apply IHf_right
          apply w_unravel_f
        case step w y z w_a_y
          y_aS_z =>
          have IHf :=
            IH (mOfFormula (⌈a⌉ (†⌈∗a⌉ f))) (by subst n_def; unfold mOfProgram mOfFormula; linarith)
              (⌈a⌉ (†⌈∗a⌉ f)) (by rfl) W M w
          -- (2)
          unfold Evaluate at IHf ;
          simp at *
          specialize IHf _;
          · unfold Evaluate Relate
            simp
            intro v w_aS_v
            -- ????
            sorry
          cases IHf
          apply IHf_right w_aSaf
          use w_a_y
          unfold Relate; use y_aS_z
    case test f => sorry
  case nstar =>
    intro n_def W M w
    unfold Evaluate unravel
    simp
    unfold Evaluate
    simp
#align newLemmaTwo newLemmaTwo

