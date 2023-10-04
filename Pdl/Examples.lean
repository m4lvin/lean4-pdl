import Oneshot.Syntax
import Oneshot.Semantics
import Mathbin.Data.Vector.Basic
import Mathbin.Tactic.FinCases
import Mathbin.Tactic.NormFin
import Mathbin.Tactic.NormNum

#align_import examples

open Vector

-- some simple silly stuff
theorem mytaut1 (p : Char) : Tautology (Formula.atomProp p↣Formula.atomProp p) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  tauto
#align mytaut1 mytaut1

open Classical

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mytaut2 (p : Char) : Tautology ((~~·p)↣·p) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  classical tauto
#align mytaut2 mytaut2

def myModel : KripkeModel ℕ where
  val _ _ := True
  Rel _ _ v := HEq v 1
#align myModel myModel

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mysat (p : Char) : Satisfiable (·p) :=
  by
  unfold Satisfiable
  exists ℕ
  exists myModel
  exists 1
  unfold EvaluatePoint Evaluate
#align mysat mysat

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- Segerberg's axioms
-- A1
-- all propositional tautologies
theorem A2 (a : Program) (X Y : Formula) : Tautology (⌈a⌉ ⊤) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  tauto
#align A2 A2

theorem A3 (a : Program) (X Y : Formula) : Tautology (⌈a⌉ (X⋀Y)↣⌈a⌉ X⋀⌈a⌉ Y) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  by_contra hyp
  cases' hyp with hl hr
  contrapose! hr
  constructor
  · intro v1 ass; exact (hl v1 ass).1
  · intro v2 ass; exact (hl v2 ass).2
#align A3 A3

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem A4 (a b : Program) (p : Char) : Tautology (⌈a;b⌉ (·p)⟷⌈a⌉ (⌈b⌉ (·p))) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  constructor
  · -- left to right
    by_contra hyp
    cases' hyp with hl hr
    contrapose! hr
    intro v w_a_v v1 v_b_v1
    specialize hl v1
    apply hl
    unfold Relate
    use v
    constructor
    · exact w_a_v
    · exact v_b_v1
  · -- right to left
    by_contra hyp
    cases' hyp with hl hr
    contrapose! hr
    intro v2 w_ab_v2
    unfold Relate at w_ab_v2 
    rcases w_ab_v2 with ⟨v1, w_a_v1, v1_b_v2⟩
    exact hl v1 w_a_v1 v2 v1_b_v2
#align A4 A4

theorem A5 (a b : Program) (X : Formula) : Tautology (⌈Program.union a b⌉ X⟷(⌈a⌉ X⋀⌈b⌉ X)) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  constructor
  · -- left to right
    by_contra hyp
    cases' hyp with lhs rhs
    contrapose! rhs
    constructor
    · -- show ⌈α⌉X
      intro v
      specialize lhs v
      intro (w_a_v : Relate M a w v)
      unfold Relate at lhs 
      apply lhs
      left
      exact w_a_v
    · -- show ⌈β⌉X
      intro v
      specialize lhs v
      intro (w_b_v : Relate M b w v)
      unfold Relate at lhs 
      apply lhs
      right
      exact w_b_v
  · -- right to left
    by_contra hyp
    cases' hyp with rhs lhs
    contrapose! lhs
    cases' rhs with rhs_a rhs_b
    intro v; intro m_ab_v
    specialize rhs_a v
    specialize rhs_b v
    unfold Relate at m_ab_v 
    cases m_ab_v
    · apply rhs_a m_ab_v
    · apply rhs_b m_ab_v
#align A5 A5

theorem A6 (a : Program) (X : Formula) : Tautology (⌈∗a⌉ X⟷(X⋀⌈a⌉ (⌈∗a⌉ X))) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  constructor
  · -- left to right
    intro lhs
    contrapose! lhs
    intro starAX
    constructor
    · -- show X using refl:
      apply starAX
      unfold Relate
      simp
      exact StarCat.refl w
    · -- show [α][α∗]X using star.step:
      intro v w_a_v v_1 v_aS_v1
      apply starAX
      unfold Relate
      apply StarCat.step w v v_1
      exact w_a_v
      unfold Relate at v_aS_v1 
      exact v_aS_v1
  · -- right to left
    by_contra hyp
    cases' hyp with hl hr
    contrapose! hr
    cases' hl with w_X w_aSaX
    intro v w_aStar_v
    unfold Relate at w_aStar_v 
    simp at w_aStar_v 
    cases w_aStar_v
    case refl => exact w_X
    case step w y v w_a_y y_aS_v =>
      unfold Relate at w_aSaX 
      simp at w_aSaX 
      exact w_aSaX y w_a_y v y_aS_v
#align A6 A6

example (a b : Program) (X : Formula) : ⌈∗(∗a) ∪ b⌉ X≡X⋀⌈a⌉ (⌈∗(∗a) ∪ b⌉ X)⋀⌈b⌉ (⌈∗(∗a) ∪ b⌉ X) :=
  by
  unfold SemEquiv
  unfold Evaluate Relate
  simp
  intro W M w
  sorry

-- related via star ==> related via a finite chain
theorem starIsFinitelyManySteps {W : Type} {M : KripkeModel W} {x z : W} {α : Program} :
    StarCat (Relate M α) x z →
      ∃ (n : ℕ) (ys : Vector W n.succ),
        x = ys.headI ∧ z = ys.getLast ∧ ∀ i : Fin n, Relate M α (get ys i) (get ys (i + 1)) :=
  by
  intro x_aS_z
  induction x_aS_z
  case refl x =>
    use 0
    use cons x nil
    simp [Vector.last_def]
  case step a b c a_a_b b_aS_c
    IH =>
    -- ∃ chain ...
    rcases IH with ⟨n, ys, IH⟩
    use n + 1
    use cons a ys
    constructor
    · finish
    rcases IH with ⟨IH1, IH2, IH3⟩
    constructor
    · rw [IH2]
      simp [Vector.last_def]
      rw [← Fin.succ_last]
      rw [Vector.get_cons_succ a ys]
    · -- i : fin (n + 1)
      apply Fin.cases
      · simp
        rw [IH1] at a_a_b 
        have hyp : (cons a ys).get? 1 = ys.head :=
          by
          cases' ys with ys_list hys
          cases ys_list
          simpa using hys
          rfl
        rw [hyp]
        apply a_a_b
      -- first step: a -a-> b
      · simp
        intro i
        specialize IH3 i
        have h1 : (a ::ᵥ ys).get? (Fin.castSuccEmb i.succ) = ys.nth i :=
          by
          rw [← Fin.succ_castSucc]
          rw [← Vector.get_cons_succ a ys]
          simp
        have h2 : ys.nth i.succ = ys.nth (i + 1) :=
          by
          rw [← Vector.get_cons_succ a ys]
          simp
        rw [h1]
        rw [h2]
        apply IH3
#align starIsFinitelyManySteps starIsFinitelyManySteps

-- rest of chain by IH
-- related via star <== related via a finite chain
theorem finitelyManyStepsIsStar {W : Type} {M : KripkeModel W} {α : Program} {n : ℕ}
    {ys : Vector W (Nat.succ n)} :
    (∀ i : Fin n, Relate M α (get ys i) (get ys (i + 1))) →
      StarCat (Relate M α) ys.headI ys.getLast :=
  by
  simp
  induction n
  case zero =>
    intro lhs
    have same : ys.head = ys.last := by simp [Vector.last_def, ← Fin.cast_nat_eq_last]
    -- thanks Ruben!
    rw [same]
    apply StarCat.refl ys.last
  case succ n IH =>
    intro lhs
    apply StarCat.step
    · -- ys has at least two elements now
      show Relate M α ys.head ys.tail.head
      specialize lhs 0
      simp at lhs 
      have foo : ys.nth 1 = ys.tail.head :=
        by
        cases' ys with ys_list ys_hyp
        cases' ys_list with a ys
        simpa using ys_hyp
        -- ys_hyp is a contradiction
        cases' ys with b ys
        simp at ys_hyp ; injection ys_hyp; contradiction
        -- thanks Kyle!
        rfl
      rw [← foo]
      apply lhs
    · have sameLast : ys.last = ys.tail.last := by simp [Vector.last_def]
      -- thanks Ruben!
      rw [sameLast]
      apply IH
      intro i
      specialize lhs i.succ
      simp [Fin.succ_castSucc]
      apply lhs
#align finitelyManyStepsIsStar finitelyManyStepsIsStar

-- related via star <=> related via a finite chain
theorem starIffFinitelyManySteps (W : Type) (M : KripkeModel W) (x z : W) (α : Program) :
    StarCat (Relate M α) x z ↔
      ∃ (n : ℕ) (ys : Vector W n.succ),
        x = ys.headI ∧ z = ys.getLast ∧ ∀ i : Fin n, Relate M α (get ys i) (get ys (i + 1)) :=
  by
  constructor
  apply starIsFinitelyManySteps
  intro rhs
  rcases rhs with ⟨n, ys, x_is_head, z_is_last, rhs⟩
  rw [x_is_head]
  rw [z_is_last]
  apply finitelyManyStepsIsStar rhs
#align starIffFinitelyManySteps starIffFinitelyManySteps

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- preparation for next lemma
theorem stepStarIsStarStep {W : Type} {M : KripkeModel W} {x z : W} {a : Program} :
    Relate M (a;∗a) x z ↔ Relate M (∗a;a) x z :=
  by
  constructor
  · intro lhs
    unfold Relate at lhs 
    cases' lhs with y lhs
    simp at lhs 
    cases' lhs with x_a_y y_aS_z
    rw [starIffFinitelyManySteps] at y_aS_z 
    rcases y_aS_z with ⟨n, ys, y_is_head, z_is_last, hyp⟩
    unfold Relate
    let newY := last (cons x (remove_nth (coe n) ys))
    use newY
    constructor
    · rw [starIffFinitelyManySteps]
      use n
      use cons x (remove_nth (coe n) ys)
      simp
      -- takes care of head and last :-)
      intro i
      cases i
      cases i_val
      case
        zero =>
        -- if i=0 use x_a_y
        simp
        rw [y_is_head] at x_a_y 
        have hyp : ys.head = (remove_nth (↑n) ys).get? ⟨0, _⟩ := by sorry
        rw [← hyp]
        apply x_a_y
      · -- if i>0 use hyp i-1,
        simp
        sorry
    -- TODO: apply hyp ,
    · rw [z_is_last]
      -- TODO apply hyp ↑n,
      sorry
  · sorry
#align stepStarIsStarStep stepStarIsStarStep

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem stepStarIsStarStepBoxes {a : Program} {φ : Formula} : Tautology (⌈a;∗a⌉ φ↣⌈∗a;a⌉ φ) :=
  by
  simp
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  simp
  intro lhs
  intro x
  rw [← stepStarIsStarStep]
  apply lhs
#align stepStarIsStarStepBoxes stepStarIsStarStepBoxes

-- Example 1 in Borzechowski
theorem inductionAxiom (a : Program) (φ : Formula) : Tautology (φ⋀⌈∗a⌉ (φ↣⌈a⌉ φ)↣⌈∗a⌉ φ) :=
  by
  unfold Tautology EvaluatePoint Evaluate
  intro W M w
  simp
  intro Mwφ
  intro MwStarImpHyp
  intro x w_starA_x
  unfold Relate at w_starA_x 
  simp at w_starA_x 
  rw [starIffFinitelyManySteps] at w_starA_x 
  rcases w_starA_x with ⟨n, ys, w_is_head, x_is_last, i_a_isucc⟩
  have claim : ∀ i : Fin n.succ, Evaluate M (ys.nth ↑i) φ :=
    by
    apply Fin.induction
    · simp
      rw [← w_is_head]
      exact Mwφ
    · simp
      sorry
  specialize claim n.succ
  simp at claim 
  have x_is_ys_nsucc : x = ys.nth (n + 1) :=
    by
    simp [Vector.last_def] at x_is_last 
    sorry
  rw [x_is_ys_nsucc]
  exact claim
#align inductionAxiom inductionAxiom

