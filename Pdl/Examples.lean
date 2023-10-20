import Pdl.Syntax
import Pdl.Semantics
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Relation

open Vector

-- some simple silly stuff
theorem mytaut1 (p : Char) : tautology ((·p) ↣ (·p)) :=
  by
  unfold tautology
  intro W M w
  simp

open Classical

theorem mytaut2 (p : Char) : tautology ((~~·p)↣·p) :=
  by
  unfold tautology evaluatePoint evaluate
  intro W M w
  simp

def myModel : KripkeModel ℕ where
  val _ _ := True
  Rel _ _ v := HEq v 1

theorem mysat (p : Char) : satisfiable (·p) :=
  by
  use ℕ, myModel, 1
  unfold myModel
  simp

-- Segerberg's axioms

-- A1: all propositional tautologies

theorem A2 : tautology (⌈a⌉ ⊤) :=
  by
  unfold tautology
  simp

theorem A3 : tautology ((⌈a⌉(X⋀Y)) ↣ (⌈a⌉X) ⋀ (⌈a⌉Y)) :=
  by
  unfold tautology
  simp
  intro W M w hyp
  constructor
  · intro v
    specialize hyp v
    tauto
  · intro v
    specialize hyp v
    tauto

theorem A4 : tautology ((⌈a;b⌉(·p)) ⟷ (⌈a⌉(⌈b⌉(·p)))) :=
  by
  unfold tautology evaluatePoint evaluate
  intro W M w
  constructor
  · -- left to right
    by_contra hyp
    simp at *
    cases' hyp with hl hr
    contrapose! hr
    intro v w_a_v v1 v_b_v1
    specialize hl v1 v
    apply hl
    exact w_a_v
    exact v_b_v1
  · -- right to left
    by_contra hyp
    simp at *
    cases' hyp with hl hr
    contrapose! hr
    intro v1 v2 w_a_v2 v2_b_v1
    exact hl v1 v2 w_a_v2 v2_b_v1

theorem A5 : tautology ((⌈a ⋓ b⌉X) ⟷ ((⌈a⌉X) ⋀ (⌈b⌉X))) :=
  by
  unfold tautology evaluatePoint evaluate
  intro W M w
  constructor
  · -- left to right
    by_contra hyp
    simp at *
    cases' hyp with lhs rhs
    contrapose! rhs
    constructor
    · -- show ⌈α⌉X
      intro v
      specialize lhs v
      intro (w_a_v : relate M a w v)
      apply lhs
      left
      exact w_a_v
    · -- show ⌈β⌉X
      intro v
      specialize lhs v
      intro (w_b_v : relate M b w v)
      apply lhs
      right
      exact w_b_v
  · -- right to left
    by_contra hyp
    simp at *

theorem A6 (a : Program) (X : Formula) : tautology ((⌈∗a⌉X) ⟷ (X ⋀ (⌈a⌉(⌈∗a⌉X)))) :=
  by
  unfold tautology evaluatePoint evaluate
  intro W M w
  constructor
  · -- left to right
    simp
    intro starAX
    constructor
    · -- show X using refl:
      apply starAX
      exact Relation.ReflTransGen.refl w
    · -- show [α][α∗]X using star.step:
      intro v w_a_v v_1 v_aS_v1
      apply starAX
      apply Relation.ReflTransGen.step w v v_1
      exact w_a_v
      exact v_aS_v1
  · -- right to left
    by_contra hyp
    simp at hyp

example (a b : Program) (X : Formula) :
  (⌈∗(∗a) ⋓ b⌉X) ≡ X ⋀ (⌈a⌉(⌈∗(∗a) ⋓ b⌉ X)) ⋀ (⌈b⌉(⌈∗(∗a) ⋓ b⌉ X)) :=
  by
  unfold semEquiv
  simp
  intro W M w
  sorry

-- related via star ==> related via a finite chain
theorem starIsFinitelyManySteps  (r : α → α → Prop) (x z : α) :
  Relation.ReflTransGen r x z →
    ∃ (n : ℕ) (ys : Vector α n.succ),
      x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (get ys i) (get ys (i.succ)) :=
  by
  intro x_aS_z
  rw [Relation.ReflTransGen.cases_head_iff] at x_aS_z
  cases x_aS_z
  case inl x_is_z =>
    subst x_is_z
    use 0
    use cons x nil
    simp
    rfl
  case inr hyp =>
    rcases hyp with ⟨c, x_r_c, c_rS_z⟩
    rw [Relation.ReflTransGen.cases_head_iff] at c_rS_z
    sorry
    /-
    rcases c_rS_z with ⟨n, ys, IH⟩
    use n.succ
    use cons a ys
    constructor
    · simp
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
        have : (cons a ys).get 1 = ys.head :=
          by
          cases' ys with ys_list hys
          cases ys_list
          simp at hys
          rfl
        rw [this]
        apply a_a_b
      -- first step: a -a-> b
      · intro i
        specialize IH3 i
        have h1 : (a ::ᵥ ys).get (i.succ) = ys.get i :=

          sorry
        rw [h1]
        exact IH3
      -/

-- rest of chain by IH
-- related via star <== related via a finite chain
theorem finitelyManyStepsIsStar (r : α → α → Prop) {n : ℕ} {ys : Vector α (Nat.succ n)} :
  (∀ i : Fin n, r (get ys i) (get ys i.succ)) → Relation.ReflTransGen r ys.head ys.last :=
  by
  simp
  induction n
  case zero =>
    intro _
    have same : ys.head = ys.last := by simp [Vector.last_def, ← Fin.cast_nat_eq_last]
    -- thanks Ruben!
    rw [same]
  case succ n IH =>
    intro lhs
    sorry
     /-
    apply Relation.ReflTransGen.tail
    · have sameLast : ys.last = ys.tail.last := by simp [Vector.last_def]
      -- thanks Ruben!
      rw [sameLast]
      apply IH
      intro i
      specialize lhs i.succ
      simp [Fin.succ_castSucc]
      apply lhs
    · sorry
      -- ys has at least two elements now
      show r ys.head ys.tail.head
      specialize lhs 0
      simp at lhs 
      have foo : ys.get 1 = ys.tail.head :=
        by
        cases' ys with ys_list ys_hyp
        cases' ys_list with a ys
        simp at ys_hyp
        -- ys_hyp is a contradiction
        cases' ys with b ys
        -- thanks Kyle!
        simp at ys_hyp
        injection ys_hyp
        rfl
      rw [← foo]
      apply lhs
     -/

-- related via star <=> related via a finite chain
theorem starIffFinitelyManySteps (r : α → α → Prop) (x z : α) :
    Relation.ReflTransGen r x z ↔
      ∃ (n : ℕ) (ys : Vector α n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (get ys i) (get ys (i.succ)) :=
  by
  constructor
  apply starIsFinitelyManySteps r x z
  intro rhs
  rcases rhs with ⟨n, ys, x_is_head, z_is_last, rhs⟩
  rw [x_is_head]
  rw [z_is_last]
  exact finitelyManyStepsIsStar r rhs

-- related via star <=> related via a finite chain
theorem starIffFinitelyManyStepsModel (W : Type) (M : KripkeModel W) (x z : W) (α : Program) :
    Relation.ReflTransGen (relate M α) x z ↔
      ∃ (n : ℕ) (ys : Vector W n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, relate M α (get ys i) (get ys (i.succ)) :=
  by
  exact starIffFinitelyManySteps (relate M α) x z

-- Example 1 in Borzechowski
theorem inductionAxiom (a : Program) (φ : Formula) : tautology ((φ ⋀ ⌈∗a⌉(φ ↣ (⌈a⌉φ))) ↣ (⌈∗a⌉φ)) :=
  by
  intro W M w
  simp
  intro Mwφ
  intro MwStarImpHyp
  intro x w_starA_x
  rw [starIffFinitelyManyStepsModel] at w_starA_x
  rcases w_starA_x with ⟨n, ys, w_is_head, x_is_last, i_a_isucc⟩
  have claim : ∀ i : Fin n.succ, evaluate M (ys.get i) φ :=
    by
    apply Fin.induction
    · simp
      rw [← w_is_head]
      exact Mwφ
    · sorry
  specialize claim n.succ
  simp at claim 
  have x_is_ys_nsucc : x = ys.get (n + 1) :=
    by
    simp [Vector.last_def] at x_is_last 
    sorry
  rw [x_is_ys_nsucc]
  exact claim
