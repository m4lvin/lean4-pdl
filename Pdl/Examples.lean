import Pdl.Syntax
import Pdl.Semantics
import Pdl.Star
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Vector.Snoc
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

theorem A4 : tautology ((⌈a;'b⌉(·p)) ⟷ (⌈a⌉(⌈b⌉(·p)))) :=
  by
  unfold tautology evaluatePoint evaluate
  intro W M w
  simp
  tauto

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
    simp only [evaluate]
    tauto

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
      exact Relation.ReflTransGen.refl
    · -- show [α][α∗]X using cases_head_iff:
      intro v w_a_v v_1 v_aS_v1
      apply starAX
      rw [Relation.ReflTransGen.cases_head_iff]
      right
      use v
  · -- right to left
    simp

example (a b : Program) (X : Formula) :
  (⌈∗(∗a) ⋓ b⌉X) ≡ X ⋀ (⌈a⌉(⌈∗(∗a) ⋓ b⌉ X)) ⋀ (⌈b⌉(⌈∗(∗a) ⋓ b⌉ X)) :=
  by
  unfold semEquiv
  intro W M w
  simp
  sorry

theorem last_snoc {m b} {ys : Vector α m} : b = last (snoc ys b) :=
  by
  sorry

-- related via star ==> related via a finite chain
theorem starIsFinitelyManySteps (r : α → α → Prop) (x z : α) :
  Relation.ReflTransGen r x z →
    ∃ (n : ℕ) (ys : Vector α n.succ),
      x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (get ys i) (get ys (i.succ)) :=
  by
  intro x_aS_z
  induction x_aS_z
  case refl =>
    use 0
    use cons x nil
    simp
    rfl
  case tail a b a_r_b b_rS_z IH =>
    rcases IH with ⟨n, ys,⟨x_def, a_def, rel_steps⟩⟩
    subst x_def
    subst a_def
    use n.succ
    use snoc ys b
    simp at *
    constructor
    · cases ys using Vector.inductionOn
      simp
    · constructor
      · exact last_snoc
      · sorry

-- related via star ==> related via a finite chain
theorem starIsFinitelyManySteps_attempt (r : α → α → Prop) (x z : α) :
  Relation.ReflTransGen r x z →
    ∃ (n : ℕ) (ys : Vector α n.succ),
      x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (get ys i) (get ys (i.succ)) :=
  by
  intro x_aS_z
  have := starCases x_aS_z
  cases this
  case inl hyp =>
    subst hyp
    use 0
    use cons x nil
    simp
    rfl
  case inr hyp =>
   rcases hyp with ⟨x_neq_z, ⟨y, x_neq_y, x_r_y, y_rS_z⟩⟩
   -- rcases IH_b_z with ⟨n, ys,⟨ y_def, z_def, rel_steps⟩⟩
   induction y_rS_z using Relation.ReflTransGen.head_induction_on
   case refl =>
    use 1
    use cons x (cons z nil)
    simp
    constructor
    · rfl
    · exact x_r_y
   case head a b a_r_b b_rS_z IH_b_z =>
    -- apply IH_b_z
    -- rcases IH_b_z with ⟨n, ys,⟨ y_def, z_def, rel_steps⟩⟩
    -- subst y_def
    -- subst z_def
    -- use n.succ
    -- use cons x ys
    simp at *
    sorry

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
