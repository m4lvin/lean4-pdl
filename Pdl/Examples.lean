import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Vector.Snoc

import Pdl.Semantics
import Pdl.Star

open Vector HasSat

-- some simple silly stuff
theorem mytaut1 (p : Nat) : tautology ((·p) ↣ (·p)) :=
  by
  unfold tautology
  intro W M w
  simp

open Classical

theorem mytaut2 (p : Nat) : tautology ((~~·p)↣·p) :=
  by
  unfold tautology evaluate
  intro W M w
  simp

def myModel : KripkeModel ℕ where
  val _ _ := True
  Rel _ _ v := HEq v 1

theorem mysat (p : Nat) : satisfiable (·p : Formula) :=
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
  unfold tautology evaluate
  intro W M w
  simp
  tauto

theorem A5 : tautology ((⌈a ⋓ b⌉X) ⟷ ((⌈a⌉X) ⋀ (⌈b⌉X))) :=
  by
  unfold tautology evaluate
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
  unfold tautology evaluate
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
  constructor
  · intro lhs
    constructor
    · apply lhs
      exact Relation.ReflTransGen.refl
    · constructor
      · intro v w_a_v u
        intro v_aSubS_w
        apply lhs
        have := ReflTransGen.cases_tail_eq_neq v_aSubS_w
        cases this
        case inl hyp =>
          subst hyp
          sorry
        · sorry
      · intro v w_b_v u v_aSubS_u
        apply lhs
        sorry
  · rintro ⟨w_X, aBox, bBox⟩ v w_aSubS_v
    sorry

-- related via star <=> related via a finite chain
theorem starIffFinitelyManyStepsModel (W : Type) (M : KripkeModel W) (x z : W) (α : Program) :
    Relation.ReflTransGen (relate M α) x z ↔
      ∃ (n : ℕ) (ys : Vector W n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, relate M α (get ys i.castSucc) (get ys (i.succ)) :=
  by
  exact ReflTransGen.iff_finitelyManySteps (relate M α) x z

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
    · intro i
      specialize i_a_isucc i
      intro sat_phi
      sorry
  specialize claim n.succ
  simp at claim
  have x_is_ys_nsucc : x = ys.get (n + 1) :=
    by
    simp [Vector.last_def] at x_is_last
    sorry
  rw [x_is_ys_nsucc]
  sorry -- was: exact claim
