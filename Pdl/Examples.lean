import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Vector.Snoc

import Pdl.Semantics
import Pdl.Star

/-! # Examples

Easy *semantic* examples. Nothing here is about tableaux yet.
-/
open HasSat

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

/-- An infinite Kripke model with ℕ as the set of states.
All atomic propositions alre true at all states, and all
atomic programs lead from any state to state 1. -/
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

set_option linter.unusedVariables false -- for `contrapose! rhs` below

theorem A5 : tautology ((⌈a ⋓ b⌉X) ⟷ ((⌈a⌉X) ⋀ (⌈b⌉X))) :=
  by
  unfold tautology evaluate
  aesop

theorem A6 (a : Program) (φ : Formula) : tautology ((⌈∗a⌉φ) ⟷ (φ ⋀ (⌈a⌉(⌈∗a⌉φ)))) :=
  by
  unfold tautology evaluate
  intro W M w
  constructor
  · -- left to right
    simp
    intro starAφ
    constructor
    · -- show φ using refl:
      apply starAφ
      exact Relation.ReflTransGen.refl
    · -- show [α][α∗]φ using cases_head_iff:
      intro v w_a_v v_1 v_aS_v1
      apply starAφ
      rw [Relation.ReflTransGen.cases_head_iff]
      right
      use v
  · -- right to left
    simp only [evaluate, relate, not_forall, not_and, not_exists,
      Decidable.not_not, and_imp]
    intro w_φ hyp v w_aS_v
    rcases Relation.ReflTransGen.cases_head w_aS_v <;> aesop

example (a b : Program) (X : Formula) :
  (⌈∗((∗a) ⋓ b)⌉X) ≡ X ⋀ (⌈a⌉(⌈∗((∗a) ⋓ b)⌉ X)) ⋀ (⌈b⌉(⌈∗((∗a) ⋓ b)⌉ X)) :=
  by
  intro W M w
  have claim : ∀ v, Relation.ReflTransGen (relate M ((∗a)⋓b)) w v ↔
      ( w = v
      ∨ ∃ u, relate M a w u ∧ Relation.ReflTransGen (relate M ((∗a)⋓b)) u v
      ∨ ∃ u, relate M b w u ∧ Relation.ReflTransGen (relate M ((∗a)⋓b)) u v ) := by
    intro v
    constructor
    · intro lhs
      have := ReflTransGen.cases_tail_eq_neq lhs
      rcases this with _ | ⟨w_ne_v, y, w_ne_y, w_y, y_v⟩
      · left; assumption
      · simp only [relate] at w_y
        cases w_y
        case inl hyp =>
          have := ReflTransGen.cases_tail_eq_neq hyp
          rcases this with _ | ⟨w_ne_y, z, w_ne_z, w_z, z_y⟩
          · aesop
          · right
            use z
            left
            constructor
            · exact w_z
            · apply @Relation.ReflTransGen.trans W _ z y v
              · apply Relation.ReflTransGen.single
                aesop
              · exact y_v
        · right
          use v
          right
          use y
    · rintro (w_eq_v | ⟨u, (⟨w_u, w_v⟩  | ⟨u, w_u, u_v⟩ )⟩ )
      · aesop
      · apply @Relation.ReflTransGen.trans W _ w u v
        · apply Relation.ReflTransGen.single
          simp only [relate]
          left
          apply Relation.ReflTransGen.single
          exact w_u
        · exact w_v
      · apply @Relation.ReflTransGen.trans W _ w u v
        · apply Relation.ReflTransGen.single
          simp only [relate]
          right
          exact w_u
        · exact u_v
  constructor
  · intro lhs
    constructor
    · simp_all
    · constructor
      · intro v w_a_v u
        intro v_aSubS_w
        aesop
      · intro v w_b_v u v_aSubS_u
        apply lhs
        aesop
  · rintro ⟨w_X, aBox, bBox⟩ v w_aSubS_v
    aesop

/-- The induction axiom is semantically valid. Example 1 in [Bor88]. -/
theorem inductionAxiom (a : Program) (φ : Formula) : tautology ((φ ⋀ ⌈∗a⌉(φ ↣ (⌈a⌉φ))) ↣ (⌈∗a⌉φ)) :=
  by
  intro W M w
  simp only [evaluate, relate, not_forall, not_and, not_exists, not_not, and_imp]
  intro Mwφ  MwStarImpHyp
  intro x w_starA_x
  induction w_starA_x
  case refl => assumption
  case tail u v w_aS_u u_a_v IH =>
    apply MwStarImpHyp
    · exact w_aS_u
    · exact IH
    · assumption
