import Pdl.Syntax
import Pdl.Semantics
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.FinCases

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
      exact StarCat.refl w
    · -- show [α][α∗]X using star.step:
      intro v w_a_v v_1 v_aS_v1
      apply starAX
      apply StarCat.step w v v_1
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
theorem starIsFinitelyManySteps {W : Type} {M : KripkeModel W} {x z : W} {α : Program} :
    StarCat (relate M α) x z →
      ∃ (n : ℕ) (ys : Vector W n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, relate M α (get ys i) (get ys (i + 1)) :=
  by
  intro x_aS_z
  induction x_aS_z
  case refl x =>
    use 0
    use cons x nil
    simp
    rfl
  case step a b c a_a_b b_aS_c IH =>
    -- ∃ chain ...
    rcases IH with ⟨n, ys, IH⟩
    use n + 1
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
        have hyp : (cons a ys).get 1 = ys.head :=
          by
          cases' ys with ys_list hys
          cases ys_list
          simp at hys
          rfl
        rw [hyp]
        apply a_a_b
      -- first step: a -a-> b
      · simp
        intro i
        specialize IH3 i
        simp at *
        have h1 : (a ::ᵥ ys).get (i + 1) = ys.get i :=
          by
          simp
          sorry
        rw [h1]
        have h2 : (Vector.get (a ::ᵥ ys) (i + 1 + 1)) = (Vector.get ys (i + 1)) :=
          by
          simp
          sorry
        rw [h2]
        convert IH3
        · simp
        · simp

-- rest of chain by IH
-- related via star <== related via a finite chain
theorem finitelyManyStepsIsStar {W : Type} {M : KripkeModel W} {α : Program} {n : ℕ}
    {ys : Vector W (Nat.succ n)} :
    (∀ i : Fin n, relate M α (get ys i) (get ys (i + 1))) →
      StarCat (relate M α) ys.head ys.last :=
  by
  simp
  induction n
  case zero =>
    intro _
    have same : ys.head = ys.last := by simp [Vector.last_def, ← Fin.cast_nat_eq_last]
    -- thanks Ruben!
    rw [same]
    apply StarCat.refl ys.last
  case succ n IH =>
    intro lhs
    apply StarCat.step
    · -- ys has at least two elements now
      show relate M α ys.head ys.tail.head
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
    · have sameLast : ys.last = ys.tail.last := by simp [Vector.last_def]
      -- thanks Ruben!
      rw [sameLast]
      apply IH
      intro i
      specialize lhs i.succ
      simp [Fin.succ_castSucc]
      apply lhs

-- related via star <=> related via a finite chain
theorem starIffFinitelyManySteps (W : Type) (M : KripkeModel W) (x z : W) (α : Program) :
    StarCat (relate M α) x z ↔
      ∃ (n : ℕ) (ys : Vector W n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, relate M α (get ys i) (get ys (i + 1)) :=
  by
  constructor
  apply starIsFinitelyManySteps
  intro rhs
  rcases rhs with ⟨n, ys, x_is_head, z_is_last, rhs⟩
  rw [x_is_head]
  rw [z_is_last]
  apply finitelyManyStepsIsStar rhs

-- preparation for next lemma
theorem stepStarIsStarStep {W : Type} {M : KripkeModel W} {x z : W} {a : Program} :
    relate M (a;(∗a)) x z ↔ relate M (∗a;a) x z :=
  by
  constructor
  · intro lhs
    unfold relate at lhs
    cases' lhs with y lhs
    simp at lhs 
    cases' lhs with x_a_y y_aS_z
    rw [starIffFinitelyManySteps] at y_aS_z 
    rcases y_aS_z with ⟨n, ys, y_is_head, z_is_last, hyp⟩
    sorry
  · sorry

theorem stepStarIsStarStepBoxes {a : Program} {φ : Formula} : tautology ((⌈a;(∗a)⌉φ) ↣ (⌈∗a;a⌉φ)) :=
  by
  intro W M w
  simp
  intro lhs
  intro x
  sorry

-- Example 1 in Borzechowski
theorem inductionAxiom (a : Program) (φ : Formula) : tautology ((φ ⋀ ⌈∗a⌉(φ ↣ (⌈a⌉φ))) ↣ (⌈∗a⌉φ)) :=
  by
  intro W M w
  simp
  intro Mwφ
  intro MwStarImpHyp
  intro x w_starA_x
  rw [starIffFinitelyManySteps] at w_starA_x
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





-- proven and true, but not actually what I wanted.
theorem starCases {α : Type} (a c : α) (r : α → α → Prop) :
  StarCat r a c ↔ a = c ∨ (a ≠ c ∧ ∃ b, r a b ∧ StarCat r b c) :=
  by
  constructor
  · intro a_rS_c
    have : a = c ∨ a ≠ c
    · tauto
    cases this
    case inl a_is_c =>
      left
      exact a_is_c
    case inr a_neq_c =>
      right
      constructor
      · exact a_neq_c
      · cases a_rS_c
        · exfalso
          tauto
        case step b a_r_b b_Sr_c =>
          use b
  · intro rhs
    cases rhs
    case inl a_is_c =>
      subst a_is_c
      apply StarCat.refl
    case inr hyp =>
      rcases hyp with ⟨_, b, b_rS_c⟩
      apply StarCat.step a b c
      tauto
      tauto

-- almost proven, but Lean does not see the termination
-- Both of these get sizeOf 0
-- #eval sizeOf (StarCat.refl 1 : StarCat (fun x y => x > y) _ _)
-- #eval sizeOf (StarCat.step 3 2 2 (by simp) (StarCat.refl 2) : StarCat (fun x y => x > y) 3 2)
-- It also seems we cannot define our own sizeOf because
-- "StarCat" is a Prop, not a type.
/-
theorem starCasesActuallyRec (α : Type) (a c : α) (r : α → α → Prop) :
  StarCat r a c → a = c ∨ (∃ b, a ≠ b ∧ r a b ∧ StarCat r b c) :=
  by
    intro a_rS_c
    have : a = c ∨ a ≠ c
    · tauto
    cases this
    case inl a_is_c =>
      left
      exact a_is_c
    case inr a_neq_c =>
      right
      cases a_rS_c
      · exfalso
        tauto
      case step b a_r_b b_Sr_c =>
        have IH := starCasesActuallyRec α b c r
        specialize IH b_Sr_c
        cases IH
        case inl b_is_c =>
          subst b_is_c
          use b
        case inr hyp =>
          rcases hyp with ⟨b2, b2_neq_b, b_r_b2, b_rS_c⟩
          have : a = b ∨ a ≠ b
          · tauto
          cases this
          case inl a_is_b =>
            subst a_is_b
            use b2
          case inr a_neq_b =>
            use b
termination_by
  starCasesActuallyRec α a c r star => sizeOf star -- always 0 ???
-/

theorem starCasesActually {α : Type} (a c : α) (r : α → α → Prop) :
  StarCat r a c → a = c ∨ (a ≠ c ∧ ∃ b, a ≠ b ∧ r a b ∧ StarCat r b c) :=
  by
  intro a_rS_c
  induction a_rS_c
  · left
    rfl
  case step a b c a_r_b b_rS_c IH  =>
    have : a = c ∨ a ≠ c
    · tauto
    cases this
    case inl a_is_c =>
      left
      assumption
    case inr a_neq_c =>
      cases IH
      case inl b_is_c =>
        subst b_is_c
        right
        constructor
        · assumption
        sorry
      case inr other =>
        convert other.right
        sorry
