import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Relation

/-- A version of `Relation.ReflTransGen.cases_tail` also giving (in)equalities. -/
-- TODO: add/make this an ↔ maybe?
theorem ReflTransGen.cases_tail_eq_neq {r : α → α → Prop} (h : Relation.ReflTransGen r x z) :
    x = z ∨ (x ≠ z ∧ ∃ y, x ≠ y ∧ r x y ∧ Relation.ReflTransGen r y z) := by
  induction h using Relation.ReflTransGen.head_induction_on
  · left
    rfl
  case head a b a_r_b b_r_z IH_b_z =>
    cases Classical.em (a = b)
    case inl a_is_b =>
      subst a_is_b
      cases IH_b_z
      case inl a_is_z =>
        left
        assumption
      case inr IH =>
        right
        assumption
    case inr a_neq_b =>
      cases IH_b_z
      case inl a_is_z =>
        subst a_is_z
        right
        constructor
        · assumption
        · use b
      case inr IH =>
        cases Classical.em (a = z)
        · left
          assumption
        · right
          constructor
          · assumption
          · use b

/-- `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ xₙ = b` implies `ReflTransGen r a b` -/
theorem ReflTransGen.to_finitelyManySteps {r : α → α → Prop} (h : Relation.ReflTransGen r x z) :
    ∃ (n : ℕ) (ys : Vector α n.succ),
      x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)) := by

  induction h using Relation.ReflTransGen.head_induction_on
  case refl =>
    use 0, Vector.cons z Vector.nil
    aesop
  case head a b a_r_b b_rS_z IH_b_z =>
    rcases IH_b_z with ⟨m, zs, b_is_head_zs, z_is_last_zs, zs_steps⟩
    use m + 1
    use a ::ᵥ zs
    simp only [Vector.head_cons, Vector.get_cons_succ, true_and]
    constructor
    · aesop
    · intro i
      induction i using Fin.induction
      all_goals aesop

/-- `ReflTransGen r a b` implies that `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ xₙ = b` -/
theorem ReflTransGen.from_finitelyManySteps (r : α → α → Prop) {n : ℕ} :
    ∀ (x z : α) (ys : Vector α (Nat.succ n)),
      (x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)))
        → Relation.ReflTransGen r x z := by
  induction n
  case zero =>
    rintro x z ys ⟨x_is_head, z_is_last, _⟩
    have : x = z := by
      subst_eqs
      simp_all [Vector.head, Vector.last, Fin.last]
    rw [this]
  case succ n IH =>
    rintro x z ys ⟨x_is_head, z_is_last, steprel⟩
    let y := ys.tail.head -- WAIT bad, tail may be empty?
    rw [Relation.ReflTransGen.cases_head_iff]
    right
    use y
    constructor
    · specialize steprel 0
      simp only [Fin.castSucc_zero, Vector.get_zero, Fin.succ_zero_eq_one] at steprel
      rw [← x_is_head] at steprel
      convert steprel
      cases ys using Vector.inductionOn
      case cons y ys hyp =>
        cases ys using Vector.inductionOn
        rfl
    · apply IH y z ys.tail
      simp only [Vector.get_tail_succ, true_and]
      constructor
      · have sameLast : ys.tail.last = ys.last := by
          cases ys using Vector.inductionOn
          case cons y ys hyp =>
            cases ys using Vector.inductionOn
            rfl
        rw [sameLast]
        exact z_is_last
      · intro i
        specialize steprel i.succ
        induction i
        all_goals aesop

/-- `ReflTransGen r a b` is equivalent to `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ = b` -/
theorem ReflTransGen.iff_finitelyManySteps (r : α → α → Prop) (x z : α) :
    Relation.ReflTransGen r x z ↔
      ∃ (n : ℕ) (ys : Vector α n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)) :=
  ⟨ReflTransGen.to_finitelyManySteps,
  fun ⟨_, ys, x_is_head, z_is_last, rhs⟩ =>
    ReflTransGen.from_finitelyManySteps r x z ys ⟨x_is_head, z_is_last, rhs⟩⟩
