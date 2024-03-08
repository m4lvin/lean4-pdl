import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Relation

-- Mathlib this?
theorem starCases {r : α → α → Prop} {x z : α} :
  Relation.ReflTransGen r x z → (x = z ∨ (x ≠ z ∧ ∃ y, x ≠ y ∧ r x y ∧ Relation.ReflTransGen r y z)) :=
  by
  intro x_rS_z
  induction x_rS_z using Relation.ReflTransGen.head_induction_on
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

-- related via star ==> related via a finite chain
theorem starIsFinitelyManySteps (r : α → α → Prop) (x z : α) :
  Relation.ReflTransGen r x z →
    ∃ (n : ℕ) (ys : Vector α n.succ),
      x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)) :=
  by
  intro x_aS_z
  induction x_aS_z using Relation.ReflTransGen.head_induction_on
  case refl =>
    use 0, Vector.cons z Vector.nil
    aesop
  case head a b a_r_b b_rS_z IH_b_z =>
    rcases IH_b_z with ⟨m, zs, b_is_head_zs, z_is_last_zs, zs_steps⟩
    use m + 1
    use a ::ᵥ zs
    simp
    constructor
    · aesop
    · intro i
      induction i using Fin.induction
      all_goals aesop

-- related via a finite chain ==> related via star
theorem finitelyManyStepsIsStar (r : α → α → Prop) {n : ℕ}  :
    ∀ (x z : α) (ys : Vector α (Nat.succ n)),
      (x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)))
      → Relation.ReflTransGen r x z :=
  by
  induction n
  case zero =>
    rintro x z ys ⟨x_is_head, z_is_last, steprel⟩
    have : x = z := by
      simp [x_is_head, z_is_last, Vector.last_def, ← Fin.cast_nat_eq_last]
    rw [this]
  case succ n IH =>
    rintro x z ys ⟨x_is_head, z_is_last, steprel⟩
    let y := ys.tail.head -- WAIT bad, tail may be empty?
    rw [Relation.ReflTransGen.cases_head_iff]
    right
    use y
    constructor
    · specialize steprel 0
      simp at steprel
      rw [← x_is_head] at steprel
      convert steprel
      cases ys using Vector.inductionOn
      case h_cons y ys hyp =>
        cases ys using Vector.inductionOn
        rfl
    · apply IH y z ys.tail
      simp
      constructor
      · have sameLast : ys.tail.last = ys.last := by
          cases ys using Vector.inductionOn
          case h_cons y ys hyp =>
            cases ys using Vector.inductionOn
            rfl
        rw [sameLast]
        exact z_is_last
      · intro i
        specialize steprel i.succ
        induction i
        all_goals aesop

-- related via star <==> related via a finite chain
theorem starIffFinitelyManySteps (r : α → α → Prop) (x z : α) :
    Relation.ReflTransGen r x z ↔
      ∃ (n : ℕ) (ys : Vector α n.succ),
        x = ys.head ∧ z = ys.last ∧ ∀ i : Fin n, r (ys.get i.castSucc) (ys.get (i.succ)) :=
  by
  constructor
  apply starIsFinitelyManySteps r x z
  intro rhs
  rcases rhs with ⟨n, ys, x_is_head, z_is_last, rhs⟩
  exact finitelyManyStepsIsStar r x z ys ⟨x_is_head, z_is_last, rhs⟩
