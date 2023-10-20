import Mathlib.Logic.Relation

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
