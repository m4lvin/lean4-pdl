module

public import Mathlib.Algebra.Order.Kleene

public import Pdl.SemQuot

/-! # PDL programs form a Kleene Algebra

This file provides `RelProp.kleeneAlgebra`.
It shows that the semantic quotient of PDL `Program`s as `RelProp`s forms a `KleeneAlgebra`.
-/

@[expose] public section

instance : KStar Program :=
  { kstar := fun α ↦ ∗α }

instance : KStar RelProp :=
  { kstar := RelProp.star }

instance : Add RelProp :=
  { add := RelProp.union }

instance : AddSemigroup RelProp where
  add_assoc := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => Quotient.ind (fun γ => ?_))))
    simp only [HAdd.hAdd, Add.add, RelProp.union, Quotient.map₂, Program.instSetoid,
      Quotient.lift_mk, Quotient.eq, relEquiv, relate]
    aesop

instance : Zero RelProp :=
  { zero := ⟦?'⊥⟧ }

instance : AddZeroClass RelProp where
  add_zero := by
    apply Quotient.ind
    intro α
    simp [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero, RelProp.union, Program.instSetoid, relEquiv,
      Quotient.eq, Quotient.map₂]
  zero_add := by
    apply Quotient.ind
    intro α
    simp [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero, RelProp.union, Program.instSetoid, relEquiv,
      Quotient.eq, Quotient.map₂]

def Program.Repeat : ℕ → Program → Program
  | 0     , _ => ?'⊥
  | n + 1 , α => α ;' (Program.Repeat n α)

def RelProp.Repeat : ℕ → RelProp → RelProp
  | 0     , _ => 0
  | n + 1 , a => RelProp.Repeat n a + a

instance RelProp.addMonoid : AddMonoid RelProp where
  nsmul := RelProp.Repeat
  nsmul_zero := by simp [HSMul.hSMul, SMul.smul, RelProp.Repeat]
  nsmul_succ := by simp [HSMul.hSMul, SMul.smul, RelProp.Repeat]
  zero_add := instAddZeroClassRelProp.zero_add -- why needed, since AddMonoid extends AddZeroClass?
  add_zero := instAddZeroClassRelProp.add_zero

instance RelProp.mul : Mul RelProp where
  mul := RelProp.sequence

instance : MulZeroClass RelProp where
  zero_mul := by
    apply Quotient.ind
    intro α
    simp [OfNat.ofNat, Zero.zero, HMul.hMul, Mul.mul, RelProp.sequence, Program.instSetoid,
      relEquiv, Quotient.eq, Quotient.map₂]
  mul_zero := by
    apply Quotient.ind
    intro α
    simp [OfNat.ofNat, Zero.zero, HMul.hMul, Mul.mul, RelProp.sequence, Program.instSetoid,
      relEquiv, Quotient.eq, Quotient.map₂]

instance : Distrib RelProp where
  left_distrib := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => Quotient.ind (fun γ => ?_))))
    simp only [HMul.hMul, Mul.mul, RelProp.sequence, Quotient.map₂, Program.instSetoid, HAdd.hAdd,
      Add.add, RelProp.union, Quotient.lift_mk, Quotient.eq, relEquiv, relate]
    aesop
  right_distrib := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => Quotient.ind (fun γ => ?_))))
    simp only [HMul.hMul, Mul.mul, RelProp.sequence, Quotient.map₂, Program.instSetoid, HAdd.hAdd,
      Add.add, RelProp.union, Quotient.lift_mk, Quotient.eq, relEquiv, relate]
    aesop

instance : AddCommMonoid RelProp where
  add_comm := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => ?_)))
    simp only [HAdd.hAdd, Add.add, RelProp.union, Quotient.map₂, Program.instSetoid,
      Quotient.lift_mk, Quotient.eq, relEquiv, relate]
    aesop

instance : NonUnitalNonAssocSemiring RelProp where
  left_distrib := instDistribRelProp.left_distrib
  right_distrib := instDistribRelProp.right_distrib
  zero_mul := instMulZeroClassRelProp.zero_mul
  mul_zero := instMulZeroClassRelProp.mul_zero

instance : NonUnitalSemiring RelProp where
  mul_assoc := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => Quotient.ind (fun γ => ?_))))
    simp only [HMul.hMul, Mul.mul, RelProp.sequence, Quotient.map₂, Program.instSetoid,
      Quotient.lift_mk, Quotient.eq, relEquiv, relate]
    aesop

instance RelProp.instOne : One RelProp :=
  { one := ⟦?'⊤⟧ }

instance RelProp.semiring : Semiring RelProp where
  one_mul := by
    apply Quotient.ind
    intro α
    simp [HMul.hMul, Mul.mul, RelProp.sequence, Program.instSetoid, OfNat.ofNat, One.one,
      Quotient.map₂, Quotient.eq, relEquiv, relate, evaluate, not_false_eq_true,
      and_true, exists_eq_left', implies_true]
  mul_one := by
    apply Quotient.ind
    intro α
    simp [HMul.hMul, Mul.mul, RelProp.sequence, Program.instSetoid, OfNat.ofNat, One.one,
      Quotient.map₂, Quotient.eq, relEquiv, relate, evaluate, not_false_eq_true,
      and_true, exists_eq_right, implies_true]

def relImp (α β : Program) := ∀ (W : Type) (M : KripkeModel W) v w, relate M α v w → relate M β v w

def relImp_strict (α β : Program) :=
     (∀ (W : Type) (M : KripkeModel W) v w, relate M α v w → relate M β v w)
  ∧ ¬(∀ (W : Type) (M : KripkeModel W) v w, relate M β v w → relate M α v w)

def RelProp.le : RelProp → RelProp → Prop := Quotient.lift₂ relImp <| by
  intro α₁ β₁ α₂ β₂ hα hβ
  simp_all only [relImp, eq_iff_iff]
  refine ⟨fun hyp W M v w v_w => ?_, fun hyp W M v w v_w => ?_⟩
  all_goals
    specialize hα W M v w
    specialize hβ W M v w
    specialize hyp W M v w
    grind

/-- `relImp` only depends on the equivalence classes of its arguments. -/
theorem relImp_congr {α₁ β₁ α₂ β₂ : Program} (hα : α₁ ≈ α₂) (hβ : β₁ ≈ β₂) :
    relImp α₁ β₁ ↔ relImp α₂ β₂ := by
  simp_all only [relImp]
  refine ⟨fun hyp W M v w v_w => ?_, fun hyp W M v w v_w => ?_⟩
  all_goals
    specialize hα W M v w
    specialize hβ W M v w
    specialize hyp W M v w
    grind

def RelProp.lt : RelProp → RelProp → Prop := Quotient.lift₂ relImp_strict <| by
  intro α₁ β₁ α₂ β₂ hα hβ
  -- `relImp_strict α β` is `relImp α β ∧ ¬ relImp β α`, so both parts are congruences.
  exact propext (and_congr (relImp_congr hα hβ) (not_congr (relImp_congr hβ hα)))

instance RelProp.instLE : LE RelProp where
  le := RelProp.le

instance RelProp.instPreorder : Preorder RelProp where
  le_refl := by
    apply Quotient.ind
    intro α
    simp [LE.le, RelProp.le, relImp]
  le_trans := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => Quotient.ind (fun γ => ?_))))
    simp_all [LE.le, RelProp.le, relImp]

instance RelProp.partialOrder : PartialOrder RelProp where
  le_antisymm := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => ?_)))
    simp [LE.le, RelProp.le, relImp, Program.instSetoid, relEquiv, Quotient.eq]
    aesop

instance RelProp.semilatticeSup : SemilatticeSup RelProp where
  sup := RelProp.union
  le_sup_left := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => ?_)))
    simp [LE.le, RelProp.le, RelProp.union, Quotient.lift, Quotient.map₂, relImp]
    aesop
  le_sup_right := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => ?_)))
    simp [LE.le, RelProp.le, RelProp.union,  Quotient.lift, Quotient.map₂, relImp]
    aesop
  sup_le := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => Quotient.ind (fun γ => ?_))))
    simp [LE.le, RelProp.le, relImp, Quotient.lift, Quotient.map₂, RelProp.union]
    aesop

instance RelProp.idemSemiring : IdemSemiring RelProp where
  bot := ⟦?'⊥⟧
  bot_le := by
    apply Quotient.ind
    intro α
    simp [LE.le, RelProp.le, Quotient.lift₂, relImp]

instance RelProp.kleeneAlgebra : KleeneAlgebra RelProp where
  one_le_kstar := by
    apply Quotient.ind
    intro α W M w
    simp only [relate, evaluate, not_false_eq_true, and_true, forall_eq']
    exact Relation.ReflTransGen.refl
  mul_kstar_le_kstar := by
    apply Quotient.ind
    intro α W M v w
    simp only [relate, forall_exists_index, and_imp]
    intro x v_α_x x_αs_w
    exact Relation.ReflTransGen.head v_α_x x_αs_w
  kstar_mul_le_kstar := by
    apply Quotient.ind
    intro α W M v w
    simp only [relate, forall_exists_index, and_imp]
    intro x v_αs_x x_α_w
    exact Relation.ReflTransGen.tail v_αs_x x_α_w
  mul_kstar_le_self := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => ?_)))
    intro h W M v w
    simp only [relate, forall_exists_index, and_imp]
    intro x v_β_x x_αs_w
    induction x_αs_w
    case refl => exact v_β_x
    case tail y z x_αs_y y_α_z ih =>
      specialize h W M v z
      simp only [relate, forall_exists_index, and_imp] at h
      exact h y ih y_α_z
  kstar_mul_le_self := by
    refine (Quotient.ind (fun α => Quotient.ind (fun β => ?_)))
    intro h W M v w
    simp only [relate, forall_exists_index, and_imp]
    intro x v_αs_x x_β_w
    induction v_αs_x
    case refl => exact x_β_w
    case tail y z x_αs_y y_α_z ih =>
      apply ih
      specialize h W M y  w
      simp at h
      tauto
