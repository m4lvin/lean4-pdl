import Pdl.Semantics
import Pdl.Star

/-! # Semantic Quotients -/

/-! ## Defining the Quotient of Formulas -/

def semEquiv.Equivalence : Equivalence semEquiv :=
  ⟨ semEquiv.refl
  , fun xy => semEquiv.symm xy
  , fun xy yz => semEquiv.trans xy yz ⟩

instance Formula.instSetoid : Setoid Formula := ⟨semEquiv, semEquiv.Equivalence⟩

/-- A semantic property is an element of the quotient given by `semEquiv`. -/
abbrev SemProp := Quotient Formula.instSetoid

/-! ## Defining the Quotient of Programs -/

def relEquiv.Equivalence : Equivalence relEquiv :=
  ⟨ relEquiv.refl
  , fun xy => relEquiv.symm xy
  , fun xy yz => relEquiv.trans xy yz ⟩

instance Program.instSetoid : Setoid Program := ⟨relEquiv, relEquiv.Equivalence⟩

/-- A relational property is an element of the quotient given by `relEquiv`. -/
abbrev RelProp := Quotient Program.instSetoid

/-! ## Lifting congruent functions (in general)

These two should maybe go in mathlib? Or they already exist somewhere?
-/

lemma congr_liftFun {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {f : α → β}
    (h : ∀ x y, R x y → S (f x) (f y)) : ((R · ·) ⇒ (S · ·)) f f := h

lemma congr_liftFun₂ {α β : Type} [HasEquiv α] [HasEquiv β] [HasEquiv γ] {f : α → β → γ}
 (h : ∀ (x₁ x₂ : α) (y₁ y₂ : β), x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ ≈ f x₂ y₂) :
 ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f :=
  by intro x₁ x₂ hx y₁ y₂ hy; exact h x₁ x₂ y₁ y₂ hx hy

/-! ## Lifting formula connectives to the quotient -/

lemma Formula.neg_congr {φ ψ : Formula} (h : φ ≈ ψ) : Formula.neg φ ≈ Formula.neg ψ :=
  by simp [HasEquiv.Equiv, Setoid.r, semEquiv] at *
     intros W M w
     simp_all only

def SemProp.neg : SemProp → SemProp :=
  Quotient.map Formula.neg (congr_liftFun $ fun _ _ => Formula.neg_congr)

lemma Formula.and_congr {φ₁ ψ₁ φ₂ ψ₂ : Formula} (h₁ : φ₁ ≈ φ₂) (h₂ : ψ₁ ≈ ψ₂) :
  φ₁.and ψ₁ ≈ φ₂.and ψ₂ :=
  by simp [HasEquiv.Equiv, Setoid.r, semEquiv] at *
     intros W M w
     simp_all only

def SemProp.and : SemProp → SemProp → SemProp :=
  Quotient.map₂ Formula.and (congr_liftFun₂ $ fun _ _ _ _ hx hy => Formula.and_congr hx hy)

lemma Formula.box_congr {α β : Program} {φ ψ : Formula} (h₁ : α ≈ β) (h₂ : φ ≈ ψ) :
  φ.box α ≈ ψ.box β :=
  by simp [HasEquiv.Equiv, Setoid.r, semEquiv, relEquiv] at *
     intros W M w
     simp_all only

def SemProp.box : RelProp → SemProp → SemProp :=
  Quotient.map₂ Formula.box (fun _ _ hx _ _ hy => Formula.box_congr hx hy)

/-! ## Lifting program operators to the quotient -/

def RelProp.sequence : RelProp → RelProp → RelProp :=
  Quotient.map₂ Program.sequence (congr_liftFun₂ $
    fun _ _ _ _ hx hy W M v w => by specialize hx W M; specialize hy W M; simp_all)

def RelProp.union : RelProp → RelProp → RelProp :=
  Quotient.map₂ Program.union (congr_liftFun₂ $
    fun _ _ _ _ hx hy W M v w => by specialize hx W M; specialize hy W M; simp_all)

def RelProp.star : RelProp → RelProp :=
  Quotient.map Program.star (congr_liftFun $
    fun α β h W M v w => by
      specialize h W M;
      simp_all only [relate, @ReflTransGen.iff_finitelyManySteps, h])

def RelProp.test : SemProp → RelProp :=
  Quotient.map Program.test (congr_liftFun $
    fun τ₁ τ₂ h W M v w => by specialize h W M; simp_all)

/-! ## Examples -/

example {φ ψ : Formula} (h : φ ≈ ψ) : Quotient.mk' φ = Quotient.mk' ψ := Quotient.sound h

example {φ ψ : Formula} (h : φ ≈ ψ) : Quotient.mk' (Formula.neg φ) = Quotient.mk' (Formula.neg ψ) :=
  Quotient.sound (Formula.neg_congr h)

theorem neg_eq {φ ψ : Formula} (h : φ ≈ ψ) :
    SemProp.neg (Quotient.mk Formula.instSetoid φ) = SemProp.neg (Quotient.mk _ ψ) :=
  Quotient.sound (Formula.neg_congr h)

theorem neg_neg_eq' (φ : Formula) :
    SemProp.neg (SemProp.neg <| Quotient.mk' φ) = Quotient.mk' φ :=
  by apply Quotient.sound
     intro W M w
     simp [evaluate]

theorem trans_calc {P Q R : Prop} (hpq : P ↔ Q) (hqr : Q ↔ R) : P ↔ R :=
  by calc
    P ↔ Q := hpq
    _ ↔ R := hqr

example {φ ψ τ : Formula} (h1 : φ ≈ ψ) (h2 : ψ ≈ τ) : φ ≈ τ :=
  calc
    φ ≈ ψ := h1
    _ ≈ τ := h2

theorem neg_neg_eq {φ : Formula} : Formula.neg (Formula.neg φ) ≈ φ := by
  apply Quotient.exact
  apply neg_neg_eq'
