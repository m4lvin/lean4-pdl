
import Pdl.Semantics

/-! ## Semantic Quotients -/

#print semEquiv

def semEquiv.Equivalence : Equivalence semEquiv :=
  ⟨semEquiv.refl
  , by convert semEquiv.symm
  , by convert semEquiv.trans ⟩
  -- (why) are the "by convert" needed here?
  -- not for refl, seems it's an autoimplicit issue
  -- probably because `Equivalence` is in core, whereas `Symmetric`, and `Transitive` are in Mathlib.

instance Formula.instSetoid : Setoid Formula := ⟨semEquiv, semEquiv.Equivalence⟩

-- How should I name this?
abbrev SemProp := Quotient Formula.instSetoid

-- Now, can we lift connectives such as ~ and ⋀ to the quotient?

lemma Formula.neg_congr {φ ψ : Formula} (h : φ ≈ ψ) : Formula.neg φ ≈ Formula.neg ψ :=
  by simp [HasEquiv.Equiv, Setoid.r, semEquiv] at *
     intros W M w
     simp_all only

lemma Formula.and_congr {φ₁ ψ₁ φ₂ ψ₂ : Formula} (h₁ : φ₁ ≈ φ₂) (h₂ : ψ₁ ≈ ψ₂) :
  Formula.and φ₁ ψ₁ ≈ Formula.and φ₂ ψ₂ :=
  by simp [HasEquiv.Equiv, Setoid.r, semEquiv] at *
     intros W M w
     simp_all only
lemma congr_liftFun {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {f : α → β}
    (h : ∀ x y, R x y → S (f x) (f y)) : ((R · ·) ⇒ (S · ·)) f f := h
-- This should maybe go in mathlib? or it exists there somewhere?

lemma congr_liftFun₂ {α β : Type} [HasEquiv α] [HasEquiv β] [HasEquiv γ] {f : α → β → γ}
 (h : ∀ (x₁ x₂ : α) (y₁ y₂ : β), x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ ≈ f x₂ y₂) :
 ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f :=
  by intro x₁ x₂ hx y₁ y₂ hy; exact h x₁ x₂ y₁ y₂ hx hy


def SemProp.neg : SemProp → SemProp :=
  Quotient.map Formula.neg (by apply congr_liftFun; apply Formula.neg_congr)

def SemProp.and : SemProp → SemProp → SemProp :=
  Quotient.map₂ Formula.and (by apply congr_liftFun₂; intros x₁ x₂ y₁ y₂ hx hy; exact Formula.and_congr hx hy)

example {φ ψ : Formula} (h : φ ≈ ψ) : Quotient.mk' φ = Quotient.mk' ψ :=
  by apply Quotient.sound; exact h

example {φ ψ : Formula} (h : φ ≈ ψ) : Quotient.mk' (Formula.neg φ) = Quotient.mk' (Formula.neg ψ) :=
  by apply Quotient.sound; apply Formula.neg_congr; exact h

theorem neg_eq {φ ψ : Formula} (h : φ ≈ ψ) : SemProp.neg (Quotient.mk Formula.instSetoid φ) = SemProp.neg (Quotient.mk _ ψ) :=
  by apply Quotient.sound; apply Formula.neg_congr; exact h -- why does this work without using neg?

theorem neg_neg_eq' (φ : Formula) : SemProp.neg (SemProp.neg <| Quotient.mk' φ) = Quotient.mk' φ :=
  by sorry


#check HEq

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
