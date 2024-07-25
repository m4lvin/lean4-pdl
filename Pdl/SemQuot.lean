
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

-- This should maybe go in mathlib? or it exists there somewhere?
lemma congr_liftFun {α β : Type} [Setoid α] [Setoid β] {f : α → β}
 (h : ∀ x y, x ≈ y → f x ≈ f y) : ((· ≈ ·) ⇒ (· ≈ ·)) f f :=
 -- by exact? -- does not work (it's not there at least so obviously)
  by intro x y hxy; exact h x y hxy

lemma congr_liftFun₂ {α β : Type} [Setoid α] [Setoid β] [Setoid γ] {f : α → β → γ}
 (h : ∀ (x₁ x₂ : α) (y₁ y₂ : β), x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ ≈ f x₂ y₂) :
 ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f :=
  by intro x₁ x₂ hx y₁ y₂ hy; exact h x₁ x₂ y₁ y₂ hx hy


def SemProp.neg : SemProp → SemProp :=
  Quotient.map Formula.neg (by apply congr_liftFun; apply Formula.neg_congr)

def SemProp.and : SemProp → SemProp → SemProp :=
  Quotient.map₂ Formula.and (by apply congr_liftFun₂; intros x₁ x₂ y₁ y₂ hx hy; exact Formula.and_congr hx hy)

example {φ ψ : Formula} (h : φ ≈ ψ) : Quotient.mk Formula.instSetoid φ = Quotient.mk _ ψ :=
  by apply Quotient.sound; exact h

example {φ ψ : Formula} (h : φ ≈ ψ) : Quotient.mk Formula.instSetoid (Formula.neg φ) = Quotient.mk _ (Formula.neg ψ) :=
  by apply Quotient.sound; apply Formula.neg_congr; exact h

example {φ ψ : Formula} (h : φ ≈ ψ) : SemProp.neg (Quotient.mk Formula.instSetoid φ) = SemProp.neg (Quotient.mk _ ψ) :=
  by apply Quotient.sound; apply Formula.neg_congr; exact h -- why does this work without using neg?
