
import Pdl.Semantics

/-! ## Semantic Quotients -/

#print semEquiv

def semEquiv.Equivalence : Equivalence semEquiv :=
  ⟨ by convert semEquiv.refl
  , by convert semEquiv.symm
  , by convert semEquiv.trans ⟩
  -- (why) are the "by convert" needed here?

instance Formula.instSetoid : Setoid Formula := ⟨semEquiv, semEquiv.Equivalence⟩

-- How should I name this?
abbrev SemProp := Quotient Formula.instSetoid

-- Now, can we lift connectives such as ~ and ⋀ to the quotient?

def SemProp.neg : SemProp → SemProp :=
  Quotient.map Formula.neg (by sorry)

def SemProp.and : SemProp → SemProp → SemProp :=
  Quotient.map₂ Formula.and (by sorry)
