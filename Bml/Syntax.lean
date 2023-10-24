-- SYNTAX
import Data.Set.Finite
import Algebra.BigOperators.Basic

#align_import syntax

-- Definition 1, page 4
-- Definition 1, page 4
inductive Formula : Type
  | bottom : Formula
  | atom_prop : Char → Formula
  | neg : Formula → Formula
  | And : Formula → Formula → Formula
  | box : Formula → Formula
  deriving DecidableEq
#align formula Formula

-- Predefined atomic propositions for convenience
def p :=
  Formula.atom_prop 'p'
#align p p

def q :=
  Formula.atom_prop 'q'
#align q q

def r :=
  Formula.atom_prop 'r'
#align r r

notation "·" -- Notation and abbreviations
c => Formula.atom_prop c

prefix:88 "~" => Formula.neg

prefix:77 "□" => Formula.box

infixr:66 "⋏" => Formula.and

@[simp]
def impl (φ ψ : Formula) :=
  ~(φ⋏~ψ)
#align impl impl

infixr:55 "↣" => impl

infixl:77 "⟷" => fun ϕ ψ => (ϕ↣ψ)⋏(ψ↣ϕ)

@[simp]
instance : Bot Formula :=
  ⟨Formula.bottom⟩

instance : Top Formula :=
  ⟨Formula.neg Formula.bottom⟩

-- showing formulas as strings that are valid Lean code
def formToString : Formula → String
  | ⊥ => "⊥"
  | ·c => repr c
  | ~ϕ => "~" ++ formToString ϕ
  | ϕ⋏ψ => "(" ++ formToString ϕ ++ " ⋏ " ++ formToString ψ ++ ")"
  | □ϕ => "(□ " ++ formToString ϕ ++ ")"
#align formToString formToString

instance : Repr Formula :=
  ⟨formToString⟩

-- COMPLEXITY
-- this should later be the measure from Lemma 2, page 20
@[simp]
def lengthOfFormula : Formula → ℕ
  | ⊥ => 1
  |-- FIXME: has bad width
    ·c =>
    1
  | ~φ => 1 + lengthOfFormula φ
  | φ⋏ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
  | □φ => 1 + lengthOfFormula φ
#align lengthOfFormula lengthOfFormula

@[simp]
def lengthOfSet : Finset Formula → ℕ
  | X => X.Sum lengthOfFormula
#align lengthOfSet lengthOfSet

class HasLength (α : Type) where
  lengthOf : α → ℕ
#align hasLength HasLength

open HasLength

instance formulaHasLength : HasLength Formula :=
  HasLength.mk lengthOfFormula
#align formula_hasLength formulaHasLength

instance setFormulaHasLength : HasLength (Finset Formula) :=
  HasLength.mk lengthOfSet
#align setFormula_hasLength setFormulaHasLength

@[simp]
def complexityOfFormula : Formula → ℕ
  | ⊥ => 1
  | ·c => 1
  | ~φ => 1 + complexityOfFormula φ
  | φ⋏ψ => 1 + max (complexityOfFormula φ) (complexityOfFormula ψ)
  | □φ => 1 + complexityOfFormula φ
#align complexityOfFormula complexityOfFormula

def complexityOfSet : Finset Formula → ℕ
  | X => X.Sum complexityOfFormula
#align complexityOfSet complexityOfSet

class HasComplexity (α : Type) where
  complexityOf : α → ℕ
#align hasComplexity HasComplexity

open HasComplexity

instance formulaHasComplexity : HasComplexity Formula :=
  HasComplexity.mk complexityOfFormula
#align formula_hasComplexity formulaHasComplexity

instance setFormulaHasComplexity : HasComplexity (Finset Formula) :=
  HasComplexity.mk complexityOfSet
#align setFormula_hasComplexity setFormulaHasComplexity

