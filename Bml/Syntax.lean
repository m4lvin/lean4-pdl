-- SYNTAX
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic

-- Definition 1, page 4
inductive Formula : Type
  | bottom : Formula
  | atom_prop : Char → Formula
  | neg : Formula → Formula
  | And : Formula → Formula → Formula
  | box : Formula → Formula
  deriving DecidableEq

-- Predefined atomic propositions for convenience
def p := Formula.atom_prop 'p'
def q := Formula.atom_prop 'q'
def r := Formula.atom_prop 'r'

notation "·" -- Notation and abbreviations
c => Formula.atom_prop c

prefix:88 "~" => Formula.neg

prefix:77 "□" => Formula.box

infixr:66 "⋀" => Formula.And

@[simp]
def impl (φ ψ : Formula) := ~(φ ⋀ ~ψ)

infixr:55 "↣" => impl

infixl:77 "⟷" => fun ϕ ψ => (ϕ↣ψ)⋀(ψ↣ϕ)

@[simp]
instance : Bot Formula :=
  ⟨Formula.bottom⟩

instance : Top Formula :=
  ⟨Formula.neg Formula.bottom⟩

-- showing formulas as strings that are valid Lean code
def formToString : Formula → ℕ → Lean.Format
  | ⊥, _ => "⊥"
  | ·c, _ => "·" ++ repr c
  | ~ϕ, n => "~" ++ formToString ϕ n
  | ϕ⋀ψ, n => "(" ++ formToString ϕ n ++ " ⋀ " ++ formToString ψ n ++ ")"
  | □ϕ, n => "(□ " ++ formToString ϕ n ++ ")"

instance : Repr Formula :=
   ⟨formToString⟩

-- COMPLEXITY
-- this should later be the measure from Lemma 2, page 20
@[simp]
def lengthOfFormula : Formula → ℕ
  | ⊥ => 1
  | ·_ => 1
  | ~φ => 1 + lengthOfFormula φ
  | φ⋀ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
  | □φ => 1 + lengthOfFormula φ

@[simp]
def lengthOfSet : Finset Formula → ℕ
  | X => X.sum lengthOfFormula

class HasLength (α : Type) where
  lengthOf : α → ℕ

open HasLength

instance formulaHasLength : HasLength Formula :=
  HasLength.mk lengthOfFormula

instance setFormulaHasLength : HasLength (Finset Formula) :=
  HasLength.mk lengthOfSet

@[simp]
def complexityOfFormula : Formula → ℕ
  | ⊥ => 1
  | ·_ => 1
  | ~φ => 1 + complexityOfFormula φ
  | φ⋀ψ => 1 + max (complexityOfFormula φ) (complexityOfFormula ψ)
  | □φ => 1 + complexityOfFormula φ

def complexityOfSet : Finset Formula → ℕ
  | X => X.sum complexityOfFormula

class HasComplexity (α : Type) where
  complexityOf : α → ℕ

open HasComplexity

instance formulaHasComplexity : HasComplexity Formula :=
  HasComplexity.mk complexityOfFormula

instance setFormulaHasComplexity : HasComplexity (Finset Formula) :=
  HasComplexity.mk complexityOfSet
