import Mathlib.Data.Finset.Basic

mutual
  inductive Formula : Type
    | bottom : Formula
    | atom_prop : Char → Formula
    | neg : Formula → Formula
    | and : Formula → Formula → Formula
    | box : Program → Formula → Formula
    | nstar : Formula → Formula
    deriving Repr -- TODO DecidableEq not posible yet?
  inductive Program : Type
    | atom_prog : Char → Program
    | sequence : Program → Program → Program
    | union : Program → Program → Program
    | star : Program → Program
    | test : Formula → Program
    deriving Repr -- TODO DecidableEq not posible yet?
end

-- needed for unions etc
instance decEqFormula : DecidableEq Formula :=
  sorry
instance decEqProgram : DecidableEq Program :=
  sorry

@[simp]
def Formula.or : Formula → Formula → Formula
  | f, g => Formula.neg (Formula.and (Formula.neg f) (Formula.neg g))

-- Notation and abbreviations

notation "·" c => Formula.atom_prop c

notation "·" c => Program.atom_prog c

prefix:11 "~" => Formula.neg

notation "⊥" => Formula.bottom

notation "⊤" => Formula.neg Formula.bottom

notation "⌈" α "⌉" P => Formula.box α P

infixr:66 "⋀" => Formula.and

infixr:60 "⋁" => Formula.or

infixr:55 "↣" => fun φ ψ => ~φ⋀(~ψ)

infixl:77 "⟷" => fun ϕ ψ => (ϕ↣ψ)⋀(ψ↣ϕ)

infixl:33 ";" => Program.sequence -- TODO avoid ; which has a meaning in Lean 4 ??

instance : Union Program :=
  ⟨Program.union⟩

prefix:33 "∗" => Program.star

prefix:33 "†" => Formula.nstar

prefix:33 "✓" => Program.test -- avoiding ? which has a meaning in Lean 4

-- THE f FUNCTION
-- | Borzechowski's f function, sort of.
def theF : Formula → Formula
  | ⊥ => ⊥
  | ~f => theF f
  | ·c => ·c
  | φ⋀ψ => theF φ⋀theF ψ
  | ⌈α⌉ φ => ⌈α⌉ (theF φ)
  | †f => theF f

-- COMPLEXITY
mutual
  @[simp]
  def lengthOfProgram : Program → ℕ
    | ·c => 1
    | α;β => 1 + lengthOfProgram α + lengthOfProgram β
    | Program.union α β => 1 + lengthOfProgram α + lengthOfProgram β
    | ∗α => 1 + lengthOfProgram α
    | (✓ φ) => 1 + lengthOfFormula φ
  @[simp]
  def lengthOfFormula : Formula → ℕ
    | ⊥ => 1
    | ·c => 1
    | ~φ => 1 + lengthOfFormula φ
    | φ⋀ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
    | ⌈α⌉ φ => 1 + lengthOfProgram α + lengthOfFormula φ
    | †f => 1 + lengthOfFormula f
end
decreasing_by sorry -- TODO!
-- see https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction

-- mwah
@[simp]
def lengthOfEither : PSum Program Formula → ℕ
  | PSum.inl p => lengthOfProgram p
  | PSum.inr f => lengthOfFormula f

-- MEASURE
mutual
  @[simp]
  def mOfProgram : Program → ℕ
    | ·c => 0
    | ✓ φ => 1 + mOfFormula φ
    | α;β => 1 + mOfProgram α + mOfProgram β + 1 -- TODO: max (mOfFormula φ) (mOfFormula (~φ))
    | Program.union α β => 1 + mOfProgram α + mOfProgram β + 1
    | ∗α => 1 + mOfProgram α
  @[simp]
  def mOfFormula : Formula → ℕ
    | ⊥ => 0
    | ~⊥ => 0
    |-- missing in borze?
      ·c =>
      0
    | ~·c => 0
    | ~~φ => 1 + mOfFormula φ
    | φ⋀ψ => 1 + mOfFormula φ + mOfFormula ψ
    | ~φ⋀ψ => 1 + mOfFormula (~φ) + mOfFormula (~ψ)
    | ⌈α⌉ φ => mOfProgram α + mOfFormula φ
    | ~⌈α⌉ φ => mOfProgram α + mOfFormula (~φ)
    | ~†ϕ => 0
    | †ϕ => 0
end
decreasing_by sorry -- TODO!

-- VOCABULARY
mutual
  def vocabOfProgram : Program → Finset Char
    | ·c => {c}
    | α;β => vocabOfProgram α ∪ vocabOfProgram β
    | Program.union α β => vocabOfProgram α ∪ vocabOfProgram β
    | ∗α => vocabOfProgram α
    | ✓ φ => vocabOfFormula φ
  def vocabOfFormula : Formula → Finset Char
    | ⊥ => ∅
    | ·c => {c}
    | ~φ => vocabOfFormula φ
    | φ⋀ψ => vocabOfFormula φ ∪ vocabOfFormula ψ
    | ⌈α⌉ φ => vocabOfProgram α ∪ vocabOfFormula φ
    | †ϕ => vocabOfFormula ϕ
end
decreasing_by sorry -- TODO!

def vocabOfSetFormula : Finset Formula → Finset Char
  | X => X.biUnion vocabOfFormula

class HasVocabulary (α : Type) where
  voc : α → Finset Char

open HasVocabulary

instance formulaHasVocabulary : HasVocabulary Formula := ⟨ vocabOfFormula⟩  

instance programHasVocabulary : HasVocabulary Program := ⟨ vocabOfProgram ⟩ 

instance finsetFormulaHasVocabulary : HasVocabulary (Finset Formula) := ⟨ vocabOfSetFormula ⟩ 
