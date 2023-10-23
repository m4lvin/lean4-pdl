import Std.Classes.SetNotation -- provides Union

import Mathlib.Data.Finset.Basic -- this import affects unrelated stuff below O.o
-- see https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/induction.20for.20mutually.20inductive.20types/near/395082787

mutual
  inductive Formula : Type
    | bottom : Formula
    | atom_prop : Char → Formula
    | neg : Formula → Formula
    | and : Formula → Formula → Formula
    | box : Program → Formula → Formula
    | nstar : Formula → Formula
    deriving Repr -- DecidableEq is not derivable here?
  inductive Program : Type
    | atom_prog : Char → Program
    | sequence : Program → Program → Program
    | union : Program → Program → Program
    | star : Program → Program
    | test : Formula → Program
    deriving Repr -- DecidableEq is not derivable here?
end

-- TODO: update the above once we have a newer Lean version
-- including https://github.com/leanprover/lean4/pull/2591

-- needed for unions etc
instance decEqFormula : DecidableEq Formula := sorry
instance decEqProgram : DecidableEq Program := sorry

-- Notation and abbreviations

@[simp]
def Formula.or : Formula → Formula → Formula
  | f, g => Formula.neg (Formula.and (Formula.neg f) (Formula.neg g))

@[simp]
def Formula.boxes : List Program → Formula → Formula
  | [], f => f
  | (p :: ps), f => Formula.box p (Formula.boxes ps f)

@[simp]
def Program.steps : List Program → Program
  | [] => Program.test (Formula.neg Formula.bottom)
  | (p :: ps) => Program.sequence p (Program.steps ps)

notation "·" c => Formula.atom_prop c
notation "·" c => Program.atom_prog c
prefix:11 "~" => Formula.neg

-- TODO: use class instances to avoid overwriting ⊥ and ⊤
notation "⊥" => Formula.bottom
notation "⊤" => Formula.neg Formula.bottom
infixr:66 "⋀" => Formula.and
infixr:60 "⋁" => Formula.or
notation:55 φ:56 " ↣ " ψ:55 => ~φ ⋀ (~ψ)
notation:55 φ:56 " ⟷ " ψ:55 => (φ↣ψ) ⋀ (φ↣φ)
notation "⌈" α "⌉" P => Formula.box α P
prefix:33 "†" => Formula.nstar

infixl:33 ";" => Program.sequence -- TODO avoid ; which has a meaning in Lean 4
infixl:33 "⋓" => Program.union
prefix:33 "∗" => Program.star
prefix:33 "✓" => Program.test -- avoiding "?" which has a meaning in Lean 4

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
  def lengthOfProgram : Program → Nat
    | ·_ => 1
    | α;β => 1 + lengthOfProgram α + lengthOfProgram β
    | α⋓β => 1 + lengthOfProgram α + lengthOfProgram β
    | ∗α => 1 + lengthOfProgram α
    | ✓φ => 1 + lengthOfFormula φ
  def lengthOfFormula : Formula → Nat
    | Formula.bottom => 1
    | ·_ => 1
    | ~φ => 1 + lengthOfFormula φ
    | φ⋀ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
    | ⌈α⌉φ => 1 + lengthOfProgram α + lengthOfFormula φ
    | † f => 1 + lengthOfFormula f
end
termination_by -- silly but needed?!
  lengthOfProgram p => sizeOf p
  lengthOfFormula f => sizeOf f

-- mwah
@[simp]
def lengthOfEither : PSum Program Formula → Nat
  | PSum.inl p => lengthOfProgram p
  | PSum.inr f => lengthOfFormula f

-- MEASURE
mutual
  @[simp]
  def mOfProgram : Program → Nat
    | ·_ => 0
    | ✓ φ => 1 + mOfFormula φ
    | α;β => 1 + mOfProgram α + mOfProgram β + 1 -- TODO: max (mOfFormula φ) (mOfFormula (~φ))
    | α⋓β => 1 + mOfProgram α + mOfProgram β + 1
    | ∗α => 1 + mOfProgram α
  @[simp]
  def mOfFormula : Formula → Nat
    | ⊥ => 0
    | ~⊥ => 0
    |-- missing in borze?
      ·_ =>
      0
    | ~·_ => 0
    | ~~φ => 1 + mOfFormula φ
    | φ⋀ψ => 1 + mOfFormula φ + mOfFormula ψ
    | ~φ⋀ψ => 1 + mOfFormula (~φ) + mOfFormula (~ψ)
    | ⌈α⌉ φ => mOfProgram α + mOfFormula φ
    | ~⌈α⌉ φ => mOfProgram α + mOfFormula (~φ)
    | ~†_ => 0
    | †_ => 0
end
termination_by -- silly but needed?!
  mOfProgram p => sizeOf p
  mOfFormula f => sizeOf f


-- VOCAB

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
termination_by -- silly but needed?!
  vocabOfProgram p => sizeOf p
  vocabOfFormula f => sizeOf f

def vocabOfSetFormula : Finset Formula → Finset Char
  | X => X.biUnion vocabOfFormula

class HasVocabulary (α : Type) where
  voc : α → Finset Char

instance formulaHasVocabulary : HasVocabulary Formula := ⟨vocabOfFormula⟩
instance programHasVocabulary : HasVocabulary Program := ⟨vocabOfProgram⟩
instance finsetFormulaHasVocabulary : HasVocabulary (Finset Formula) := ⟨vocabOfSetFormula⟩

lemma boxes_last : (~⌈a⌉Formula.boxes (as ++ [c]) P) = (~⌈a⌉Formula.boxes as (⌈c⌉P)) :=
  by
  induction as
  · simp
  · simp at *
    assumption

lemma boxes_append : Formula.boxes (as ++ bs) P = Formula.boxes as (Formula.boxes bs P) :=
  by
  induction as
  · simp
  · simp at *
    assumption
