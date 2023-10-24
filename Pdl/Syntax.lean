import Mathlib.Order.BoundedOrder

mutual
  inductive Formula : Type
    | bottom : Formula
    | atom_prop : Char → Formula
    | neg : Formula → Formula
    | and : Formula → Formula → Formula
    | box : Program → Formula → Formula
    deriving Repr, DecidableEq
  inductive Program : Type
    | atom_prog : Char → Program
    | sequence : Program → Program → Program
    | union : Program → Program → Program
    | star : Program → Program
    | test : Formula → Program
    deriving Repr, DecidableEq -- is not derivable here?
end

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

@[simp]
instance Formula.instBot : Bot Formula := ⟨Formula.bottom⟩
@[simp]
instance Formula.insTop : Top Formula := ⟨Formula.neg Formula.bottom⟩

infixr:66 "⋀" => Formula.and
infixr:60 "⋁" => Formula.or
notation:55 φ:56 " ↣ " ψ:55 => ~φ ⋀ (~ψ)
notation:55 φ:56 " ⟷ " ψ:55 => (φ↣ψ) ⋀ (φ↣φ)
notation "⌈" α "⌉" P => Formula.box α P

infixl:33 ";" => Program.sequence -- TODO avoid ; which has a meaning in Lean 4
infixl:33 "⋓" => Program.union
prefix:33 "∗" => Program.star
prefix:33 "✓" => Program.test -- avoiding "?" which has a meaning in Lean 4


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
end
termination_by -- silly but needed?!
  mOfProgram p => sizeOf p
  mOfFormula f => sizeOf f

theorem boxes_last : (~⌈a⌉Formula.boxes (as ++ [c]) P) = (~⌈a⌉Formula.boxes as (⌈c⌉P)) :=
  by
  induction as
  · simp
  · simp at *
    assumption

theorem boxes_append : Formula.boxes (as ++ bs) P = Formula.boxes as (Formula.boxes bs P) :=
  by
  induction as
  · simp
  · simp at *
    assumption
