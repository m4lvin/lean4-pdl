import Mathlib.Order.BoundedOrder

mutual
  inductive Formula : Type
    | bottom : Formula
    | atom_prop : Nat → Formula
    | neg : Formula → Formula
    | and : Formula → Formula → Formula
    | box : Program → Formula → Formula
  deriving Repr,DecidableEq
  inductive Program : Type
    | atom_prog : Nat → Program
    | sequence : Program → Program → Program
    | union : Program → Program → Program
    | star : Program → Program
    | test : Formula → Program
  deriving Repr,DecidableEq
end

-- Notation and abbreviations

@[simp]
def Formula.or : Formula → Formula → Formula
  | f, g => Formula.neg (Formula.and (Formula.neg f) (Formula.neg g))

/-- □(αs,φ) -/
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
notation "⌈⌈" as "⌉⌉" P => Formula.boxes as P

infixl:33 ";'" => Program.sequence -- avoiding plain ";" which has a meaning in Lean 4
infixl:33 "⋓" => Program.union
prefix:33 "∗" => Program.star
prefix:33 "?'" => Program.test -- avoiding plain "?" which has a meaning in Lean 4

def isAtomic : Program → Bool
| ·_ => true
| _ => false

def isStar : Program → Bool
| ∗_ => true
| _ => false

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

-- LOADED FORMULAS

-- Loaded formulas consist of a negation, a sequence of loading boxes and then a normal formula.
-- For loading boxes we write ⌊α⌋ instead of ⌈α⌉.

inductive LoadFormula : Type -- χ
  | load : Program → Formula → LoadFormula -- ⌊α⌋φ
  | box : Program → LoadFormula → LoadFormula -- ⌊α⌋χ
  deriving Repr, DecidableEq

@[simp]
def loadMulti : List Program → Program → Formula → LoadFormula
| bs, α, φ => List.foldl (flip LoadFormula.box) (LoadFormula.load α φ) bs

@[simp]
def LoadFormula.boxes : List Program → LoadFormula → LoadFormula
| [], χ => χ
| (b::bs), χ => (χ.boxes bs).box b

@[simp]
def unload : LoadFormula → Formula
| LoadFormula.load α φ => ⌈α⌉φ
| LoadFormula.box α χ => ⌈α⌉(unload χ)

inductive NegLoadFormula : Type -- ¬χ
  | neg : LoadFormula → NegLoadFormula
  deriving Repr, DecidableEq

@[simp]
def negUnload : NegLoadFormula → Formula
| NegLoadFormula.neg χ => ~(unload χ)

notation "⌊" α "⌋" φ => LoadFormula.load α φ
notation "⌊" α "⌋" χ => LoadFormula.box α χ
notation "⌊⌊" αs "⌋⌋" χ => LoadFormula.boxes αs χ
notation "~'" χ => NegLoadFormula.neg χ

example : NegLoadFormula := ~'(⌊((·1) ;' (·2))⌋⊤)
example : NegLoadFormula := ~'(⌊⌊[·1, ·2]⌋⌋⌊·1⌋ ⊤)

theorem loadBoxes_last : (~'⌊a⌋LoadFormula.boxes (as ++ [c]) P) = (~'⌊a⌋LoadFormula.boxes as (⌊c⌋P)) :=
  by
  induction as
  · simp
  · simp at *
    assumption

theorem loadBoxes_append : LoadFormula.boxes (as ++ bs) P = LoadFormula.boxes as (LoadFormula.boxes bs P) :=
  by
  induction as
  · simp
  · simp at *
    assumption
