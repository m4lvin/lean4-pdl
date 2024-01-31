import Mathlib.Order.BoundedOrder

mutual
  inductive Formula : Type
    | bottom : Formula
    | atom_prop : Char → Formula
    | neg : Formula → Formula
    | and : Formula → Formula → Formula
    | box : Program → Formula → Formula
  inductive Program : Type
    | atom_prog : Char → Program
    | sequence : Program → Program → Program
    | union : Program → Program → Program
    | star : Program → Program
    | test : Formula → Program
end
-- workaround, see https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/order.20of.20inductives.20affects.20deriving.20DecidableEq/near/407684123
deriving instance Repr,DecidableEq for Formula
deriving instance Repr,DecidableEq for Program

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
notation "⌈⌈" as "⌉⌉" P => Formula.boxes as P

infixl:33 ";'" => Program.sequence -- avoiding plain ";" which has a meaning in Lean 4
infixl:33 "⋓" => Program.union
prefix:33 "∗" => Program.star
prefix:33 "?'" => Program.test -- avoiding plain "?" which has a meaning in Lean 4

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
def LoadFormula.boxes : List Program → LoadFormula → LoadFormula
  | [], f => f
  | (p :: ps), f => LoadFormula.box p (LoadFormula.boxes ps f)

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

example : NegLoadFormula := ~'(⌊((·'a') ;' (·'b'))⌋⊤)
example : NegLoadFormula := ~'(⌊⌊[·'a', ·'b']⌋⌋⌊·'a'⌋ ⊤)
