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

/-! ## Loaded Formulas -/

-- Loaded formulas consist of a negation, a sequence of loading boxes and then a normal formula.
-- For loading boxes we write ⌊α⌋ instead of ⌈α⌉.

mutual
inductive AnyFormula : Type
  | normal : Formula → AnyFormula -- φ
  | loaded : LoadFormula → AnyFormula -- χ
  deriving Repr, DecidableEq

inductive LoadFormula : Type
  | box : Program → AnyFormula → LoadFormula -- ⌊α⌋χ
  deriving Repr, DecidableEq
end

instance : Coe Formula AnyFormula := ⟨AnyFormula.normal⟩
instance : Coe LoadFormula AnyFormula := ⟨AnyFormula.loaded⟩

inductive AnyNegFormula
| neg : AnyFormula → AnyNegFormula

@[simp]
def loadMulti : List Program → Program → Formula → LoadFormula
| bs, α, φ => List.foldl (fun f β => LoadFormula.box β f) (LoadFormula.box α φ) bs

@[simp]
def LoadFormula.boxes : List Program → LoadFormula → LoadFormula
| [], χ => χ
| (b::bs), χ => LoadFormula.box b (LoadFormula.boxes bs χ)

@[simp]
def unload : LoadFormula → Formula
| LoadFormula.box α (.normal φ) => ⌈α⌉φ
| LoadFormula.box α (.loaded χ) => ⌈α⌉(unload χ)

inductive NegLoadFormula : Type -- ¬χ
  | neg : LoadFormula → NegLoadFormula
  deriving Repr, DecidableEq

-- FIXME: find some nice short notation for this and get Lean to use it?
-- notation "n:" φ:arg => AnyFormula.normal φ
-- notation "l:" χ:arg => AnyFormula.normal χ

notation "⌊" α "⌋" χ => LoadFormula.box α χ
notation "⌊⌊" αs "⌋⌋" χ => LoadFormula.boxes αs χ
notation "~'" χ => NegLoadFormula.neg χ
notation "~''" φ:arg => AnyNegFormula.neg φ

@[simp]
def negUnload : NegLoadFormula → Formula
| NegLoadFormula.neg χ => ~(unload χ)

example : NegLoadFormula := ~'(⌊((·1) ;' (·2))⌋(⊤ : Formula))
example : NegLoadFormula := ~'(⌊⌊[·1, ·2]⌋⌋⌊·1⌋(⊤ : Formula))

theorem loadBoxes_append : LoadFormula.boxes (as ++ bs) P = LoadFormula.boxes as (LoadFormula.boxes bs P) :=
  by
  induction as
  · simp
  · simp at *
    assumption

theorem loadBoxes_last : (~'⌊a⌋LoadFormula.boxes (as ++ [c]) P) = (~'⌊a⌋LoadFormula.boxes as (⌊c⌋P)) :=
  by
  induction as
  · simp
  case cons IH =>
    simp [loadBoxes_append] at *

@[simp]
theorem unload_boxes : unload (⌊⌊δ⌋⌋φ) = ⌈⌈δ⌉⌉(unload φ) := by
  induction δ
  · simp
  · simp_all only [LoadFormula.boxes, unload, Formula.boxes]

@[simp]
theorem unload_neg_loaded : unload (~'⌊α⌋(.loaded χ)).1 = ⌈α⌉(unload χ) := by
  simp [unload]

@[simp]
theorem unload_neg_normal : unload (~'⌊α⌋(.normal φ)).1 = ⌈α⌉φ := by
  simp [unload]

/-! ## Fischer-Ladner Closure -/

def fischerLadnerStep : Formula → List Formula
| ⊥ => []
| ·_ => []
| φ⋀ψ => [~(φ⋀ψ), φ, ψ]
| ⌈·_⌉φ => [φ]
| ⌈α;'β⌉φ => [ ⌈α⌉⌈β⌉φ ]
| ⌈α⋓β⌉φ => [ ⌈α⌉φ, ⌈β⌉φ ]
| ⌈∗α⌉φ => [ φ, ⌈α⌉⌈∗α⌉φ ]
| ⌈?'τ⌉φ => [ τ, φ ]
| ~~φ => [~φ]
| ~⊥ => []
| ~(·_) => []
| ~(φ⋀ψ) => [φ⋀ψ]
| ~⌈·_⌉φ => [~φ]
| ~⌈α;'β⌉φ => [ ~⌈α⌉⌈β⌉φ ]
| ~⌈α⋓β⌉φ => [ ~⌈α⌉φ, ~⌈β⌉φ ]
| ~⌈∗α⌉φ => [ ~φ, ~⌈α⌉⌈∗α⌉φ ]
| ~⌈?'τ⌉φ => [ ~τ, ~φ ]

def fischerLadner : List Formula → List Formula
| X => let Y := X ∪ (X.map fischerLadnerStep).join
       if Y ⊆ X then Y else fischerLadner Y
decreasing_by sorry -- hmm??

-- Examples:
-- #eval fischerLadner [~~((·1) : Formula)]
-- #eval fischerLadner [ ((⌈(·1) ⋓ (·2)⌉(·3)) ⟷ ((⌈(·1)⌉(·3)) ⋀ (⌈(·2)⌉(·3)))) ]
