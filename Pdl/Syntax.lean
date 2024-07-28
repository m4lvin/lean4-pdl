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
def Formula.boxes : List Program → Formula → Formula
| δ, χ => List.foldr (fun β φ => Formula.box β φ) χ δ

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

@[simp]
theorem Formula.boxes_nil : Formula.boxes [] φ = φ := by simp [Formula.boxes]

@[simp]
theorem Formula.boxes_cons : Formula.boxes (β :: δ) φ = Formula.box β (Formula.boxes δ φ) := by simp [Formula.boxes]

theorem boxes_last : Formula.boxes (δ ++ [α]) φ = Formula.boxes δ (⌈α⌉φ) :=
  by
  induction δ <;> simp [Formula.boxes]

theorem boxes_append : Formula.boxes (as ++ bs) P = Formula.boxes as (Formula.boxes bs P) :=
  by
  induction as <;> simp [Formula.boxes]

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

def loadMulti : List Program → Program → Formula → LoadFormula
| bs, α, φ => List.foldr (fun β lf => LoadFormula.box β lf) (LoadFormula.box α φ) bs

@[simp]
theorem loadMulti_nil : loadMulti [] α φ = LoadFormula.box α φ := by simp [loadMulti]

@[simp]
theorem loadMulti_cons : loadMulti (β :: δ) α φ = LoadFormula.box β (loadMulti δ α φ) := by simp [loadMulti]

def LoadFormula.boxes : List Program → LoadFormula → LoadFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ

@[simp]
theorem boxes_first : (Formula.boxes (α :: δ) φ) = ⌈α⌉(Formula.boxes δ φ) := by
  simp [Formula.boxes, LoadFormula.boxes]

@[simp]
def unload : LoadFormula → Formula
| LoadFormula.box α (.normal φ) => ⌈α⌉φ
| LoadFormula.box α (.loaded χ) => ⌈α⌉(unload χ)

@[simp]
theorem unload_loadMulti : unload (loadMulti δ α φ) = ⌈⌈δ⌉⌉⌈α⌉φ := by
  induction δ
  · simp [Formula.boxes, LoadFormula.boxes, loadMulti]
  · simpa [Formula.boxes, LoadFormula.boxes, loadMulti]

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
  induction as <;> simp [LoadFormula.boxes]

theorem loadBoxes_last : (~'⌊a⌋LoadFormula.boxes (as ++ [c]) P) = (~'⌊a⌋LoadFormula.boxes as (⌊c⌋P)) :=
  by
  induction as <;> simp [LoadFormula.boxes, loadBoxes_append]

@[simp]
theorem unload_boxes : unload (⌊⌊δ⌋⌋φ) = ⌈⌈δ⌉⌉(unload φ) := by
  induction δ
  · simp only [LoadFormula.boxes, List.foldr_nil, Formula.boxes]
  · simpa [Formula.boxes, LoadFormula.boxes]

@[simp]
theorem unload_neg_loaded : unload (~'⌊α⌋(.loaded χ)).1 = ⌈α⌉(unload χ) := by
  simp [unload]

@[simp]
theorem unload_neg_normal : unload (~'⌊α⌋(.normal φ)).1 = ⌈α⌉φ := by
  simp [unload]
