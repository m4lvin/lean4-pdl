import Mathlib.Order.BoundedOrder.Basic

/-! # Syntax (Section 2.1) -/

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

/-! ## Abbreviations and Notation  -/

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

def Program.isAtomic : Program → Prop
| ·_ => true
| _ => false

instance : DecidablePred Program.isAtomic := by
  intro α
  cases α <;> simp [Program.isAtomic] <;>
  all_goals
    try exact instDecidableTrue
    try exact instDecidableFalse

theorem Program.isAtomic_iff : α.isAtomic ↔ ∃ a, α = (·a : Program) := by
  cases α <;> simp_all [isAtomic]

def Program.isStar : Program → Prop
| ∗_ => true
| _ => false

instance : DecidablePred Program.isStar := by
  intro α
  cases α <;> simp [Program.isStar] <;>
  all_goals
    try exact instDecidableTrue
    try exact instDecidableFalse

theorem Program.isStar_iff : α.isStar ↔ ∃ β, α = (∗β) := by
  cases α <;> simp_all [isStar]

@[simp]
theorem Formula.boxes_nil : Formula.boxes [] φ = φ := by simp [Formula.boxes]

@[simp]
theorem Formula.boxes_cons : Formula.boxes (β :: δ) φ = ⌈β⌉(Formula.boxes δ φ) := by
  simp [Formula.boxes]

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
def LoadFormula.unload : LoadFormula → Formula
| LoadFormula.box α (.normal φ) => ⌈α⌉φ
| LoadFormula.box α (.loaded χ) => ⌈α⌉(unload χ)

@[simp]
theorem unload_loadMulti : (loadMulti δ α φ).unload  = ⌈⌈δ⌉⌉⌈α⌉φ := by
  induction δ
  · simp [Formula.boxes, LoadFormula.boxes, loadMulti]
  · simpa [Formula.boxes, LoadFormula.boxes, loadMulti]

inductive NegLoadFormula : Type -- ¬χ
  | neg : LoadFormula → NegLoadFormula
  deriving Repr, DecidableEq

-- FIXME: find some nice short notation for this and get Lean to use it?
-- notation "n:" φ:arg => AnyFormula.normal φ
-- notation "l:" χ:arg => AnyFormula.loaded χ

notation "⌊" α "⌋" χ => LoadFormula.box α χ
notation "⌊⌊" αs "⌋⌋" χ => LoadFormula.boxes αs χ
notation "~'" χ => NegLoadFormula.neg χ
notation "~''" φ:arg => AnyNegFormula.neg φ

@[simp]
def negUnload : NegLoadFormula → Formula
| NegLoadFormula.neg χ => ~(χ.unload)

example : NegLoadFormula := ~'(⌊((·1) ;' (·2))⌋(⊤ : Formula))
example : NegLoadFormula := ~'(⌊⌊[·1, ·2]⌋⌋⌊·1⌋(⊤ : Formula))

theorem loadBoxes_append : LoadFormula.boxes (as ++ bs) P = LoadFormula.boxes as (LoadFormula.boxes bs P) :=
  by
  induction as <;> simp [LoadFormula.boxes]

theorem loadBoxes_last : (~'⌊a⌋LoadFormula.boxes (as ++ [c]) P) = (~'⌊a⌋LoadFormula.boxes as (⌊c⌋P)) :=
  by
  induction as <;> simp [LoadFormula.boxes, loadBoxes_append]

@[simp]
theorem unload_boxes : (⌊⌊δ⌋⌋φ).unload = ⌈⌈δ⌉⌉φ.unload := by
  induction δ
  · simp only [LoadFormula.boxes, List.foldr_nil, Formula.boxes]
  · simpa [Formula.boxes, LoadFormula.boxes]

@[simp]
theorem unload_neg_loaded : (~'⌊α⌋(.loaded χ)).1.unload = ⌈α⌉(χ.unload) := by
  simp [LoadFormula.unload]

@[simp]
theorem unload_neg_normal : (~'⌊α⌋(.normal φ)).1.unload = ⌈α⌉φ := by
  simp [LoadFormula.unload]

/-- Load a possibly already loaded formula χ with a sequence δ of boxes.
The result is loaded iff δ≠[] or χ was loaded. -/
def AnyFormula.loadBoxes : List Program → AnyFormula → AnyFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ

@[simp]
lemma AnyFormula.boxes_nil : AnyFormula.loadBoxes [] ξ = ξ := by
  simp [AnyFormula.loadBoxes]

@[simp]
lemma AnyFormula.loadBoxes_cons : AnyFormula.loadBoxes (α :: γ) ξ = ⌊α⌋ (AnyFormula.loadBoxes γ ξ) := by
  simp [AnyFormula.loadBoxes]

def AnyFormula.unload : AnyFormula → Formula
  | .normal φ => φ
  | .loaded χ => χ.unload

/-! ## Spliting of loaded formulas -/

mutual
/-- Split any formula into the list of loaded boxes and the free formula. -/
@[simp]
def AnyFormula.split : (af : AnyFormula) → List Program × Formula
| .loaded lf => lf.split
| .normal f => ([], f)

/-- Split a loaded formula into the list of loaded boxes and the free formula. -/
@[simp]
def LoadFormula.split : (lf : LoadFormula) → List Program × Formula
| .box α af => (fun (δ,f) => (α :: δ, f)) af.split
end

@[simp]
theorem AnyFormula.split_normal (φ : Formula): (AnyFormula.normal φ).split = ([],φ) := by
  simp [AnyFormula.split]

theorem AnyFormula.box_split (af : AnyFormula) :
  (⌊α⌋af).split = (α :: af.split.1, af.split.2) := by
  cases af <;> simp

@[simp]
theorem LoadFormula.split_list_not_empty (lf : LoadFormula): lf.split.1 ≠ [] := by
  cases lf
  simp [LoadFormula.split]

@[simp]
def loadMulti_nonEmpty : (δ : List Program) → (h : δ ≠ []) → Formula → LoadFormula
| [ ],           h, _ => by exfalso; simp at *
| (α :: []),     _, φ => LoadFormula.box α φ
| (α :: d :: δ), _, φ => LoadFormula.box α (loadMulti_nonEmpty (d :: δ) (by simp) φ)

@[simp]
theorem loadMulti_nonEmpty_box (h : δ ≠ []) :
    loadMulti_nonEmpty (α :: δ) h' φ = ⌊α⌋(loadMulti_nonEmpty δ h φ) := by
  cases δ
  · absurd h; rfl
  · simp at *

theorem LoadFormula.split_eq_loadMulti_nonEmpty {δ φ} (lf : LoadFormula) :
    (h : lf.split = (δ,φ)) → lf = loadMulti_nonEmpty δ (by have := split_list_not_empty lf; simp_all) φ := by
  induction δ generalizing φ lf
  all_goals
    rcases lf_def : lf with ⟨α,af⟩
    intro h
  · simp [LoadFormula.split] at h
  case cons β δ IH =>
    cases af
    · unfold LoadFormula.split at h
      simp at h
      rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
      subst_eqs
      simp_all
    case loaded lf2 =>
      specialize @IH φ lf2 ?_
      · rw [AnyFormula.box_split] at h
        simp at *
        rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
        subst_eqs
        simp
      · rw [loadMulti_nonEmpty_box ?_]
        · simp
          rw [AnyFormula.box_split] at h
          simp at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp
          convert IH
        · simp
          rw [AnyFormula.box_split] at h
          simp at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp

theorem LoadFormula.split_eq_loadMulti_nonEmpty' {δ φ} (lf : LoadFormula)
    (h : δ ≠ []) (h2 : lf.split = (δ,φ)):
    lf = loadMulti_nonEmpty δ h φ := by
  have := LoadFormula.split_eq_loadMulti_nonEmpty lf h2
  rw [this]

theorem loadMulti_nonEmpty_eq_loadMulti :
    loadMulti_nonEmpty (δ ++ [α]) h φ = loadMulti δ α φ := by
  induction δ
  · simp
  case cons IH =>
    simp
    rw [IH]

theorem LoadFormula.split_eq_loadMulti (lf : LoadFormula) {δ α φ}
    (h : lf.split = (δ ++ [α], φ)) : lf = loadMulti δ α φ := by
  rw [LoadFormula.split_eq_loadMulti_nonEmpty' lf (by simp) h]
  apply loadMulti_nonEmpty_eq_loadMulti

theorem LoadFormula.exists_splitLast (lf : LoadFormula) :
    ∃ δ α, lf.split.1 = δ ++ [α] := by
  rcases lf with ⟨α, af⟩
  cases af
  case normal =>
    use [], α
    simp
  case loaded lf =>
    rcases LoadFormula.exists_splitLast lf with ⟨δ', α', IH⟩
    simp
    rw [IH]
    use α :: δ', α'
    simp

theorem LoadFormula.exists_loadMulti (lf : LoadFormula) :
    ∃ δ α φ, lf = loadMulti δ α φ := by
  rcases LoadFormula.exists_splitLast lf with ⟨δ, α, split1_def⟩
  use δ, α
  use lf.split.2
  apply LoadFormula.split_eq_loadMulti lf
  cases lfs_def : lf.split
  rw [lfs_def] at split1_def
  simp_all
