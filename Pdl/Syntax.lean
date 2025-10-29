import Mathlib.Data.List.Induction
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

prefix:70 "·" => Formula.atom_prop
prefix:70 "·" => Program.atom_prog
prefix:69 "~" => Formula.neg

@[simp]
instance Formula.instBot : Bot Formula := ⟨Formula.bottom⟩
@[simp]
instance Formula.insTop : Top Formula := ⟨Formula.neg Formula.bottom⟩

infixr:66 " ⋀ " => Formula.and
infixr:60 " ⋁ " => Formula.or
notation:55 φ:56 " ↣ " ψ:55 => ~ (φ ⋀ (~ψ))
notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) ⋀ (ψ ↣ φ)
notation "⌈" α "⌉" P => Formula.box α P
notation "⌈⌈" as "⌉⌉" P => Formula.boxes as P

infixl:33 ";'" => Program.sequence -- avoiding plain ";" which has a meaning in Lean 4
infixl:33 "⋓" => Program.union
prefix:33 "∗" => Program.star
prefix:33 "?'" => Program.test -- avoiding plain "?" which has a meaning in Lean 4

/-- A basic formula is of the form `¬⊥`, `p`, `¬p`, `[a]_` or `¬[a]_`.
Note: in the article also `⊥` is basic, but not here because we want
to apply `OneSidedLocalRule.bot` to it. -/
@[simp]
def Formula.basic : Formula → Bool
  | ⊥ => False
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | ⌈·_⌉_ => True
  | ~⌈·_⌉_ => True
  | _ => False

def Program.isAtomic : Program → Prop
| ·_ => true
| _ => false

-- Note: to make `decide` work we use `decidable_of_decidable_of_iff`.
instance : DecidablePred Program.isAtomic
| ·_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : True ↔ _)
| _ ;' _ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| a ⋓ _ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| ∗_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| ?'_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)

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

/-! ## Tools for Box Formulas -/

@[simp]
theorem Formula.boxes_nil : Formula.boxes [] φ = φ := by simp [Formula.boxes]

@[simp]
theorem Formula.boxes_cons : Formula.boxes (β :: δ) φ = ⌈β⌉(Formula.boxes δ φ) := by
  simp [Formula.boxes]

@[simp]
lemma Formula.boxes_injective : (⌈⌈αs⌉⌉φ) = (⌈⌈αs⌉⌉ψ) ↔ φ = ψ := by
  induction αs <;> simp_all

theorem boxes_last : Formula.boxes (δ ++ [α]) φ = Formula.boxes δ (⌈α⌉φ) :=
  by
  induction δ <;> simp [Formula.boxes]

theorem boxes_append : Formula.boxes (as ++ bs) P = Formula.boxes as (Formula.boxes bs P) :=
  by
  induction as <;> simp [Formula.boxes]

def boxesOf : Formula → List Program × Formula
| (Formula.box prog nextf) => let (rest,endf) := boxesOf nextf; ⟨prog::rest, endf⟩
| f => ([], f)

lemma def_of_boxesOf_def (h : boxesOf φ = (αs, ψ)) : φ = ⌈⌈αs⌉⌉ψ := by
  induction αs generalizing φ
  · unfold boxesOf at h
    cases φ <;> simp_all
  case cons α αs IH =>
    simp
    cases φ <;> simp_all [boxesOf]
    case box β φ =>
      apply IH
      grind

def Formula.isBox : Formula → Prop
| (Formula.box _ _ ) => True
| _ => False

lemma boxesOf_def_of_def_of_nonBox (h : φ = ⌈⌈αs⌉⌉ψ) (nonBox : ¬ ψ.isBox) :
    boxesOf φ = (αs, ψ) := by
  induction αs generalizing φ
  · unfold boxesOf
    cases φ <;> simp_all [Formula.isBox]; aesop
  case cons α αs IH =>
    subst h
    unfold boxesOf
    simp_all

@[simp]
lemma boxesOf_output_not_isBox : ¬ (boxesOf φ).2.isBox := by
  cases φ
  case box α φ =>
    have := @boxesOf_output_not_isBox φ
    simp_all [boxesOf, Formula.isBox]
  all_goals
    simp_all [boxesOf, Formula.isBox]

lemma Formula.boxes_cons_neq_self φ β δ : (⌈β⌉⌈⌈δ⌉⌉φ) ≠ φ := by
  cases φ <;> try grind [Formula.boxes]
  case box α φ =>
    rw [← boxes_last]
    simp only [ne_eq, box.injEq, not_and]
    intro β_eq_α
    rw [boxes_last]
    cases δ
    · exact @Formula.boxes_cons_neq_self φ α []
    case cons γ δ =>
      simp only [boxes_cons]
      rw [← boxes_last]
      exact @Formula.boxes_cons_neq_self φ γ (δ ++ [α])

lemma Formula.boxesOf_boxes_prefix (αs : List Program) φ : αs <+: (boxesOf (⌈⌈αs⌉⌉φ)).1 := by
  induction αs
  · simp_all
  case cons α αs IH =>
    simp only [boxes_cons, boxesOf, List.cons_prefix_cons, true_and]
    exact IH

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
theorem loadMulti_cons {β δ α φ} :
    loadMulti (β :: δ) α φ = LoadFormula.box β (loadMulti δ α φ) := by simp [loadMulti]

def LoadFormula.boxes : List Program → LoadFormula → LoadFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ

@[simp]
lemma LoadFormula.boxes_nil : LoadFormula.boxes [] χ = χ := by simp [LoadFormula.boxes]

lemma LoadFormula.boxes_cons :
    LoadFormula.boxes (b :: bs) φ = LoadFormula.box b (LoadFormula.boxes bs φ) :=
  by
  induction bs <;> simp [LoadFormula.boxes]

@[simp]
def LoadFormula.unload : LoadFormula → Formula
| LoadFormula.box α (.normal φ) => ⌈α⌉φ
| LoadFormula.box α (.loaded χ) => ⌈α⌉(unload χ)

@[simp]
theorem unload_loadMulti : (loadMulti δ α φ).unload  = ⌈⌈δ⌉⌉⌈α⌉φ := by
  induction δ
  · simp [Formula.boxes, loadMulti]
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
| NegLoadFormula.neg χ => ~ χ.unload

example : NegLoadFormula := ~'(⌊((·1) ;' (·2))⌋(⊤ : Formula))
example : NegLoadFormula := ~'(⌊⌊[·1, ·2]⌋⌋⌊·1⌋(⊤ : Formula))

theorem loadBoxes_append {as bs P} :
    LoadFormula.boxes (as ++ bs) P = LoadFormula.boxes as (LoadFormula.boxes bs P) :=
  by
  induction as <;> simp [LoadFormula.boxes]

theorem loadBoxes_last {a as c P} :
    (~'⌊a⌋LoadFormula.boxes (as ++ [c]) P) = (~'⌊a⌋LoadFormula.boxes as (⌊c⌋P)) :=
  by
  induction as <;> simp [LoadFormula.boxes]

@[simp]
theorem unload_boxes {δ φ} : (⌊⌊δ⌋⌋φ).unload = ⌈⌈δ⌉⌉φ.unload := by
  induction δ
  · simp only [LoadFormula.boxes, List.foldr_nil, Formula.boxes]
  · simpa [Formula.boxes, LoadFormula.boxes]

@[simp]
theorem unload_neg_loaded {α χ} : (~'⌊α⌋(.loaded χ)).1.unload = ⌈α⌉(χ.unload) := by
  simp [LoadFormula.unload]

@[simp]
theorem unload_neg_normal {α φ} : (~'⌊α⌋(.normal φ)).1.unload = ⌈α⌉φ := by
  simp [LoadFormula.unload]

/-- Load a possibly already loaded formula χ with a sequence δ of boxes.
The result is loaded iff δ≠[] or χ was loaded. -/
def AnyFormula.loadBoxes : List Program → AnyFormula → AnyFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ

@[simp]
lemma AnyFormula.boxes_nil {ξ} : AnyFormula.loadBoxes [] ξ = ξ := by
  simp [AnyFormula.loadBoxes]

@[simp]
lemma AnyFormula.loadBoxes_cons {α γ ξ} :
    AnyFormula.loadBoxes (α :: γ) ξ = ⌊α⌋ (AnyFormula.loadBoxes γ ξ) := by
  simp [AnyFormula.loadBoxes]

theorem AnyFormula.loadBoxes_append {as bs φ} :
    AnyFormula.loadBoxes (as ++ bs) φ = AnyFormula.loadBoxes as (AnyFormula.loadBoxes bs φ) :=
  by
  induction as <;> simp [AnyFormula.loadBoxes]

lemma AnyFormula.loadBoxes_loaded_eq_loaded_boxes {δ χ} :
    AnyFormula.loadBoxes δ (AnyFormula.loaded χ) = AnyFormula.loaded (⌊⌊δ⌋⌋χ) := by
  induction δ
  · simp
  case cons IH =>
    simp
    rw [IH]
    rfl

def AnyFormula.unload : AnyFormula → Formula
  | .normal φ => φ
  | .loaded χ => χ.unload

lemma box_loadBoxes_append_eq_of_loaded_eq_loadBoxes
    (h : AnyFormula.loaded χ' = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : (⌊d⌋AnyFormula.loadBoxes (δ ++ αs) (AnyFormula.normal φ)) = ⌊⌊d :: δ⌋⌋χ' := by
  cases αs
  · exfalso
    simp_all
  case cons α αs =>
    simp at h
    subst h
    rw [LoadFormula.boxes_cons]
    rw [AnyFormula.loadBoxes_append]
    rw [AnyFormula.loadBoxes_cons]
    simp -- d gone
    apply AnyFormula.loadBoxes_loaded_eq_loaded_boxes

@[simp]
lemma AnyFormulaBoxBoxes_eq_FormulaBoxLoadBoxes_inside_unload :
      ((⌊α⌋  AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)
    = ( ⌈α⌉((AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)) := by
  cases αs <;> simp_all [AnyFormula.loadBoxes, AnyFormula.unload]

lemma AnyFormula.loadBoxes_unload_eq_boxes {βs φ} :
    (AnyFormula.loadBoxes βs (AnyFormula.normal φ)).unload = ⌈⌈βs⌉⌉φ := by
  induction βs <;> simp [unload]
  case cons ih => exact ih

lemma loaded_eq_to_unload_eq χ αs φ
    (h : AnyFormula.loaded χ = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : χ.unload = ⌈⌈αs⌉⌉φ
    := by
  cases αs
  · simp_all
  case cons α1 αs =>
    cases αs
    · simp_all
    case cons α2 αs =>
      simp only [Formula.boxes_cons]
      rcases χ with  ⟨β, af⟩
      simp only [AnyFormula.loadBoxes_cons, AnyFormula.loaded.injEq, LoadFormula.box.injEq] at h
      rcases h with ⟨β_eq_α1, af_def⟩
      have := loaded_eq_to_unload_eq ((⌊α2⌋AnyFormula.loadBoxes αs (.normal φ))) (α2 :: αs) _ rfl
      subst_eqs
      simp_all

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
theorem AnyFormula.split_normal (φ : Formula) : (AnyFormula.normal φ).split = ([],φ) := by
  simp [AnyFormula.split]

theorem AnyFormula.split_eq_nil_is_normal (ξ φ) : ξ.split = ([],φ) → ξ = AnyFormula.normal φ := by
  rcases ξ with _|⟨_,_⟩ <;> simp [AnyFormula.split]

mutual
lemma LoadFormula.split_inj {ξ ξ' : LoadFormula} (h : ξ.split = ξ'.split) : ξ = ξ' := by
  rcases ξ with ⟨α, ξ⟩
  rcases ξ' with ⟨α', ξ'⟩
  simp only [LoadFormula.split, Prod.mk.injEq, List.cons.injEq, LoadFormula.box.injEq] at *
  constructor
  · tauto
  case right =>
    apply AnyFormula.split_inj
    aesop

lemma AnyFormula.split_inj {ξ ξ' : AnyFormula} (h : ξ.split = ξ'.split) : ξ = ξ' := by
  rcases ξ with φ|ξ <;> rcases ξ' with φ'|ξ' <;> simp_all
  case normal.loaded =>
    cases ξ'; simp_all
  case loaded.normal =>
    cases ξ; simp_all
  case loaded.loaded =>
    exact LoadFormula.split_inj h
end

theorem AnyFormula.box_split (af : AnyFormula) :
  (⌊α⌋af).split = (α :: af.split.1, af.split.2) := by
  cases af <;> simp

@[simp]
theorem LoadFormula.split_list_not_empty (lf : LoadFormula) : lf.split.1 ≠ [] := by
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

@[simp]
lemma loadMulti_split : (loadMulti αs α φ).split = (αs ++ [α], φ) := by
  induction αs <;> simp_all

@[simp]
lemma loadMulti_nonEmpty_unload {δ h φ} : (loadMulti_nonEmpty δ h φ).unload  = ⌈⌈δ⌉⌉φ := by
  induction δ
  · exfalso; absurd h; rfl
  case cons α αs IH =>
    unfold loadMulti_nonEmpty
    cases αs <;> simp
    case cons β βs => exact IH

theorem LoadFormula.split_eq_loadMulti_nonEmpty {δ φ} (lf : LoadFormula) : (h : lf.split = (δ,φ)) →
    lf = loadMulti_nonEmpty δ (by have := split_list_not_empty lf; simp_all) φ := by
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

theorem LoadFormula.split_eq_loadMulti_nonEmpty' {δ φ} (lf : LoadFormula) (h : δ ≠ [])
    (h2 : lf.split = (δ, φ)) : lf = loadMulti_nonEmpty δ h φ := by
  have := LoadFormula.split_eq_loadMulti_nonEmpty lf h2
  rw [this]

theorem loadMulti_nonEmpty_eq_loadMulti {δ α h φ} :
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

lemma loadMulti_eq_of_some (h : δ.head? = some d) :
    loadMulti δ β φ = ⌊d⌋AnyFormula.loaded (loadMulti δ.tail β φ) := by
  cases δ
  <;> simp_all

lemma loadMulti_eq_loadBoxes :
    AnyFormula.loaded (loadMulti δ α φ) = AnyFormula.loadBoxes (δ ++ [α]) φ := by
  induction δ <;> aesop

/-! ## splitLast -/

/-- Helper function for `YsetLoad'` to get last list element. -/
def splitLast : List α → Option (List α × α)
| [] => none
| (x :: xs) => some <| match splitLast xs with
  | none => ([], x)
  | some (ys, y) => (x::ys, y)

@[simp]
theorem splitLast_nil : splitLast [] = (none : Option (List α × α)) := by simp [splitLast]

theorem nil_of_splitLast_none : splitLast δs = none → δs = [] := by
  cases δs <;> simp [splitLast]

theorem splitLast_cons_eq_some (x : α) (xs : List α) :
    splitLast (x :: xs) = some ((x :: xs).dropLast, (x :: xs).getLast (List.cons_ne_nil x xs)) := by
  cases xs
  · simp [splitLast]
  case cons y ys =>
    have := splitLast_cons_eq_some y ys -- recursion!
    unfold splitLast
    rw [this]
    simp

@[simp]
theorem splitLast_append_singleton : splitLast (xs ++ [x]) = some (xs, x) := by
  induction xs
  · simp [splitLast]
  case cons IH =>
    simp [splitLast]
    rw [IH]

lemma splitLast_inj (h : splitLast αs = splitLast βs) :
    αs = βs := by
  induction αs using List.reverseRecOn <;> induction βs using List.reverseRecOn
  · rfl
  · exfalso
    simp_all
  · exfalso
    simp_all
  aesop

lemma splitLast_undo_of_some (h : splitLast αs = some βs_b) :
    βs_b.1 ++ [βs_b.2] = αs := by
  rcases αs with _ |⟨α,αs⟩
  · exfalso
    simp_all
  have := @splitLast_cons_eq_some _ α αs
  rw [h] at this
  simp at this
  subst this
  simp
  apply List.dropLast_append_getLast

lemma loadMulti_of_splitLast_cons {α αs βs β φ} (h : splitLast (α :: αs) = some ⟨βs, β⟩) :
    loadMulti βs β φ = ⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ) := by
  have : (α :: αs) = βs ++ [β] := by
    rw [← @splitLast_append_singleton] at h
    exact splitLast_inj h
  cases αs
  · unfold splitLast at h
    simp at h
    cases h
    subst_eqs
    simp at *
  case cons α2 αs =>
    have ⟨δβ2, new_h⟩ : ∃ δ2_β2, splitLast (α2 :: αs) = some δ2_β2 := by simp [splitLast]
    rw [AnyFormula.loadBoxes_cons]
    have IH := @loadMulti_of_splitLast_cons α2 αs _ _ φ new_h
    rw [← IH]; clear IH
    cases βs
    · exfalso
      unfold splitLast at h
      simp at h
      cases h
    case cons β2 βs =>
      simp_all
      subst new_h
      simp_all
