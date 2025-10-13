import Mathlib.Algebra.Order.BigOperators.Group.List

import Pdl.Measures
import Pdl.Vocab

/-! # Fischer-Ladner Closure

Here we define a closure on sets of formulas.
Our main reference for this closure is Section 6.1 of [HKT2000]
See also Definition 4.79 and Exercise 4.8.2 in [BRV2001].
An alternative version following the proof of Theorem 3.2 in [FL1979]
but unfinished is in `Unused/FischerLadnerViaPreForms.lean`.

- [FL1979] Michael J. Fischer and Richard E. Ladner (1979):
  *Propositional dynamic logic of regular programs*.
	Journal of Computer and System Sciences, vol 18, no 2, pp. 194--211.
	<https://doi.org/10.1016/0022-0000(79)90046-1>

- [BRV2001] Patrick Blackburn, Maarten de Rijke and Yde Venema (2001):
	*Modal Logic*.
	Cambridge University Press.
  <https://www.mlbook.org/>

- [HKT2000] David Harel, Dexter Kozen, and Jerzy Tiuryn (2000):
  *Dynamic Logic*.
  MIT Press, 2000.

-/

/-! ## Definition  -/

mutual
/-- The Fischer-Ladner closure of a formula.
See Section 6.1 of [HKT2000]. Note that there only implication is given.
For our `Formula` type we also need to cover conjunction and negation.
Also note that we are closing under single negations as well here.
The main work is done by `FLb`, which also ensures termination. -/
def FL : Formula → List Formula
| ⊥ => [⊥, ~⊥]
| ·p => [·p, ~·p]
| φ⋀ψ => [φ⋀ψ, ~(φ⋀ψ), ~φ, ~ψ] ++ FL φ ++ FL ψ -- ~φ and ~ψ needed for ~~ case.
| ⌈α⌉φ => [~⌈α⌉φ, ~φ] ++ FLb α φ ++ FL φ -- Note: `~⌈α⌉φ` seems needed for `FLb_trans`.
| ~φ => [~φ] ++ FL φ -- first element needed to deal with ~~φ, ~~~φ etc.

/-- The Fischer-Ladner closure of a box formula,
not recursing into the formula after the box. -/
def FLb : Program → Formula → List Formula
| ·a, φ => [ ⌈·a⌉φ, ~⌈·a⌉φ ]
| α⋓β, φ => [ ⌈α⋓β⌉φ, ~⌈α⋓β⌉φ ] ++ FLb α φ ++ FLb β φ
| α;'β, φ => [ ⌈α;'β⌉φ, ~⌈α;'β⌉φ ] ++ FLb α (⌈β⌉φ) ++ FLb β φ
| ∗α, φ => [ ⌈∗α⌉φ, ~⌈∗α⌉φ ] ++ FLb α (⌈∗α⌉φ)
| ?'τ, φ => [ ⌈?'τ⌉φ, ~⌈?'τ⌉φ ] ++ FL τ
end

/-! ## Lemmas  -/

def isNeg : Formula → Prop
| ~_ => True
| _ => False

lemma FL_single_neg_closed {φ} :
    ¬ isNeg φ → ~φ ∈ FL φ := by
  cases φ <;> simp [FL, isNeg]

@[simp]
lemma FL_refl {φ} :
    φ ∈ FL φ := by
  cases φ <;> simp [FL]
  case box α φ =>
    cases α <;> simp [FLb]

@[simp]
lemma FLb_refl {α φ} :
    (⌈α⌉φ) ∈ FLb α φ := by
  cases α <;> simp [FLb]

mutual
/-- Lemma 6.1(i) from [HKT2000] -/
lemma FL_trans {φ ψ} :
    ψ ∈ FL φ → FL ψ ⊆ FL φ := by
  intro ψ_in
  cases φ <;> simp [FL] at *
  · cases ψ_in <;> subst_eqs <;> simp [FL]
  · cases ψ_in <;> subst_eqs <;> simp [FL]
  · case neg φ =>
    cases ψ_in <;> subst_eqs
    · simp [FL]
    · have IH := @FL_trans φ
      aesop
  case and φ1 φ2 =>
    rcases ψ_in with h|h|h|h|h|h <;> subst_eqs
    · simp [FL]
    · simp [FL]
    · simp [FL]; grind
    · simp [FL]; grind
    · have IH1 := @FL_trans φ1 ψ h
      grind
    · have IH2 := @FL_trans φ2 ψ h
      grind
  case box α φ =>
    rcases ψ_in with h|h|h|h
    · subst_eqs
      simp [FL]
    · subst_eqs
      grind [FL]
    · have := FLb_trans h
      grind [FL]
    · have IH := @FL_trans φ ψ
      grind

/-- Lemma 6.1(ii) from [HKT2000] -/
lemma FLb_trans {α φ ψ} :
    ψ ∈ FLb α φ → FL ψ ⊆ FLb α φ ++ FL (~φ) := by
  intro ψ_in
  cases α <;> simp [FLb] at *
  · cases ψ_in <;> subst_eqs <;> grind [FL, FLb]
  case sequence α1 α2 =>
    rcases ψ_in with h|h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH1 := @FLb_trans α1 (⌈α2⌉φ) ψ h
      intro x x_in
      specialize IH1 x_in
      simp [FL] at *
      rcases IH1 with _|_|_|_ <;> try (aesop; done)
      · subst_eqs
        simp at *
        right
        right
        left
        cases α2 <;> simp [FLb]
    · have IH2 := @FLb_trans α2 φ ψ h
      grind [FL]
  case union α1 α2 =>
    rcases ψ_in with h|h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH1 := @FLb_trans α1 φ ψ h
      intro x x_in
      specialize IH1 x_in
      aesop
    · have IH2 := @FLb_trans α2 φ ψ h
      intro x x_in
      specialize IH2 x_in
      aesop
  case star α =>
    rcases ψ_in with h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH := @FLb_trans α (⌈∗α⌉φ) ψ h
      intro x x_in
      specialize IH x_in
      simp [FL] at *
      rcases IH with h|h|h|h|h
      · aesop
      · aesop
      · aesop
      · grind [FLb]
      · aesop
  case test τ =>
    rcases ψ_in with h|h|h
    · subst_eqs; grind [FL, FLb]
    · subst_eqs; grind [FL, FLb]
    · have := @FL_trans τ ψ
      grind [FL]
end

/- Lemma 6.2(i) -/
lemma FL_box_sub {φ α ψ} :
    (⌈α⌉ψ) ∈ FL φ → ψ ∈ FL φ := by
  intro hyp
  apply FL_trans hyp
  simp [FL]

/- Lemma 6.2(ii) -/
lemma FL_box_test {φ τ ψ} :
    (⌈?'τ⌉ψ) ∈ FL φ → τ ∈ FL φ := by
  intro hyp
  apply FL_trans hyp
  simp [FL, FLb]

/- Lemma 6.2(iii) -/
lemma FL_box_cup {φ α β ψ} :
    (⌈α ⋓ β⌉ψ) ∈ FL φ → (⌈α⌉ψ) ∈ FL φ ∧ (⌈β⌉ψ) ∈ FL φ := by
  intro hyp
  have := FL_trans hyp
  simp [FL, FLb] at this
  aesop

/- Lemma 6.2(iv) -/
lemma FL_box_seq {φ α β ψ} :
    (⌈α ;' β⌉ψ) ∈ FL φ → (⌈α⌉⌈β⌉ψ) ∈ FL φ ∧ (⌈β⌉ψ) ∈ FL φ := by
  intro hyp
  have := FL_trans hyp
  simp [FL, FLb] at this
  aesop

/- Lemma 6.2(v) -/
lemma FL_box_star {φ α ψ} :
    (⌈∗α⌉ψ) ∈ FL φ → (⌈α⌉⌈∗α⌉ψ) ∈ FL φ := by
  intro hyp
  have := FL_trans hyp
  simp [FL, FLb] at this
  aesop

def FLL (L : List Formula) : List Formula := L.flatMap FL

@[simp]
lemma FLL_refl_sub {L} : L ⊆ FLL L := by induction L <;> simp_all [FLL]

lemma FLL_sub {L1 L2} : L1 ⊆ L2 → FLL L1 ⊆ FLL L2 := by
  unfold FLL
  intro h x x_in
  grind

@[simp]
lemma FLL_nil : FLL [] = [] := List.flatMap_nil

@[simp]
lemma FLL_singelton : FLL [φ] = FL φ := by simp [FLL]

@[simp]
lemma FLL_idem_ext {L φ} : φ ∈ FLL (FLL L) ↔ φ ∈ FLL L := by
  constructor
  · unfold FLL
    intro φ_in
    have := @FL_trans
    grind
  · intro φ_in
    have := @FLL_refl_sub (FLL L)
    grind

lemma FLL_sub_FLL_iff_sub_FLL {L K : List Formula} : L ⊆ FLL K ↔ FLL L ⊆ FLL K := by
  constructor
  · unfold FLL
    rintro h φ' φ'_in
    simp_all only [List.mem_flatMap]
    rcases φ'_in with ⟨φ, φ_in, φ'_in⟩
    specialize h φ_in
    simp only [List.mem_flatMap] at h
    rcases h with ⟨φ'', φ''_in, φ_in⟩
    use φ''
    have := @FL_trans
    grind
  · have := @FLL_refl_sub L
    grind

lemma FLL_append_eq {L K} : FLL (L ++ K) = FLL L ++ FLL K := by simp [FLL]

lemma FLL_diff_sub {L K} : FLL (L \ K) ⊆ FLL L := FLL_sub (List.diff_subset L K)

/-- Being a member of the FL closure of a list does not depend on the position. -/
lemma FLL_ext (h : ∀ φ, φ ∈ L1 ↔ φ ∈ L2) φ : φ ∈ FLL L1  ↔ φ ∈ FLL L2 := by
  simp [FLL] at *
  aesop

/-! ## FL stays in the Vocabulary -/

mutual

lemma FL_stays_in_voc {φ ψ} (ψ_in_FL : ψ ∈ FL φ) : ψ.voc ⊆ φ.voc := by
  cases φ <;> simp_all [FL]
  case neg φ =>
    rcases ψ_in_FL with _|h <;> subst_eqs
    · simp at *
    · exact FL_stays_in_voc h
  case and φ1 φ2 =>
    rcases ψ_in_FL with h|h|h|h|h|h
    · subst_eqs
      simp
    · subst_eqs
      simp
    · subst_eqs
      simp
    · subst_eqs
      simp
    · have IH := FL_stays_in_voc h
      grind
    · have IH := FL_stays_in_voc h
      grind
  case box α φ =>
    rcases ψ_in_FL with h|h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · exact FLb_stays_in_voc h
    · have IH := FL_stays_in_voc h
      grind
  all_goals
    grind [Formula.voc]

lemma FLb_stays_in_voc {α φ ψ} (ψ_in_FLb : ψ ∈ FLb α φ) : ψ.voc ⊆ α.voc ∪ φ.voc := by
  cases α <;> simp_all [FLb]
  case atom_prog =>
    aesop
  case sequence α1 α2 =>
    rcases ψ_in_FLb with h|h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FLb_stays_in_voc h
      aesop
    · have IH := FLb_stays_in_voc h
      grind
  case union α1 α2 =>
    rcases ψ_in_FLb with h|h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FLb_stays_in_voc h
      grind
    · have IH := FLb_stays_in_voc h
      grind
  case test τ =>
    rcases ψ_in_FLb with h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FL_stays_in_voc h
      grind
  case star α =>
    rcases ψ_in_FLb with h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FLb_stays_in_voc h
      aesop

end
