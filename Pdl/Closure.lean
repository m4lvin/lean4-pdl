import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Basic

-- reflexive transitive closure of a decreasing function
def ftr {α : Type}
    (f : α → Finset α)
    (h : DecidableEq α)
    (m : α → ℕ)
    (isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x) :
    α → Finset α
  | x => {x} ∪ (f x).attach.biUnion (fun ⟨y, y_in⟩ => have := y_in; ftr f h m isDec y)
termination_by
  ftr f h m isDec S => m S
decreasing_by simp_wf; apply isDec x _ (by assumption)
-- have := ... to avoid false waring, see https://github.com/leanprover/lean4/issues/2920

theorem ftr.iff (x y : α)
    {f : α → Finset α}
    {h : DecidableEq α}
    {m : α → ℕ}
    {isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x} :
    y ∈ ftr f h m isDec x  ↔  y = x ∨ ∃ z, z ∈ f x ∧ y ∈ ftr f h m isDec z := by
  constructor
  · intro y_in
    unfold ftr at y_in
    simp at y_in
    convert y_in
  · intro claim
    unfold ftr
    simp
    convert claim

theorem biUnion_subset (h : DecidableEq α) (f) : ∀ i, ∀ (X Y : Finset α),
    X ⊆ Y → ((λ X => X.biUnion f)^[i]) X ⊆ ((λ X => X.biUnion f)^[i]) Y :=  by
  intro i
  induction i
  case zero =>
    intro X Y
    intro X_sub_Y
    simp at *
    assumption
  case succ i IH =>
    intro X Y
    simp
    intro X_sub_Y
    exact IH (X.biUnion f) (Y.biUnion f) (Finset.biUnion_subset_biUnion_of_subset_left f X_sub_Y)

theorem ftr.toNth {α : Type}
    (f : α → Finset α)
    (h : DecidableEq α)
    (m : α → ℕ)
    (isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x)
    {k : ℕ}
    :
    ∀ (x : α)
    (_ : k = m x)
    (y : α),
    y ∈ ftr f h m isDec x ↔ (∃ i, y ∈ ((λ X => Finset.biUnion X f)^[i]) {x}) := by
  induction k using Nat.strong_induction_on
  case h k IH =>
    intro x k_is y
    subst k_is
    constructor
    · intro y_in
      rw [ftr] at y_in
      simp at y_in
      cases y_in
      case inl y_is_x =>
        use 0
        simp
        assumption
      case inr y_in =>
        rcases y_in with ⟨z, z_in_fx, y_in_ftr_z⟩
        have := (IH (m z) (isDec x z z_in_fx) z rfl y).1 y_in_ftr_z
        rcases this with ⟨j,foo⟩
        use j + 1
        simp
        rw [← @Finset.singleton_subset_iff] at z_in_fx
        exact biUnion_subset h f j {z} (f x) z_in_fx foo
    · simp
      intro i
      induction i
      all_goals intro y_in_fiX
      case zero =>
        simp at y_in_fiX
        rw [ftr]
        simp
        left
        assumption
      case succ i deep_IH =>
        rw [Function.iterate_succ'] at y_in_fiX
        simp at y_in_fiX
        rcases y_in_fiX with ⟨a, a_claim⟩
        specialize IH (m y) (isDec x y _) _ rfl y
        · sorry
        -- PROBLEM: deep_IH is not general enough! reformulate theorem above?
        rw [ftr.iff]
        sorry

theorem ftr.Trans (s t u : α)
    (f : α → Finset α)
    (h : DecidableEq α)
    (m : α → ℕ)
    (isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x)
    (s_in_ftr_t : s ∈ ftr f h m isDec t)
    (t_in_ftr_u : t ∈ ftr f h m isDec u) :
    s ∈ ftr f h m isDec u
  := by
  rw [ftr.toNth f h m isDec _ rfl s]
  rw [ftr.toNth f h m isDec _ rfl s] at s_in_ftr_t
  rw [ftr.toNth f h m isDec _ rfl t] at t_in_ftr_u
  rcases s_in_ftr_t with ⟨i, s_in⟩
  rcases t_in_ftr_u with ⟨j, t_in⟩
  use i + j
  rw [Function.iterate_add]
  simp at *
  rw [← @Finset.singleton_subset_iff] at t_in
  have := biUnion_subset h f i {t} ((fun X => Finset.biUnion X f)^[j] {u}) t_in
  apply this
  assumption
