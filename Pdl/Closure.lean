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
        apply deep_IH
        specialize IH (m y) (isDec x y _) _ rfl a
        · sorry
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

def fTransRefl {α : Type} (f : Finset α → Finset α) (h : DecidableEq α)
    (m : Finset α → ℕ) (isDec : ∀ X, m (f X) < m X) :
    Finset α → Finset α
  | S => S ∪ (fTransRefl f h m isDec (f S))
termination_by
  fTransRefl f h m isDec S => m S
decreasing_by simp_wf; apply isDec

theorem fTransRefl.toNth {α : Type}
    {f : Finset α → Finset α}
    {m : Finset α → ℕ}
    (isDec : ∀ X, m (f X) < m X)
    (h : DecidableEq α)
    {k : ℕ}
    :
    ∀ (X : Finset α)
    (_ : k = m X)
    (x : α),
    x ∈ fTransRefl f h m isDec X ↔ ∃ i, x ∈ (f^[i]) X := by
  induction k using Nat.strong_induction_on
  case h k IH =>
    intro X k_is x
    constructor
    · intro x_in
      rw [fTransRefl] at x_in
      simp at x_in
      cases x_in
      case inl x_in_X =>
        use 0
        simp
        assumption
      case inr x_in =>
        subst k_is
        have := (IH (m (f X)) (isDec X) (f X) rfl x).1 x_in
        rcases this with ⟨j,foo⟩
        use j + 1
        simp
        exact foo
    · rintro ⟨i, x_in_fiX⟩
      cases i
      case zero =>
        simp at x_in_fiX
        rw [fTransRefl]
        simp
        left
        assumption
      case succ i =>
        rw [fTransRefl]
        simp
        right
        subst k_is
        specialize IH (m (f X)) (isDec X) (f X) rfl x
        rw [IH]
        simp at x_in_fiX
        use i

theorem fTransRefl.Trans (S T U : Finset α) (s t u : α)
    (f : Finset α → Finset α) (h : DecidableEq α)
    (m : Finset α → ℕ) (isDec : ∀ X, m (f X) < m X)
    (s_in_T : s ∈ fTransRefl f h m isDec {t})
    (t_in_U : t ∈ fTransRefl f h m isDec U)
    : s ∈ fTransRefl f h m isDec U
  := by
  rw [fTransRefl.toNth isDec h U rfl s]
  let T' : Finset α := {t}
  rw [fTransRefl.toNth isDec h T' rfl s] at s_in_T
  rw [fTransRefl.toNth isDec h U rfl t] at t_in_U
  rcases s_in_T with ⟨sj, s_in⟩
  rcases t_in_U with ⟨st, t_in⟩
  simp at *
  use sj + st
  rw [Function.iterate_add]
  simp at *
  convert s_in -- WRONG, but to make inclusion enough here we need monotonicity!?
  sorry

-- U          T           S
-- {...} -f-> {t,..} -f-> {s,..}
--               s!
