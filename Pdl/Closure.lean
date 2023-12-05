import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Iterate

-- reflexive transitive closure of a function on finsets

def fTransRefl {α : Type} (f : Finset α → Finset α ) (h : DecidableEq α)
    (m : Finset α → ℕ) (isDec : ∀ X, m (f X) < m X) :
    Finset α → Finset α
  | S => S ∪ (fTransRefl f h m isDec (f S))
termination_by
  fTransRefl f h m isDec S => m S
decreasing_by simp_wf; apply isDec

theorem ftr.toNth {α : Type}
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

theorem ftr.Trans (S T U : Finset α) (s t u : α)
    (f : Finset α → Finset α) (h : DecidableEq α)
    (m : Finset α → ℕ) (isDec : ∀ X, m (f X) < m X)
    (s_in_T : s ∈ fTransRefl f h m isDec {t})
    (t_in_U : t ∈ fTransRefl f h m isDec U)
    : s ∈ fTransRefl f h m isDec U
  := by
  rw [ftr.toNth isDec h U rfl s]
  let T' : Finset α := {t}
  rw [ftr.toNth isDec h T' rfl s] at s_in_T
  rw [ftr.toNth isDec h U rfl t] at t_in_U
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
