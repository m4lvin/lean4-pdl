import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Basic

-- NOTES:

-- This currently works for the diamond cases in DagTableau.
-- For boxes we need something different, namely replacing the
-- measure m : (m : α → ℕ)
-- with a well-founded < : α → α → Prop

-- In general, some of these things should already be in Mathlib.
-- But maybe not computable / decidable?

-- reflexive transitive closure of a decreasing function
def ftr {α : Type}
    (f : α → List α)
    (m : α → ℕ)
    (isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x) :
    α → List α
  | x => [x] ++ ((f x).attach.map (fun ⟨y,y_in⟩ => have := y_in; ftr f m isDec y)).join
termination_by
  S => m S
decreasing_by simp_wf; apply isDec x _ (by assumption)
-- have := ... to avoid false waring, see https://github.com/leanprover/lean4/issues/2920

theorem ftr.iff (x y : α)
    {f : α → List α}
    {m : α → ℕ}
    {isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x} :
    y ∈ ftr f m isDec x  ↔  y = x ∨ ∃ z, z ∈ f x ∧ y ∈ ftr f m isDec z := by
  constructor
  · intro y_in
    unfold ftr at y_in
    simp at y_in
    convert y_in
  · intro claim
    unfold ftr
    simp
    convert claim

theorem ftr.iff' {x y : α}
    {f : α → List α}
    {m : α → ℕ}
    {isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x} :
    y ∈ ftr f m isDec x  ↔  y = x ∨ ∃ z, z ∈ ftr f m isDec x ∧ y ∈ f z := by
  constructor
  · intro y_in
    unfold ftr at y_in
    simp at y_in
    cases y_in
    · left; assumption
    case inr hyp =>
      right
      rcases hyp with ⟨a, a_in_x, y_in_ftr_a⟩
      rw [ftr.iff'] at y_in_ftr_a -- termination??
      cases y_in_ftr_a
      case inl y_is_a =>
        subst y_is_a
        use x
        unfold ftr
        aesop
      case inr hyp =>
        rcases hyp with ⟨z, z_in_ftr_a, y_in_fz⟩
        use z
        rw [ftr.iff]
        aesop
  · intro claim
    cases claim
    · unfold ftr
      simp
      left
      assumption
    case inr hyp =>
      rcases hyp with ⟨a, a_in_ftr_x, y_in_fa⟩
      rw [ftr.iff] at a_in_ftr_x
      cases a_in_ftr_x
      case inl a_is_x =>
        subst a_is_x
        unfold ftr
        unfold ftr
        aesop
      case inr hyp =>
        rcases hyp with ⟨z, z_in_fx, a_in_ftr_z⟩
        have y_in_ftr_z : y ∈ ftr f m isDec z := by
          rw [ftr.iff']
          right
          use a
        unfold ftr
        aesop
termination_by m x
decreasing_by
  all_goals (simp_wf; apply isDec; tauto)

theorem biUnion_subset (f : α → List α) : ∀ i, ∀ (X Y : List α),
    X ⊆ Y → ((λ X => (X.map f).join)^[i]) X ⊆ ((λ X => (X.map f).join)^[i]) Y :=  by
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
    apply IH
    have := List.map_subset f X_sub_Y
    intro a a_in
    aesop

theorem ftr.fromNth {α : Type}
    {f : α → List α}
    {m : α → ℕ}
    {isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x}
    {i : ℕ}
    :
    ∀ {x y : α}, (y ∈ ((λ X => (X.map f).join)^[i]) [x]) → (y ∈ ftr f m isDec x) := by
      induction i
      all_goals intro x y y_in
      case zero =>
        simp at y_in
        rw [ftr]
        simp
        left
        assumption
      case succ i IH =>
        rw [ftr.iff']
        rw [Function.iterate_succ'] at y_in
        simp at y_in
        rcases y_in with ⟨b, b_in_fiX, y_in_fb⟩
        right
        use b
        constructor
        · apply IH
          assumption
        · assumption

theorem ftr.toNth {α : Type}
    {f : α → List α}
    {m : α → ℕ}
    {isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x}
    (k : ℕ)
    :
    ∀ {x : α}
    {_ : k = m x}
    {y : α},
    (y ∈ ftr f m isDec x → (∃ i, y ∈ ((λ X => (X.map f).join)^[i]) [x])) := by
  induction k using Nat.strong_induction_on
  case h k IH =>
    intro x k_is y
    intro y_in -- left to right
    rw [ftr] at y_in
    simp at y_in
    cases y_in
    case inl y_is_x =>
      use 0
      simp
      assumption
    case inr y_in =>
      rcases y_in with ⟨z, z_in_fx, y_in_ftr_z⟩
      have := (@IH (m z) (by rw [k_is]; exact isDec x z z_in_fx) z rfl y) y_in_ftr_z
      rcases this with ⟨j,y_in⟩
      use j + 1
      simp
      exact biUnion_subset f j [z] (f x) (by simp; assumption) y_in

theorem ftr.iff_Nth {α : Type}
    (f : α → List α)
    (m : α → ℕ)
    (isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x)
    (x : α)
    (y : α)
    :
    (y ∈ ftr f m isDec x ↔ (∃ i, y ∈ ((λ X => (X.map f).join)^[i]) [x])) := by
   constructor
   · apply ftr.toNth (m x); rfl
   · rintro ⟨i,claim⟩; apply ftr.fromNth claim

theorem ftr.Trans (s t u : α)
    (f : α → List α)
    (m : α → ℕ)
    (isDec : ∀ (x : α), ∀ y ∈ (f x), m y < m x)
    (s_in_ftr_t : s ∈ ftr f m isDec t)
    (t_in_ftr_u : t ∈ ftr f m isDec u) :
    s ∈ ftr f m isDec u
  := by
  rw [ftr.iff_Nth]
  rw [ftr.iff_Nth] at s_in_ftr_t
  rw [ftr.iff_Nth] at t_in_ftr_u
  rcases s_in_ftr_t with ⟨i, s_in⟩
  rcases t_in_ftr_u with ⟨j, t_in⟩
  use i + j
  rw [Function.iterate_add]
  simp at *
  apply biUnion_subset f i [t] ((fun X => (X.map f).join)^[j] [u]) (by simp; aesop)
  assumption
