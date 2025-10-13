import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.Linarith

/-! # Helper Lemmas about List.Vector

These were previously used in `Soundness.lean`.
-/

lemma List.nonempty_drop_sub_succ {δ : List α} (δ_not_empty : δ ≠ []) (k : Fin δ.length) :
  (List.drop (k.val + 1) δ).length + 1 = δ.length.succ - (k.val + 1) :=
  by
  simp
  have : ∀ n, n ≠ 0 → (k.val < n) → n - (k.val + 1) + 1 = n - k.val := by
    intro n n_no_zero k_lt_n
    induction n <;> simp_all
    omega
  apply this <;> aesop

lemma List.Vector.my_cast_head {α} (n m : Nat) (v : List.Vector α n.succ) (h : n = m) :
    (h ▸ v).head = v.head := by subst h; simp

lemma List.Vector.my_cast_getElem {α} (n m) (v : List.Vector α n.succ) (h : n = m) (i : Fin n) :
    (h ▸ v)[i] = v[i] := by subst h; simp

lemma List.Vector.my_cast_eq_val_head {α} (n m : Nat) (v : List.Vector α n.succ) (h : n = m) h2 :
    (h ▸ v).head = v.1.head h2 := by
  rcases v with ⟨l,l_prop⟩
  rw [List.Vector.my_cast_head]
  induction l <;> simp_all
  · exfalso; aesop
  · aesop

lemma List.Vector.my_cast_toList {α} (n m : ℕ) (t : List α) ht (h : n = m) :
    t = List.Vector.toList (h ▸ (⟨t, ht⟩ : List.Vector α n)) := by subst h; simp

lemma aux_simplify_vector_type {α} {q p : ℕ} (t : List α) h :
    let help (n m : ℕ) : (n + 1 + 1 - (m + 1 + 1)) = n + 1 - (m + 1) := by omega
    (⟨t, h⟩ : List.Vector α (q + 1 + 1 - (p + 1 + 1)))
    = (help q p) ▸ ⟨t, by simp at h; simp; exact h⟩ := by
    apply List.Vector.eq
    simp
    apply List.Vector.my_cast_toList

lemma List.Vector.my_drop_succ_cons {α} {m n : ℕ} (x : α) (t : List α) h (hyp : m < n) :
    let help : (n + 1 - (m + 1)) = n - m := by omega
    List.Vector.drop (m + 1) (⟨x :: t, h⟩ : List.Vector α n.succ)
    = help ▸ List.Vector.drop m ⟨t, by simp at h; exact h⟩ := by
    induction m generalizing t n h x with
    | zero => simp [List.Vector.drop]
    | succ p ih =>
      cases t with
      | nil => simp at h; omega
      | cons head tail =>
        cases n with
        | zero => omega
        | succ q =>
        simp [List.Vector.drop] at ih
        simp [List.Vector.drop]
        rw [aux_simplify_vector_type]

lemma List.Vector.get_succ_eq_head_drop {α n} {v : List.Vector α n.succ} (k : Fin n) (j : Nat)
    (h : (n + 1 - (k.val + 1)) = j + 1) :
    v.get k.succ = (h ▸ v.drop (k.val + 1)).head
    := by
  rcases v with ⟨l, l_prop⟩
  induction l generalizing n
  · exfalso
    aesop
  case cons he ta IH =>
    simp only [Nat.succ_eq_add_one] at IH
    rw [← List.Vector.get_tail_succ]
    simp only [List.Vector.tail]
    cases n
    · exfalso
      cases k
      linarith
    case succ n =>
      cases k using Fin.cases
      · rw [Vector.my_drop_succ_cons]
        · simp [List.Vector.drop]
          convert rfl using 2 <;> simp_all
        · simp
      case succ k =>
        specialize @IH n k (by simp_all) (by simp_all)
        simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one, Fin.val_succ]
        rw [IH]
        clear IH
        rw [Vector.my_drop_succ_cons]
        · convert rfl
          simp only [eqRec_heq_iff_heq, heq_eq_eq]
        omega

/-- Generalized vesrion of `Vector.drop_get_eq_get_add`. -/
lemma List.Vector.drop_get_eq_get_add' (v : List.Vector α n) (l r : ℕ) {h : i = l + r} {hi hr} :
    v.get ⟨i, hi⟩ = (List.Vector.drop l v).get ⟨r, hr⟩ := by
  rcases v with ⟨t, t_prop⟩
  simp [List.Vector.get, List.Vector.drop, h]

/-- A Vector analogue of `List.getElem_drop`. -/
lemma List.Vector.drop_get_eq_get_add {n : Nat} (v : List.Vector α n) (k : Nat)
    (i : Fin (n - k))
    (still_lt : k + i.val < n) :
    (v.drop k).get i = v.get ⟨k + i.val, still_lt⟩ := by
  apply Eq.symm (List.Vector.drop_get_eq_get_add' ..)
  rfl

-- FIXME is this in mathlib?
lemma Fin.my_cast_val (n m : Nat) (h : n = m) (j_lt : j < n) :
    (h ▸ ( ⟨j, j_lt⟩ : Fin n)).val = j := by
  aesop

lemma List.Vector.drop_last_eq_last {v : List.Vector α n.succ} (k : Fin n) (j : Nat)
    (h : (n.succ - (k + 1)) = j.succ) :
    (h ▸ v.drop (k + 1)).last = v.last := by
  unfold List.Vector.last
  have := List.Vector.drop_get_eq_get_add v (k.val + 1) (h ▸ Fin.last j) (by omega)
  convert this using 2
  · linarith
  · simp
  · simp
  · ext
    unfold Fin.last
    rcases k with ⟨k, k_lt⟩
    simp only [Nat.succ_eq_add_one]
    simp only [Nat.succ_eq_add_one, Nat.reduceSubDiff] at h
    rw [Fin.my_cast_val (j + 1) (n + 1 - (k + 1)) (by linarith) (Nat.lt_succ_self j)]
    omega

lemma List.Vector.my_cast_heq (n m : Nat) (h : n = m) (v : List.Vector α n) :
    HEq (h ▸ v : List.Vector α m) v := by
  aesop

lemma list_drop_eq_get :
    List.drop k.val xs = (xs.get k) :: (List.drop (k.val + 1) xs) := by
  induction xs
  case nil => exfalso; have ⟨k, k_pf⟩ := k; simp_all
  case cons => induction k using Fin.inductionOn <;> simp

-- Analogue of `List.getElem_zero_eq_head` for `List.Vector`.
lemma List.Vector.getElem_zero_eq_head {α : Type} {k : Nat} (l : List.Vector α k.succ) :
    l[0] = l.head := by
  rcases l with ⟨l, h_l⟩
  cases l with
  | nil => simp at h_l
  | cons => rfl

lemma List.Vector.getElem_max_eq_last {α : Type} {k : Nat} (l : List.Vector α k.succ) :
    l[k] = l.last := by
  rcases l with ⟨l, h_l⟩
  cases l with
  | nil => simp at h_l
  | cons => rfl

lemma List.Vector.head_eq_last_of_one {α : Type} (l : List.Vector α 1) :
    l.head = l.last := by
  rcases l with ⟨l, h_l⟩
  cases l with
  | nil => simp at h_l
  | cons => rfl

-- Like `List.Vector.get_tail_succ` but for `getElem`
lemma List.Vector.tail_getElem_eq_getElem_succ {k : Nat} (l : List.Vector α k.succ) (i : Fin k) :
    l.tail[i] = l[i.succ] := by
  rcases l with ⟨l, h_l⟩
  cases l with
  | nil => simp at h_l
  | cons => rfl

lemma List.Vector.tail_last_eq_last {k : Nat} (l : List.Vector α k.succ.succ) :
    l.tail.last = l.last := by
  rcases l with ⟨l, h_l⟩
  cases l with
  | nil => simp at h_l
  | cons => rfl

lemma cast_append_getElem_eq_getElem_of_lt {α : Type}
    (k : ℕ) (l : List.Vector α k)
    (k' : ℕ) (l' : List.Vector α k'.succ)
    (this : k'.succ + k = (k + k').succ)
    i
    (i_low : i < k'.succ)
    : (this ▸ (l' ++ l))[↑i] = l'[↑i] := by
  sorry

lemma cast_append_getElem_eq_getElem_of_ge {α : Type}
    (k : ℕ) (l : List.Vector α k.succ)
    (k' : ℕ) (l' : List.Vector α k'.succ)
    (this : k'.succ + (k.succ - 1) = (k + k').succ)
    i
    (i_high : i ≥ k'.succ)
    (i_in_bound : i < (k + k').succ)
    : (this ▸ (l' ++ l.tail))[i] = l[i - k'] := by
  sorry

/-- Special case of `cast_append_getElem_eq_getElem_of_lt`.
Slightly more general compared to `cast_append_last_eq_last`, this takes `l` instead of `l.tail`. -/
lemma cast_append_head_eq_head {α : Type}
    (k : ℕ) (l : List.Vector α k)
    (k' : ℕ) (l' : List.Vector α k'.succ)
    (this : k'.succ + k = (k + k').succ)
    : (this ▸ (l' ++ l)).head = l'.head := by
  convert cast_append_getElem_eq_getElem_of_lt k l k' l' this 0 (by omega)
  · have := List.Vector.getElem_zero_eq_head (this ▸ (l' ++ l))
    rw [← this]
  · have := List.Vector.getElem_zero_eq_head l'
    rw [← this]

/-- Special case of `cast_append_getElem_eq_getElem_of_ge` -/
lemma cast_append_last_eq_last {α : Type}
    (k : ℕ) (l : List.Vector α k.succ)
    (k' : ℕ) (l' : List.Vector α k'.succ)
    (this : k'.succ + (k.succ - 1) = (k + k').succ)
    : (this ▸ (l' ++ l.tail)).last = l.last := by
  -- have := cast_append_getElem_eq_getElem_of_ge k l k' l' this (k' + k) (by omega) -- hmm
  -- use List.Vector.getElem_max_eq_last here?
  sorry
