import Mathlib.Algebra.Order.BigOperators.Group.List

import Pdl.Measures
import Pdl.Vector

/-! # Fischer-Ladner Closure

Here we define a closure on sets of formulas.
Our main reference for this closure is the proof of Theorem 3.2 in [FL1979].
See also Definition 4.79 and Exercise 4.8.2 in [BRV2001].

- [FL1979] Michael J. Fischer and Richard E. Ladner (1979):
  *Propositional dynamic logic of regular programs*.
	Journal of Computer and System Sciences, vol 18, no 2, pp. 194--211.
	<https://doi.org/10.1016/0022-0000(79)90046-1>

- [BRV2001] Patrick Blackburn, Maarten de Rijke and Yde Venema (2001):
	*Modal Logic*.
	Cambridge University Press.
  <https://www.mlbook.org/>

-/

/-! ## Naive Single-step  -/

def Formula.fischerLadnerStep : Formula → List Formula
| ⊥ => []
| ·_ => []
| φ⋀ψ => [φ, ψ]
| ⌈·_⌉φ => [φ]
| ⌈α;'β⌉φ => [ ⌈α⌉⌈β⌉φ ]
| ⌈α⋓β⌉φ => [ ⌈α⌉φ, ⌈β⌉φ ]
| ⌈∗α⌉φ => [ φ, ⌈α⌉⌈∗α⌉φ ]
| ⌈?'τ⌉φ => [ τ, φ ] -- hmm?
| ~~φ => [~φ]
| ~⊥ => []
| ~(·_) => []
| ~(φ⋀ψ) => [ ~φ, ~ψ ]
| ~⌈·_⌉φ => [ ~φ]
| ~⌈α;'β⌉φ => [ ~⌈α⌉⌈β⌉φ ]
| ~⌈α⋓β⌉φ => [ ~⌈α⌉φ, ~⌈β⌉φ ]
| ~⌈∗α⌉φ => [ ~φ, ~⌈α⌉⌈∗α⌉φ ]
| ~⌈?'τ⌉φ => [ ~τ, ~φ ] -- hmm?

/-! ## PreFormulas

The proof of Theorem 3.2 in [FL1979] uses fresh variables, which would mean we have to
compute those and then work with `repl_in_F` to get the original formula back, etc.
Instead, here we use a new `PreForm` type that allows us to mark the subformula after
a box to not be taken apart further in the recursive step `PreForm.fischerLadnerStep`.
In particular, we define
-/

/-- A (non-)negated sequence of boxes before a formula that should (not) be taken apart. -/
def PreForm : Type := Bool × Option Program × Sum Formula Formula

/-- No negation, empty list of boxes and to still be taken apart. -/
def PreForm.ofFormula (ψ : Formula) : PreForm := ⟨true, none, Sum.inl ψ⟩

-- instance : Coe Formula (PreForm) := ⟨PreForm.ofFormula⟩ -- unused.

def PreForm.toForm : PreForm → Formula
| (b, αs, lrφ) => (if b then id else Formula.neg) $ Formula.boxes αs.toList (lrφ.elim id id)

/-- Converting `Formula` to `PreForm` and back to `Formula` is the identity. Note that the other
direction does not hold, because two different `PreForm`s can encode the same `Formula`. -/
@[simp]
lemma PreForm.toForm_ofFormula_cancel {φ} : (PreForm.ofFormula φ).toForm = φ := by
  simp [ofFormula,toForm]

/-! Length of a `PreForm`. Crucially, this does not count the `.inr` part. -/
@[simp]
def PreForm.length : PreForm → Nat
| (_, α, Sum.inl φ) => (α.map lengthOfProgram).getD 0 + lengthOfFormula φ
| (_, α, Sum.inr _) => (α.map lengthOfProgram).getD 0 -- NOT counting φ here

/-! ## Single Step -/

/-- Inspired by [FL1979] proof of Theorem 3.2. -/
def PreForm.fischerLadnerStep : PreForm → List PreForm
| ⟨_, none, Sum.inl (⊥)⟩ => []
| ⟨_, none, Sum.inl (·_)⟩ => []
| ⟨b, none, Sum.inl (φ⋀ψ)⟩ => [ ⟨b, none, Sum.inl φ⟩, ⟨b, none, Sum.inl ψ⟩ ]
| ⟨true, none, Sum.inl (~φ)⟩ => [ ⟨false, none, Sum.inl φ⟩ ] -- ~φ staying the same
| ⟨false, none, Sum.inl (~φ)⟩ => [ ⟨false, none, Sum.inl φ⟩ ] -- ~~φ to ~φ
| ⟨b, none, Sum.inl (⌈α⌉φ)⟩ => [ ⟨b, α, Sum.inl φ⟩ ] -- [α]φ staying the same
| ⟨_, none, Sum.inr _⟩ => [ ] -- blocked formula generates nothing.
-- Boxes before formulas still to be taken apart:
| ⟨b, ·_, Sum.inl φ⟩ => [ ⟨b, none, Sum.inl φ⟩ ]
| ⟨b, α;'β, Sum.inl φ⟩ => [ ⟨b, α, Sum.inr (⌈β⌉φ)⟩, ⟨b, β, Sum.inl φ⟩ ]
| ⟨b, α⋓β, Sum.inl φ⟩ => [ ⟨b, α, Sum.inr φ⟩, ⟨b, β, Sum.inr φ⟩, ⟨b, none, Sum.inl φ⟩ ]
| ⟨b, ∗α, Sum.inl φ⟩ => [ ⟨b, none, Sum.inl φ⟩, ⟨b, α, Sum.inr (⌈∗α⌉φ)⟩ ]
| ⟨true, ?'τ, Sum.inl φ⟩ => [ ⟨true, none, Sum.inl τ⟩, ⟨true, none, Sum.inl φ⟩ ]
| ⟨false, ?'τ, Sum.inl φ⟩ => [ ⟨false, none, Sum.inl τ⟩, ⟨false, none, Sum.inl φ⟩ ]
-- Boxes before blocked formulas:
| ⟨b, ·_, Sum.inr φ⟩ => [ ⟨b, none, Sum.inr φ⟩ ]
| ⟨b, α;'β, Sum.inr φ⟩ => [ ⟨b, α, Sum.inr (⌈β⌉φ)⟩, ⟨b, β, Sum.inr φ⟩ ]
| ⟨b, α⋓β, Sum.inr φ⟩ => [ ⟨b, α, Sum.inr (φ)⟩, ⟨b, β, Sum.inr (φ)⟩, ⟨b, none, Sum.inr φ⟩ ]
| ⟨b, ∗α, Sum.inr φ⟩ => [ ⟨b, none, Sum.inr φ⟩, ⟨b, α, Sum.inr (⌈∗α⌉φ)⟩ ]
| ⟨true, ?'τ, Sum.inr φ⟩ => [ ⟨true, none, Sum.inr τ⟩, ⟨true, none, Sum.inr φ⟩ ]
| ⟨false, ?'τ, Sum.inr φ⟩ => [ ⟨false, none, Sum.inr τ⟩, ⟨false, none, Sum.inr φ⟩ ]

/-- Unused, weaker than `PreForm.fischerLadnerStep_sum_down`. -/
lemma PreForm.fischerLadnerStep_down {pφ pψ : PreForm} :
    pψ ∈ pφ.fischerLadnerStep → pψ.length < PreForm.length pφ := by
  rcases pφ with ⟨b, _|α, φ|φ⟩
  case none.inl =>
    intro ψ_def
    cases φ <;> cases b <;> simp [PreForm.fischerLadnerStep] at ψ_def
    all_goals
      subst_eqs
      simp_all
    all_goals
      cases ψ_def <;> subst_eqs <;> simp_all; omega
  case none.inr =>
    simp [PreForm.fischerLadnerStep]
  case some.inl =>
    intro ψ_def
    cases α <;> simp [PreForm.fischerLadnerStep] at ψ_def
    case atom_prog a => simp_all
    case sequence => cases ψ_def <;> simp_all; omega
    case union => rcases ψ_def with _|_|_ <;> (subst_eqs; simp <;> try omega)
    case star => cases ψ_def <;> (subst_eqs; simp <;> try omega)
    case test => cases b <;> simp_all <;> cases ψ_def <;> simp_all <;> omega
  case some.inr =>
    intro ψ_def
    cases α <;> simp [PreForm.fischerLadnerStep] at ψ_def
    case atom_prog a => simp_all
    case sequence => cases ψ_def <;> simp_all ; omega
    case union => rcases ψ_def with _|_|_ <;> (subst_eqs; simp <;> omega)
    case star => cases ψ_def <;> (subst_eqs; simp; try omega)
    case test => cases b <;> simp_all <;> cases ψ_def <;> simp_all

/-- With `PreForm.fischerLadnerStep` the (sum of) `PreForm.length` goes down.
Here `h` is needed to exclude the .inr case (where we would claim 0 < 0). -/
lemma PreForm.fischerLadnerStep_sum_down (pφ : PreForm) (h : pφ.2.1.isSome ∨ pφ.2.2.isLeft) :
    ((PreForm.fischerLadnerStep pφ).map PreForm.length).sum < PreForm.length pφ := by
  rcases pφ with ⟨b, _|α, φ|φ⟩
  case none.inl =>
    cases φ <;> cases b <;> simp [PreForm.fischerLadnerStep]
  case none.inr =>
    exfalso
    simp at h
  case some.inl =>
    cases α <;> simp [PreForm.fischerLadnerStep] <;> try omega
    case test => cases b <;> simp_all
  case some.inr =>
    cases α <;> simp [PreForm.fischerLadnerStep]
    case test => cases b <;> simp_all

/-! ## Closure for PreFormulas -/

def PreForm.fischerLadnerClosure (pfs : List PreForm) : List PreForm :=
  pfs ++ pfs.flatMap (fun pφ =>
    if _forTermination : pφ.2.1.isSome ∨ pφ.2.2.isLeft
      then PreForm.fischerLadnerClosure (PreForm.fischerLadnerStep pφ)
      else [])
termination_by
  (pfs.map PreForm.length).sum
decreasing_by
  apply lt_of_lt_of_le (PreForm.fischerLadnerStep_sum_down _ _forTermination)
  apply List.le_sum_of_mem
  simp
  use pφ

lemma PreForm.fischerLadnerClosure_mem_def :
    pφ ∈ PreForm.fischerLadnerClosure pfs
    ↔   pφ ∈ pfs
      ∨ (∃ pf ∈ pfs, (pf.2.1.isSome ∨ pf.2.2.isLeft)
          ∧ pφ ∈ PreForm.fischerLadnerClosure (PreForm.fischerLadnerStep pf)) := by
  constructor
  · intro pφ_in
    unfold PreForm.fischerLadnerClosure at pφ_in
    simp only [dite_eq_ite, List.mem_append, List.mem_flatMap, List.mem_ite_nil_right] at pφ_in
    rcases pφ_in with _|⟨pf,pf_in,bla⟩ <;> aesop
  · intro pφ_in
    unfold PreForm.fischerLadnerClosure
    aesop

lemma PreForm.fischerLadnerClosure_all_noneright_then_id {pfs}
    (h : ∀ pf ∈ pfs, pf.2.1 = none ∧ pf.2.2.isRight) : PreForm.fischerLadnerClosure pfs = pfs := by
  unfold PreForm.fischerLadnerClosure
  simp
  grind

@[simp]
lemma PreForm.fischerLadnerClosure_empty : fischerLadnerClosure [] = [] := by
  unfold PreForm.fischerLadnerClosure
  simp

lemma PreForm.fischerLadnerClosure_self pfs :
    pfs ⊆ PreForm.fischerLadnerClosure pfs := by
  unfold PreForm.fischerLadnerClosure
  simp

lemma PreForm.fischerLadnerClosure_union pfs pgs :
    PreForm.fischerLadnerClosure pfs ++ PreForm.fischerLadnerClosure pgs
    ⊆ PreForm.fischerLadnerClosure (pfs ++ pgs) := by
  unfold PreForm.fischerLadnerClosure
  intro pφ pφ_in
  simp_all
  aesop

lemma PreForm.fischerLadnerClosure_sub pfs pgs :
    pfs ⊆ pgs → PreForm.fischerLadnerClosure pfs ⊆ PreForm.fischerLadnerClosure pgs := by
  unfold PreForm.fischerLadnerClosure
  intro pφ pφ_in
  simp_all
  aesop

lemma PreForm.fischerLadnerStep_stays_right {pf : PreForm}
    (h : pf.2.2.isRight) : ∀ pφ ∈ pf.fischerLadnerStep, pφ.2.2.isRight := by
  intro pφ pφ_in
  unfold fischerLadnerStep at pφ_in
  rcases pf with ⟨b, _|α, φ|φ⟩
  case none.inl => exfalso; aesop
  case some.inl => exfalso; aesop
  · cases φ <;> simp at *
  · cases α <;> aesop

lemma PreForm.fischerLadnerClosure_cons pf pfs {pφ} :
    pφ ∈ PreForm.fischerLadnerClosure (pf :: pfs)
    ↔ pφ = pf
      ∨ ( (pf.2.1.isSome = true ∨ pf.2.2.isLeft = true)
        ∧ pφ ∈ PreForm.fischerLadnerClosure (PreForm.fischerLadnerStep pf))
      ∨ pφ ∈ PreForm.fischerLadnerClosure pfs := by
  constructor
  · intro pφ_in
    unfold fischerLadnerClosure at pφ_in
    simp at pφ_in
    rcases pφ_in with _|pφ_in|_|⟨_,_,_,_⟩
    · simp_all
    · right; right; exact PreForm.fischerLadnerClosure_self pfs pφ_in
    · right; left; aesop
    · right; right; unfold fischerLadnerClosure; aesop
  · rintro (_|_|_) <;> unfold fischerLadnerClosure
    · aesop
    · aesop
    next h => unfold fischerLadnerClosure at h; aesop

-- maybe use  ∃ l, List.Chain pflR pf l ∧ l.last  but "last" is annoying.
-- for Chain: def pflR (pf pg : PreForm) : Prop := pg ∈ PreForm.fischerLadnerStep pf
lemma PreForm.fischerLadnerClosure_mem_iff_chain :
  pφ ∈ PreForm.fischerLadnerClosure pfs ↔
    ∃ k : Nat, ∃ l : List.Vector PreForm k.succ,
        l.head ∈ pfs
      ∧ l.last = pφ
      ∧ ∀ i : Fin k, (l[i].2.1.isSome ∨ l[i].2.2.isLeft) ∧ l[i.succ] ∈ PreForm.fischerLadnerStep l[i] := by
  constructor
  · intro pφ_in
    unfold PreForm.fischerLadnerClosure at pφ_in
    simp only [dite_eq_ite, List.mem_append, List.mem_flatMap, List.mem_ite_nil_right,
      Nat.succ_eq_add_one, Fin.getElem_fin, Fin.val_succ] at *
    rcases pφ_in with pf_in | ⟨qf, qf_in, qf_left, pf_from_qf⟩
    · use 0, ⟨[pφ], by simp⟩
      aesop
    · have IH := @PreForm.fischerLadnerClosure_mem_iff_chain (qf.fischerLadnerStep) pφ
      rw [IH] at pf_from_qf; clear IH
      rcases pf_from_qf with ⟨k, l, l_head_in, def_pφ, steps⟩
      use k + 1, (l.cons qf)
      refine ⟨by aesop, by aesop, ?_⟩
      intro i
      cases i using Fin.cases
      · clear steps
        change _ ∧ l[0] ∈ qf.fischerLadnerStep
        convert And.intro qf_left l_head_in
        apply List.Vector.getElem_zero_eq_head
      · apply steps
  · rintro ⟨k, l, l_head_in, def_pφ, steps⟩
    cases k
    · rw [← def_pφ, ← List.Vector.head_eq_last_of_one l]
      exact PreForm.fischerLadnerClosure_self _ l_head_in
    case succ k =>
      unfold PreForm.fischerLadnerClosure
      simp
      have _forTermination : l.head.2.1.isSome ∨ l.head.2.2.isLeft := by
        convert (steps 0).1 <;> rw [← List.Vector.getElem_zero_eq_head] <;> rfl
      have IH := @PreForm.fischerLadnerClosure_mem_iff_chain (l.head.fischerLadnerStep) pφ
      right
      refine ⟨l.head, by assumption, ?_⟩
      constructor
      · exact _forTermination
      · rw [IH]
        refine ⟨k, l.tail, ?_, ?_, ?_⟩  -- hmm??
        · convert (steps 0).2
          · rw [← List.Vector.getElem_zero_eq_head]; rfl
          · simp
            -- another List.Vector lemma?
            have := @List.Vector.tail_getElem_eq_getElem_succ _ _ l 0
            convert this
            rw [← List.Vector.getElem_zero_eq_head]; rfl
        · rw [List.Vector.tail_last_eq_last]
          exact def_pφ
        · intro i
          convert steps i.succ
          · have := @List.Vector.tail_getElem_eq_getElem_succ _ _ l i.castSucc
            convert this using 1
          · have := @List.Vector.tail_getElem_eq_getElem_succ _ _ l i.castSucc
            convert this using 1
          · have := @List.Vector.tail_getElem_eq_getElem_succ _ _ l i.castSucc
            convert this using 1
          · apply List.Vector.tail_getElem_eq_getElem_succ
termination_by
  (pfs.map PreForm.length).sum
decreasing_by
  · apply lt_of_lt_of_le (PreForm.fischerLadnerStep_sum_down _ (by aesop))
    apply List.le_sum_of_mem
    simp
    use qf
  · apply lt_of_lt_of_le (PreForm.fischerLadnerStep_sum_down _ _forTermination)
    apply List.le_sum_of_mem
    simp
    use l.head

/-- Might be useful for `fLC_idem`. -/
lemma PreForm.fischerLadnerClosure_idem :
    pφ ∈ PreForm.fischerLadnerClosure (PreForm.fischerLadnerClosure pfs)
    ↔ pφ ∈ fischerLadnerClosure pfs := by
  constructor
  · intro pφ_in
    rw [PreForm.fischerLadnerClosure_mem_iff_chain] at pφ_in
    rcases pφ_in with ⟨k, l, l_head_in, def_pφ, steps⟩
    rw [PreForm.fischerLadnerClosure_mem_iff_chain] at l_head_in
    rcases l_head_in with ⟨k', l', l'_head_in, def_l_head, steps'⟩
    rw [PreForm.fischerLadnerClosure_mem_iff_chain]
    -- FIXME maybe the rest here should be a separate (more general) lemma about lists/chains.
    -- Now we need to concatenate the two vectors and their properties.
    -- Note that we have l'.last = l.head (and not have an ∈ FL stel there)
    -- so we only use l.tail instead of l.
    use (k + k') -- yes!
    have : (k'.succ + (k.succ - 1)) = (k + k').succ := by omega
    refine ⟨this ▸ (l' ++ l.tail), ?_, ?_, ?_⟩
    · convert l'_head_in using 1
      apply cast_append_head_eq_head
    · convert def_pφ using 1
      apply cast_append_last_eq_last
    · intro i
      -- IDEA: case split whether i ≤ k.succ or so, then use steps or steps'.
      by_cases i_low : i.val < k'
      · specialize steps' ⟨i.val, i_low⟩
        simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Fin.val_succ, Fin.succ_mk] at *
        convert steps' <;> apply cast_append_getElem_eq_getElem_of_lt
      · simp at i_low
        by_cases i_eq_k' : i = k' -- We treat the special case i = k' separately.
        · -- Here use the that newlist[k'] = l'.last = l.head has a `steps` to l[1].
          -- Also note that the last element of l' isLeft because it is the first of l.
          simp
          specialize steps ⟨0, by omega⟩
          convert steps
          · have := @cast_append_getElem_eq_getElem_of_lt _ k l.tail k' l' (by omega) i.val (by omega)
            convert this
            convert def_l_head.symm
            · apply List.Vector.getElem_zero_eq_head
            · simp_all [List.Vector.getElem_max_eq_last]
          · have := @cast_append_getElem_eq_getElem_of_lt _ k l.tail k' l' (by omega) i.val (by omega)
            convert this
            convert def_l_head.symm
            · apply List.Vector.getElem_zero_eq_head
            · simp_all [List.Vector.getElem_max_eq_last]
          · have := @cast_append_getElem_eq_getElem_of_lt _ k l.tail k' l' (by omega) i.val (by omega)
            convert this
            convert def_l_head.symm
            · apply List.Vector.getElem_zero_eq_head
            · simp_all [List.Vector.getElem_max_eq_last]
          · rcases i with ⟨i,i_lt⟩
            have := @cast_append_getElem_eq_getElem_of_ge _ _ l _ l' this (k' + 1) (by simp) (by omega)
            simp at this
            convert this
        · specialize steps ⟨i - k', by omega⟩
          simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Fin.val_succ, Fin.succ_mk,
            Nat.add_one_sub_one] at *
          convert steps
          · apply cast_append_getElem_eq_getElem_of_ge; omega
          · apply cast_append_getElem_eq_getElem_of_ge; omega
          · apply cast_append_getElem_eq_getElem_of_ge; omega
          · have := @cast_append_getElem_eq_getElem_of_ge _ _ l _ l' this i.succ
              (by simp at *; omega) (by omega)
            convert this using 2
            simp
            omega
  · apply PreForm.fischerLadnerClosure_self

-- other idea: induction principle
-- to prove h for all elements of flC(fs)
-- base: prove h for fs
-- step: assuming h for pf, prove h for all elements of flStep(pf)
-- ????


/-! ## Closure for normal Formulas -/

/-- The Fischer-Ladner closure. Computed via `PreForm.fischerLadnerClosure`. -/
def fischerLadnerClosure (fs : List Formula) : List Formula :=
  (PreForm.fischerLadnerClosure (fs.map PreForm.ofFormula)).map PreForm.toForm

-- Examples. Is the duplication annoying? (Comes from "staying the same" cases above.)
--
-- #eval fischerLadnerClosure [⌈(∗(·1))⌉ ·9]
-- #eval fischerLadnerClosure [⌈(∗(·1 ⋓ ·2))⌉ ·9] -- was wrong with older fLC def
-- #eval List.dedup $ fischerLadnerClosure [⌈(∗(·1 ⋓ ·2))⌉ ·9]

-- TODO how to say that it contains any number of steps?
lemma fLC_contains_step (φ : Formula) :
    φ.fischerLadnerStep ⊆ fischerLadnerClosure [φ] := by
  cases φ <;> simp [Formula.fischerLadnerStep]
  case neg φ =>
    cases φ <;> try simp
    case neg φ =>
      simp [fischerLadnerClosure,PreForm.ofFormula]
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      simp [PreForm.toForm, PreForm.fischerLadnerStep]
    case and φ1 φ2 =>
      simp [fischerLadnerClosure,PreForm.ofFormula]
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      simp [PreForm.toForm, PreForm.fischerLadnerStep]
    case box α φ =>
      cases α
      all_goals
        simp [fischerLadnerClosure,PreForm.ofFormula]
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.toForm, PreForm.fischerLadnerStep]
      case atom_prog a =>
        unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]
      case sequence α β =>
        right
        · unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          simp [PreForm.fischerLadnerStep]
      all_goals -- union, star and test
        constructor <;> right
        · unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          simp [PreForm.fischerLadnerStep]
        · unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          simp [PreForm.fischerLadnerStep]
  case and φ1 φ2 =>
    simp [fischerLadnerClosure,PreForm.ofFormula]
    unfold PreForm.fischerLadnerClosure
    simp [PreForm.toForm, PreForm.fischerLadnerStep]
    unfold PreForm.fischerLadnerClosure
    simp [PreForm.fischerLadnerStep]
  case box α φ =>
    cases α
    all_goals
      simp [fischerLadnerClosure,PreForm.ofFormula]
      unfold PreForm.fischerLadnerClosure
      simp [PreForm.toForm, PreForm.fischerLadnerStep]
    case atom_prog a =>
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure -- twice, but not inf. often!
      simp [PreForm.fischerLadnerStep]
    case sequence α β =>
      right
      · unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]
    all_goals -- union, star and test
      constructor <;> right
      · unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]
      · unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]

/-- The `fischerLadnerClosure` still contains the given formulas. -/
lemma fLC_self (fs : List Formula) :
    fs ⊆ fischerLadnerClosure fs := by
  have := PreForm.fischerLadnerClosure_self (fs.map PreForm.ofFormula)
  unfold fischerLadnerClosure
  intro φ φ_in
  aesop

lemma fLC_union (fs gs : List Formula) :
    fischerLadnerClosure fs ++ fischerLadnerClosure gs ⊆ fischerLadnerClosure (fs ++ gs) := by
  intro φ
  unfold fischerLadnerClosure
  have := PreForm.fischerLadnerClosure_union (fs.map PreForm.ofFormula) (gs.map PreForm.ofFormula)
  aesop

lemma fLC_sub (fs gs : List Formula) :
    fs ⊆ gs → fischerLadnerClosure fs ⊆ fischerLadnerClosure gs := by
  intro fs_sub_gs φ φ_in
  unfold fischerLadnerClosure at *
  have := @PreForm.fischerLadnerClosure_sub (fs.map PreForm.ofFormula) (gs.map PreForm.ofFormula)
    (by intro φ; aesop)
  aesop

/-- This probably does not hold in general. -/
lemma speculation :
    PreForm.fischerLadnerClosure
      (List.map (PreForm.ofFormula ∘ PreForm.toForm)
        (PreForm.fischerLadnerClosure (List.map PreForm.ofFormula fs)))
    ⊆ PreForm.fischerLadnerClosure (List.map PreForm.ofFormula fs) := by
  intro pf pf_in
  induction fs
  · simp_all
  case cons f fs IH =>
    simp [List.map_cons] at *
    rw [PreForm.fischerLadnerClosure_mem_def] at pf_in
    simp at pf_in
    rcases pf_in with ⟨pφ, pφ_in, def_pf⟩|⟨pφ, pφ_in, _, pf_in⟩
    · subst def_pf
      rw [PreForm.fischerLadnerClosure_cons]
      rw [PreForm.fischerLadnerClosure_cons] at pφ_in
      rcases pφ_in with _|⟨_,pφ_in⟩ |_
      · left; simp_all
      · -- coming from f
        clear IH -- probably useless here?
        right
        left
        simp_all
        -- pφ is in it, but its to-normal-to-pre variant might not be?
        -- NOTE: the whole lemma here might be wrong!
        unfold PreForm.ofFormula at *
        rw [PreForm.fischerLadnerClosure_mem_def] at pφ_in
        sorry
      case inr h =>
        -- coming from fs
        right
        right
        -- use IH here (which assumes we already solved the issue??)
        apply IH
        clear IH
        -- unsure here
        rw [← PreForm.fischerLadnerClosure_idem] at h
        sorry
    · sorry

/-- The `fischerLadnerClosure` is idempotent / transitive. -/
lemma fLC_idem (fs : List Formula) φ :
    φ ∈ fischerLadnerClosure (fischerLadnerClosure fs) ↔ φ ∈ fischerLadnerClosure fs := by
  unfold fischerLadnerClosure
  constructor
  · intro φ_in
    simp at *
    rcases φ_in with ⟨pf, pf_in, pf_is_φ⟩
    -- exact ⟨pf, speculation pf_in, pf_is_φ⟩ -- but UNSURE about that lemma!!
    -- use pf -- NO, might not have the same witness / do not know this yet?

    unfold PreForm.fischerLadnerClosure at pf_in
    simp at *
    rcases pf_in with ⟨qf, qf_in, def_pf⟩ | ⟨qf, qf_in, qf_inl, pf_in⟩
    · subst def_pf
      use qf -- yes!?!?
      aesop
    ·

      use pf -- not sure
      constructor
      · unfold PreForm.fischerLadnerClosure
        simp
        right -- hmm?
        unfold PreForm.fischerLadnerClosure at qf_in
        simp at qf_in
        -- STUCK, would `PreForm.fischerLadnerClosure_idem` be useful here?
        sorry
      · assumption
  · apply fLC_self

/-- The `fischerLadnerClosure` is idempotent / transitive. -/
lemma fLC_idem' (fs : List Formula) φ :
    φ ∈ fischerLadnerClosure (fischerLadnerClosure fs) ↔ φ ∈ fischerLadnerClosure fs := by
  induction fs
  · unfold fischerLadnerClosure
    simp
  case cons f fs IH =>

  unfold fischerLadnerClosure at *

  constructor
  · intro φ_in
    simp at *
    rcases φ_in with ⟨pf, pf_in, pf_is_φ⟩

    -- refine ⟨pf, ?_, pf_is_φ⟩ -- UNSURE from here!
    --exact speculation pf_in
    -- use pf -- NO, might not have the same witness / not know this yet.
    unfold PreForm.fischerLadnerClosure at pf_in
    simp at *
    rcases pf_in with ⟨qf, qf_in, def_pf⟩ | ⟨qf, qf_in, qf_inl, pf_in⟩
    · subst def_pf
      use qf -- yes!?!?
      aesop
    · use pf -- not sure
      constructor
      · unfold PreForm.fischerLadnerClosure
        simp
        right -- hmm?
        unfold PreForm.fischerLadnerClosure at qf_in
        simp at qf_in
        -- STUCK, would `PreForm.fischerLadnerClosure_idem` be useful here?
        sorry
      · assumption
  · apply fLC_self

lemma fLC_closed_under_step {fs : List Formula} (φ ψ : Formula)
    (φ_in : φ ∈ fischerLadnerClosure fs)
    (ψ_in : ψ ∈ φ.fischerLadnerStep) :
    ψ ∈ fischerLadnerClosure fs := by
  rw [← fLC_idem]
  exact fLC_sub [φ] (fischerLadnerClosure fs) (by aesop) (fLC_contains_step φ ψ_in)
