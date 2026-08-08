import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Multiset.DershowitzManna

import Pdl.LocalRules

/-! # Local Tableaux (Section 3) -/

/-- Local tableau for `X`, maximal by definition. -/
inductive LocalTableau : (X : Sequent) → Type
  | byLocalRule {X} (lra : LocalRuleApp) (X_def : X = lra.X)
      (next : ∀ Y ∈ lra.C, LocalTableau Y) : LocalTableau X
  | sim {X} : X.basic → LocalTableau X

instance LocalTableau.instDecidableEq {lt1 lt2 : LocalTableau X} : Decidable (lt1 = lt2) := by
  rcases lt1 with (⟨lra1, X_def1, next1⟩|Xbas1)
  all_goals
    rcases lt2 with (⟨lra2, X_def2, next2⟩|Xbas2)
  · by_cases lra1.C = lra2.C
    · subst_eqs
      simp_all
      by_cases lra1 = lra2
      · subst_eqs
        simp only [true_and]
        have := fun (X : Sequent) (X_in : X ∈ _) =>
          @LocalTableau.instDecidableEq _ (next1 X X_in) (next2 X X_in)
        by_cases ∃ Z ∈ lra1.C, ∀ h, next1 Z h ≠ next2 Z h
        · apply isFalse
          aesop
        · apply isTrue
          aesop
      · apply isFalse
        aesop
    · apply isFalse
      aesop
  all_goals
    try simp_all
    try exact instDecidableFalse
    try exact instDecidableTrue

/-! ## Termination of LocalTableau -/

theorem testsOfProgram_sizeOf_lt α : ∀ τ ∈ testsOfProgram α, sizeOf τ < sizeOf α := by
  intro τ τ_in
  cases α
  all_goals
    simp [testsOfProgram] at *
  case sequence α β =>
    rcases τ_in with τ_in | τ_in
    · have := testsOfProgram_sizeOf_lt α _ τ_in; linarith
    · have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case union α β =>
    rcases τ_in with τ_in | τ_in
    · have := testsOfProgram_sizeOf_lt α _ τ_in; linarith
    · have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case star β =>
    have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case test τ =>
    subst_eqs
    linarith

open LocalTableau

/-- The local measure we use together with D-M to show that LocalTableau are finite.
Note that different from the paper here we also add `lmOfFormula (~φ)` in the `~⌈α⌉φ` case.
This is needed to get `lmOfFormula_lt_dia_of_nonAtom`. -/
@[simp]
def lmOfFormula : (f : Formula) → Nat
| ⊥ => 0
| ~⊥ => 0
| ·_ => 0
| ~·_ => 0
| ~~φ => 1 + lmOfFormula φ
| φ⋀ψ => 1 + lmOfFormula φ + lmOfFormula ψ
| ~(φ⋀ψ) => 1 + lmOfFormula (~φ) + lmOfFormula (~ψ)
| ⌈·_⌉ _ => 0 -- No more local steps
| ~⌈·_⌉ _ => 0 -- No more local steps
| ⌈α⌉φ => 1 + lmOfFormula φ -- unfoldBox
            + ((testsOfProgram α).attach.map (fun τ => lmOfFormula (~τ.1))).sum
| ~⌈α⌉φ => 1 + lmOfFormula (~φ)
             + ((testsOfProgram α).attach.map (fun τ => lmOfFormula τ.1)).sum
decreasing_by
  all_goals simp_wf
  all_goals try linarith
  all_goals
    have := testsOfProgram_sizeOf_lt _ _ τ.2
    linarith

theorem lmOfFormula_lt_box_of_nonAtom (h : ¬ α.isAtomic) :
    lmOfFormula φ < lmOfFormula (⌈α⌉φ) := by
  cases α <;> simp_all [Program.isAtomic, testsOfProgram] <;> linarith

theorem lmOfFormula_lt_dia_of_nonAtom (h : ¬ α.isAtomic) :
    lmOfFormula (~φ) < lmOfFormula (~⌈α⌉φ) := by
  cases α <;> simp_all [Program.isAtomic, testsOfProgram] <;> linarith

-- Only need this here, so don't export this.
@[simp]
private instance instLTFormula : LT Formula := ⟨fun φ1 φ2 => lmOfFormula φ1 < lmOfFormula φ2⟩

instance Formula.WellFoundedLT : WellFoundedLT Formula := by
  constructor
  simp_all only [instLTFormula]
  exact @WellFounded.onFun Formula Nat Nat.lt lmOfFormula Nat.lt_wfRel.wf

instance Formula.instPreorderFormula : Preorder Formula := Preorder.lift lmOfFormula

@[simp]
def node_to_multiset : Sequent → Multiset Formula
| (L, R, none) => (L + R)
| (L, R, some (Sum.inl (~'χ))) => (L + R + [~χ.unload])
| (L, R, some (Sum.inr (~'χ))) => (L + R + [~χ.unload])

def Olf.toForm : Olf → Multiset Formula
| none => {}
| some (Sum.inl (~'χ)) => {~χ.unload}
| some (Sum.inr (~'χ)) => {~χ.unload}

theorem node_to_multiset_eq {L R O} :
    node_to_multiset (L, R, O) = Multiset.ofList L + Multiset.ofList R + O.toForm := by
  cases O
  · simp [node_to_multiset, Olf.toForm]
  case some nlf =>
    cases nlf
    · simp [node_to_multiset, Olf.toForm]
    · simp [node_to_multiset, Olf.toForm]

/-- If each three parts are the same then node_to_multiset is the same. -/
theorem node_to_multiset_eq_of_three_eq (hL : L = L') (hR : R = R') (hO : O = O') :
    node_to_multiset (L, R, O) = node_to_multiset (L', R', O') := by
  aesop

-- mathlib this?
lemma List.Subperm.append {α : Type u_1} {l₁ l₂ r₁ r₂ : List α} :
    l₁.Subperm l₂ → r₁.Subperm r₂ → (l₁ ++ r₁).Subperm (l₂ ++ r₂) := by
  intro hl hr
  cases l₁
  case nil =>
    simp
    apply List.Subperm.trans hr
    induction l₂
    · simp
      exact Subperm.refl r₂
    case cons IH =>
      simp_all
      apply List.Subperm.cons_right
      exact IH
  case cons h t =>
    have : (h :: t ++ r₁).Subperm (l₂ ++ r₁) := by
      rw [List.subperm_append_right]
      exact hl
    apply List.Subperm.trans this
    rw [List.subperm_append_left]
    exact hr

theorem preconP_to_submultiset {Lcond L Rcond R Ocond O}
    (preconditionProof : List.Subperm Lcond L ∧ List.Subperm Rcond R ∧ Ocond ⊆ O)
    : node_to_multiset (Lcond, Rcond, Ocond) ≤ node_to_multiset (L, R, O) :=
  by
  cases Ocond <;> cases O
  all_goals (try (rename_i f g; cases f; cases g))
  all_goals (try (rename_i f; cases f))
  all_goals
    simp [node_to_multiset] at * -- FIXME avoid non-terminal simp here!
  case none.none =>
    exact (List.Subperm.append preconditionProof.1 preconditionProof.2)
  case none.some.inl =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2) f
    simp_all
    linarith
  case none.some.inr =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2) f
    simp_all
    linarith
  case some.some.inl.inl.neg =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2.1) f
    simp_all
  case some.some.inr.neg a =>
    rw [Multiset.le_iff_count]
    intro f
    have := List.Subperm.count_le (List.Subperm.append preconditionProof.1 preconditionProof.2.1) f
    cases g <;> (rename_i nlform; cases nlform; simp_all)

theorem Multiset.sub_of_le {α} [DecidableEq α] {M N X Y : Multiset α} (h : N ≤ M) :
    M - N + Y = X ↔ M + Y = X + N := by
  constructor
  all_goals
    intro hyp
    ext φ
    rw [@Multiset.ext] at hyp
    specialize hyp φ
    rw [@le_iff_count] at h
    specialize h φ
    simp only [count_add, count_sub] at *
    omega

theorem Multiset_diff_append_of_le [DecidableEq α] {R Rcond Rnew : List α} :
    Multiset.ofList (R.diff Rcond ++ Rnew)
    = Multiset.ofList R - Multiset.ofList Rcond + Multiset.ofList Rnew := by
  rw [@Multiset.coe_sub]
  rw [Multiset.coe_add]

theorem List.Perm_diff_append_of_Subperm {α} [DecidableEq α] {L M : List α} (h : M.Subperm L) :
    L.Perm (L.diff M ++ M) := by
  rw [perm_iff_count]
  intro φ
  rw [← Multiset.coe_count, ← Multiset.coe_count]
  rw [@Multiset_diff_append_of_le α _ L M M]
  rw [tsub_add_cancel_of_le h]

theorem List.count_eq_diff_of_subperm [DecidableEq α] {L M : List α} (h : M.Subperm L) φ :
    List.count φ L = List.count φ (L.diff M) + List.count φ M := by
  suffices L.Perm (L.diff M ++ M) by
    rw [← count_append]
    have := @List.perm_iff_count _ _ _ L (L.diff M ++ M)
    tauto
  apply List.Perm_diff_append_of_Subperm h

/-- Applying `node_to_multiset` before or after `applyLocalRule` gives the same. -/
theorem node_to_multiset_of_precon {O Ocond Onew : Olf}
    (precon : Lcond.Subperm L ∧ Rcond.Subperm R ∧ Ocond ⊆ O)
    (O_extracon : O ≠ none → Ocond = none → Onew = none)
    :   node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond)
        + node_to_multiset (Lnew, Rnew, Onew)
      = node_to_multiset (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, Olf.change O Ocond Onew) := by
  have my_le := preconP_to_submultiset precon
  rw [Multiset.sub_of_le my_le]
  clear my_le
  simp only [node_to_multiset_eq]
  rw [Multiset_diff_append_of_le]
  rw [Multiset_diff_append_of_le]
  have claim : ↑L - ↑Lcond + ↑Lnew + (↑R - ↑Rcond + ↑Rnew)
                                  + (O.change Ocond Onew).toForm + (↑Lcond + ↑Rcond + Ocond.toForm)
      = ↑L + ↑Lnew + (↑R + ↑Rnew) + (O.change Ocond Onew).toForm + (Ocond.toForm) := by
    rw [← add_assoc]
    apply add_right_cancel_iff.mpr
    rw [add_add_add_comm]
    rw [← add_assoc]
    rw [add_right_comm]
    rw [@add_right_cancel_iff]
    ext φ
    simp only [Multiset.coe_sub, Multiset.coe_add, List.append_assoc, Multiset.coe_count,
      List.count_append]
    have := List.count_eq_diff_of_subperm precon.2.1 φ
    have := List.count_eq_diff_of_subperm precon.1 φ
    linarith
  rw [claim]
  clear claim
  ext φ
  simp
  suffices Multiset.count φ O.toForm + (Multiset.count φ Onew.toForm) =
      Multiset.count φ (O.change Ocond Onew).toForm + Multiset.count φ Ocond.toForm by
    linarith
  unfold Olf.change
  have claim : (Olf.toForm (Option.overwrite (O \ Ocond) Onew))
               = O.toForm - Ocond.toForm + Onew.toForm := by
    all_goals cases O_Def : O <;> try (cases O_def2 : O)
    all_goals cases Ocond_Def : Ocond <;> try (cases Ocond_def2 : Ocond)
    all_goals cases Onew_Def : Onew <;> try (cases Onew_def2 : Onew)
    all_goals simp_all [Olf.toForm, Option.insHasSdiff]
  rw [claim]
  -- we now get 3 * 3 * 3 = 27 cases
  all_goals cases O <;> try (rename_i O; cases O)
  all_goals cases Onew <;> try (rename_i Onew; cases Onew)
  all_goals cases Ocond <;> try (rename_i cond; cases cond)
  all_goals simp_all [Olf.toForm] -- solve 23 out of 27 cases, of which 4 use O_extracon
  all_goals
    linarith

@[simp]
def lt_Sequent (X : Sequent) (Y : Sequent) :=
  Multiset.IsDershowitzMannaLT (node_to_multiset X) (node_to_multiset Y)

-- Needed for termination of endNOdesOf.
-- Here we use `dm_wf` from MultisetOrder.lean.
instance : WellFoundedRelation Sequent where
  rel := lt_Sequent
  wf := InvImage.wf node_to_multiset (Multiset.wellFounded_isDershowitzMannaLT)

theorem LocalRule.cond_non_empty (rule : LocalRule (Lcond, Rcond, Ocond) X) :
    node_to_multiset (Lcond, Rcond, Ocond) ≠ ∅ :=
  by
  cases rule
  all_goals simp [node_to_multiset]
  case oneSidedL _ orule X_def => cases orule <;> simp
  case oneSidedR _ orule X_def => cases orule <;> simp

theorem Multiset.sub_add_of_subset_eq [DecidableEq α] {M : Multiset α} (h : X ≤ M) :
    M = M - X + X := (tsub_add_cancel_of_le h).symm

theorem unfoldBox.decreases_lmOf_nonAtomic {α : Program} {φ : Formula} {X : List Formula}
    (α_non_atomic : ¬ α.isAtomic)
    (X_in : X ∈ unfoldBox α φ)
    (ψ_in_X : ψ ∈ X)
    : lmOfFormula ψ < lmOfFormula (⌈α⌉φ) := by
  have ubc := unfoldBoxContent (α) φ X X_in ψ ψ_in_X
  cases α <;> simp [Program.isAtomic] at *
  case sequence α β =>
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (α;'β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (α;'β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      apply List.le_sum_of_mem
      simp only [List.mem_map]
      use τ
    · subst def_ψ
      simp [lmOfFormula]
  case union α β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (α⋓β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (α⋓β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]
  case star β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (∗β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (∗β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]
  case test τ0 => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (?'τ0)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (?'τ0)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]

theorem lmOfFormula.le_union_left α β φ : lmOfFormula (~⌈α⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) := by
  cases α <;> simp [lmOfFormula]
  all_goals
    simp [testsOfProgram]

theorem lmOfFormula.le_union_right α β φ : lmOfFormula (~⌈β⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) := by
  cases β <;> simp [lmOfFormula]
  all_goals
    simp [testsOfProgram]

theorem Dset_goes_down (α : Program) φ {Fs δ} (in_H : (Fs, δ) ∈ Dset α) {ψ} (in_Fs : ψ ∈ Fs) :
    lmOfFormula ψ < lmOfFormula (~⌈α⌉φ) := by
  cases α
  · simp_all [Dset]
  case sequence α β =>
    simp only [lmOfFormula]
    simp only [Dset, List.mem_flatten, List.mem_map, Prod.exists] at in_H
    rcases in_H with ⟨l, ⟨Fs', δ', in_H, def_l⟩, in_l⟩
    · subst def_l
      by_cases δ' = []
      · subst_eqs
        simp_all only [List.nil_append, ite_true, List.mem_flatten, List.mem_map, Prod.exists]
        rcases in_l with ⟨l, ⟨Fs'', δ'', in_Hβ, def_l⟩, in_l⟩
        subst def_l
        simp only [List.mem_singleton, Prod.mk.injEq] at in_l
        cases in_l
        subst_eqs
        simp_all only [List.mem_union_iff]
        rcases in_Fs with in_Fs'|in_Fs''
        · have IHα := Dset_goes_down α φ in_H in_Fs'
          cases α
          all_goals
            simp [lmOfFormula] at IHα
          all_goals
            simp only [List.attach_map_val, testsOfProgram] at *
            simp_all
            try linarith
        · have IHβ := Dset_goes_down β φ in_Hβ in_Fs''
          cases β
          all_goals
            simp_all [Dset, testsOfProgram, lmOfFormula]
            try linarith
      · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq, testsOfProgram,
        List.attach_append, List.map_append, List.map_map, List.sum_append]
        rw [Function.comp_def, Function.comp_def, List.attach_map_val, List.attach_map_val]
        cases in_l
        subst_eqs
        have IHα := Dset_goes_down α φ in_H in_Fs
        cases α
        all_goals
          simp_all [Dset, testsOfProgram, lmOfFormula]
        all_goals
          try rw [Function.comp_def, Function.comp_def, List.attach_map_val,
            List.attach_map_val] at IHα
          try linarith
  case union α β =>
    simp only [Dset, List.mem_union_iff] at in_H
    rcases in_H with hyp|hyp
    · have IHα := Dset_goes_down α φ hyp in_Fs
      suffices lmOfFormula (~⌈α⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) by linarith
      apply lmOfFormula.le_union_left
    · have IHβ := Dset_goes_down β φ hyp in_Fs
      suffices lmOfFormula (~⌈β⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) by linarith
      apply lmOfFormula.le_union_right
  case star α =>
    simp only [lmOfFormula]
    simp [Dset] at in_H
    rcases in_H with _ | ⟨δ', in_H', in_l⟩
    · simp_all only [List.not_mem_nil]
    · by_cases δ' = []
      · simp_all
      · simp only [testsOfProgram]
        cases in_l
        subst_eqs
        have IHα := Dset_goes_down α φ in_H' in_Fs
        cases α <;> simp_all only [lmOfFormula, not_lt_zero']
  case test τ =>
    simp_all [Dset, testsOfProgram]

theorem unfoldDiamond.decreases_lmOf_nonAtomic {α : Program} {φ : Formula} {X : List Formula}
    (α_non_atomic : ¬ α.isAtomic)
    (X_in : X ∈ unfoldDiamond α φ)
    (ψ_in_X : ψ ∈ X)
    : lmOfFormula ψ < lmOfFormula (~⌈α⌉φ) := by
  have udc := unfoldDiamondContent _ _ _ X_in _ ψ_in_X
  rcases udc with ψ_def | ⟨τ, τ_in, ψ_def⟩ | ⟨a, δ, ψ_def⟩ <;> subst ψ_def
  · exact lmOfFormula_lt_dia_of_nonAtom α_non_atomic
  · cases α <;> simp_all [Program.isAtomic, testsOfProgram]
    case sequence α β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (α;'β))).sum.succ by
        simp_all [testsOfProgram]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (α;'β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ_iff]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
    case union α β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (α⋓β))).sum.succ by
        simp_all [testsOfProgram]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (α;'β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ_iff]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
    case star β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (∗β))).sum.succ by
        simp_all [testsOfProgram]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (∗β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ_iff]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
  · simp only [lmOfFormula, gt_iff_lt]
    cases α <;> simp_all [Program.isAtomic]

/-- This is a helper for `measureProp` parts (d) and (e).
If each element of a list `X` is either `a`, belongs to a list `bs`, or has `f` value 0,
then the sum of `f` over `X.toFinset` is at most `f a + (bs.map f).sum`. -/
lemma finset_sum_trichotomy {A : Type*} [DecidableEq A]
    (f : A → ℕ) (X : List A) (a : A) (bs : List A)
    (h : ∀ x ∈ X, x = a ∨ x ∈ bs ∨ f x = 0) :
    ∑ x ∈ X.toFinset, f x ≤ f a + (bs.map f).sum := by
  have h_sum_split : (∑ x ∈ X.toFinset, f x) ≤ (∑ x ∈ (X.toFinset.erase a), f x) + f a := by
    by_cases ha : a ∈ X.toFinset <;> simp_all +decide
    rw [← Finset.sum_erase_add _ _ (by aesop : a ∈ X.toFinset), add_comm]
  have h_sum_le : (∑ x ∈ X.toFinset.erase a, f x) ≤ (∑ x ∈ (bs.toFinset), f x) := by
    have h_sum_le' : (∑ x ∈ X.toFinset.erase a, f x) ≤
        (∑ x ∈ (X.toFinset.erase a ∩ bs.toFinset), f x) := by
      rw [← Finset.sum_subset (Finset.inter_subset_left)]
      intro x hx hx'; specialize h x; aesop
    exact h_sum_le'.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.inter_subset_right) (fun _ _ _ => Nat.zero_le _))
  apply le_trans h_sum_split
  rw [add_comm]
  refine Nat.add_le_add_left (le_trans h_sum_le ?_) _
  have h_toFinset_le : ∀ (l : List A), (∑ x ∈ l.toFinset, f x) ≤ (l.map f).sum := by
    intro l; induction l <;> simp_all +decide
    by_cases hh : ‹A› ∈ ‹List A›.toFinset <;> simp_all +decide; linarith!
  exact h_toFinset_le bs

/-- This is a summary lemma and not used as a whole anywhere.
Note that parts (d) and (e) are about the measure sum over `X` and not single formulas, so
for example (e) is not the same as `unfoldDiamond.decreases_lmOf_nonAtomic`.
Also note that we use `List.toFinset` here to ignore duplicates in the list `X`. -/
lemma measureProp {α : Program} {φ φ₁ φ₂ : Formula} :
      (lmOfFormula φ < lmOfFormula (~~φ)) -- a
    ∧ (lmOfFormula φ₁ + lmOfFormula φ₂ < lmOfFormula (φ₁ ⋀ φ₂)) -- b
    ∧ (lmOfFormula (~φ₁) < lmOfFormula (~(φ₁ ⋀ φ₂))) -- c i=1
    ∧ (lmOfFormula (~φ₂) < lmOfFormula (~(φ₁ ⋀ φ₂))) -- c i=2
    ∧ (¬ α.isAtomic → ∀ X ∈ unfoldBox α φ,
        ∑ ψ ∈ X.toFinset, lmOfFormula ψ < lmOfFormula (⌈α⌉φ)) -- d
    ∧ (¬ α.isAtomic → ∀ X ∈ unfoldDiamond α φ,
        ∑ ψ ∈ X.toFinset, lmOfFormula ψ < lmOfFormula (~⌈α⌉φ)) -- e
    := by
  refine ⟨?a, ?b, ?c1, ?c2, ?d, ?e⟩
  case a => simp
  case b => simp
  case c1 => simp; linarith
  case c2 => simp
  case d =>
    intro α_non_atomic X X_in
    cases α_def : α
    case atom_prog => exfalso; simp_all [Program.isAtomic]
    case test τ =>
      subst α_def
      simp_all [testsOfProgram, unfoldBox, allTP, Bset, F, P]
      cases h : X_in <;> subst h <;> simp_all [Finset.sum]; linarith
    all_goals
      simp only [lmOfFormula, List.map_subtype, List.unattach_attach]
      have tri : ∀ ψ ∈ X, ψ = φ ∨ ψ ∈ (testsOfProgram α).map (~·) ∨ lmOfFormula ψ = 0 := by
        have ubc := unfoldBoxContent _ φ X X_in
        intro ψ ψ_in; rcases ubc ψ ψ_in with rfl | ⟨τ, τ_in, rfl⟩ | ⟨a, δ, rfl, _⟩
        · left; rfl
        · right; left; exact List.mem_map_of_mem τ_in
        · right; right; simp [lmOfFormula]
      have := finset_sum_trichotomy lmOfFormula X φ ((testsOfProgram α).map (~·)) tri
      subst α_def
      simp only [List.mem_map, List.map_map, Function.comp_def, gt_iff_lt] at *
      linarith
  case e =>
    intro α_non_atomic X X_in
    have := @lmOfFormula_lt_dia_of_nonAtom φ _ α_non_atomic
    cases α_def : α
    case atom_prog =>
      simp_all [Program.isAtomic]
    case test τ =>
      simp_all [testsOfProgram, unfoldDiamond, Dset, Yset]
      subst X_in
      by_cases h : τ = ~φ <;> simp_all; grind
    all_goals
      have tri : ∀ ψ ∈ X, ψ = (~φ) ∨ ψ ∈ testsOfProgram α ∨ lmOfFormula ψ = 0 := by
        have udc := unfoldDiamondContent _ _ _ X_in
        intro ψ ψ_in
        rcases udc ψ ψ_in with rfl | ⟨τ, τ_in, rfl⟩ | ⟨a, δ, rfl⟩
        · left; rfl
        · right; left; exact τ_in
        · right; right; simp [lmOfFormula]
      have := finset_sum_trichotomy lmOfFormula X (~φ) (testsOfProgram α) tri
      subst α_def
      simp only [lmOfFormula, List.map_subtype, List.unattach_attach, gt_iff_lt] at *
      linarith

theorem LocalRuleDecreases (rule : LocalRule X ress) :
    ∀ Y ∈ ress, ∀ y ∈ node_to_multiset Y, ∃ x ∈ node_to_multiset X, y < x :=
  by
    intro Y Y_in_ress y y_in_Y
    cases rule
    case LRnegL => simp at *
    case LRnegR => simp at *
    case oneSidedL orule ress_def =>
      subst ress_def
      cases orule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case neg => linarith
      case con => cases y_in_Y <;> (subst_eqs; linarith)
      case nCo => cases Y_in_ress <;> (subst_eqs; simp at * ; subst_eqs; linarith)
      case dia α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldDiamond.decreases_lmOf_nonAtomic notAtom E_in y_in_Y
      case box α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [List.append_nil, Multiset.mem_coe]
        exact unfoldBox.decreases_lmOf_nonAtomic notAtom E_in y_in_Y
    case oneSidedR orule ress_def =>
      subst ress_def
      cases orule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case neg => linarith
      case con => cases y_in_Y <;> (subst_eqs; linarith)
      case nCo => cases Y_in_ress <;> (subst_eqs; simp at * ; subst_eqs ; linarith)
      case dia α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [Multiset.mem_coe]
        exact unfoldDiamond.decreases_lmOf_nonAtomic notAtom  E_in y_in_Y
      case box α φ notAtom =>
        rcases Y_in_ress with ⟨E, E_in, E_def⟩
        subst E_def
        simp_all only [Multiset.mem_coe]
        exact unfoldBox.decreases_lmOf_nonAtomic notAtom E_in y_in_Y
    case loadedL lrule ress_def =>
      simp [node_to_multiset]
      cases lrule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case dia α χ notAtom =>
        -- we re-use the lemma for the free analogue here
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded_eq α χ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload, negUnload]
      case dia' α φ notAtom =>
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded'_eq α φ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload]
    case loadedR lrule ress_def =>
      simp [node_to_multiset]
      cases lrule
      all_goals
        simp [node_to_multiset] at *
        try subst_eqs
        try simp at *
        try subst_eqs
      case dia α χ notAtom =>
        -- we re-use the lemma for the free analogue here
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded_eq α χ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload, negUnload]
      case dia' α φ notAtom =>
        rcases Y_in_ress with ⟨F, o, in_unfold, Y_def⟩
        apply unfoldDiamond.decreases_lmOf_nonAtomic notAtom
        · rw [← unfoldDiamondLoaded'_eq α φ]
          simp only [List.mem_map, Prod.exists]
          use F, o
        · subst Y_def
          cases o <;> simp_all [pairUnload]

-- An equivalent definition of DM.
def MultisetLT' {α} [Preorder α] (M : Multiset α) (N : Multiset α) : Prop :=
  ∃ (X Y Z: Multiset α),
        Y ≠ ∅ ∧
        M = Z + X ∧
        N = Z + Y ∧
        (∀ x ∈ X, ∃ y ∈ Y, x < y)

-- The definition used in Multiset.IsDershowitzMannaLT is equivalent to ours.
theorem MultisetDMLT.iff_MultisetLT' [Preorder α] {M N : Multiset α} :
    Multiset.IsDershowitzMannaLT M N ↔ MultisetLT' M N := by
  unfold MultisetLT'
  constructor
  · intro M_LT_N
    cases M_LT_N
    aesop
  · intro M_LT'_N
    rcases M_LT'_N with ⟨X,Y,Z,claim⟩
    constructor
    all_goals tauto

theorem localRuleApp.decreases_DM
    (lra : LocalRuleApp) : ∀ Y ∈ lra.C, lt_Sequent Y lra.X :=
  by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconP⟩
  subst hC
  intro RES RES_in
  simp [applyLocalRule] at RES_in
  rcases RES_in with ⟨⟨Lnew,Rnew,Onew⟩, Y_in_ress, def_RES⟩
  unfold lt_Sequent
  simp at def_RES
  rw [MultisetDMLT.iff_MultisetLT']
  unfold MultisetLT'
  use node_to_multiset (Lnew, Rnew, Onew) -- choose X to be the newly added formulas
  use node_to_multiset (Lcond, Rcond, Ocond) -- choose Y to be the removed formulas
  -- Now choose a way to define Z (the context formulas that stay)
  -- let Z:= use node_to_multiset RES - node_to_multiset (Lnew, Rnew, Onew) -- way 1
  let Z := node_to_multiset (L, R, O) - node_to_multiset (Lcond, Rcond, Ocond) -- way 2
  use Z
  -- claim that the other definition would have been the same:
  have Z_eq : Z = node_to_multiset RES - node_to_multiset (Lnew, Rnew, Onew) := by
    unfold Z
    have : node_to_multiset RES =   node_to_multiset (L, R, O)
                                  - node_to_multiset (Lcond, Rcond, Ocond)
                                  + node_to_multiset (Lnew, Rnew, Onew) := by
      have lrOprop : O ≠ none → Ocond = none → Onew = none := by
        cases O <;> cases Ocond <;> cases Onew <;> cases rule <;> simp_all
        all_goals
          rcases Y_in_ress with ⟨a, a_in, bla⟩ ; cases bla
      rw [← def_RES, node_to_multiset_of_precon preconP lrOprop]
    rw [this]
    subst def_RES
    simp_all only [Option.instHasSubsetOption, add_tsub_cancel_right]
  split_ands
  · exact (LocalRule.cond_non_empty rule : node_to_multiset (Lcond, Rcond, Ocond) ≠ ∅)
  · rw [Z_eq]
    apply Multiset.sub_add_of_subset_eq
    -- This works but should be cleaned up to avoid non-terminal simp.
    all_goals cases O <;> try (rename_i cond; cases cond)
    all_goals cases Onew <;> try (rename_i f; cases f)
    all_goals cases Ocond <;> try (rename_i cond; cases cond)
    all_goals simp_all
    all_goals subst_eqs
    all_goals
      simp only []
      rw [Multiset.le_iff_count]
      intro φ
      simp_all
      linarith
  · apply Multiset.sub_add_of_subset_eq
    exact preconP_to_submultiset preconP
  · exact LocalRuleDecreases rule _ Y_in_ress

@[simp]
def endNodesOf : {X : _} → LocalTableau X → List Sequent
  | .(_), (@byLocalRule X lra _ next) =>
      (lra.C.attach.map (fun ⟨Y, h⟩ => endNodesOf (next Y h))).flatten
  | .(_), (@sim X _) => [X]
termination_by
  X => X -- pick up instance WellFoundedRelation Sequent from above!
decreasing_by
  subst_eqs
  apply localRuleApp.decreases_DM lra Y h

/-- An open local tableau has at least one end node. -/
def OpenLocalTableau (X : Sequent) : Type := {lt : LocalTableau X // endNodesOf lt ≠ []}
deriving DecidableEq

/-! ## Helper functions, relating end nodes and children -/

-- TODO Computable version possible?
noncomputable def endNode_to_endNodeOfChildNonComp (lrA)
  (E_in : E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  @Subtype Sequent (fun x => ∃ h, E ∈ endNodesOf (subTabs x h)) := by
  simp [endNodesOf] at E_in
  choose l h E_in using E_in
  aesop

theorem endNodeIsEndNodeOfChild (lrA)
  (E_in : E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  ∃ Y h, E ∈ endNodesOf (subTabs Y h) := by
  have := endNode_to_endNodeOfChildNonComp lrA E_in
  use this
  aesop

theorem endNodeOfChild_to_endNode
    {Y : Sequent}
    (lrA : LocalRuleApp)
    {ltX : LocalTableau lrA.X}
    subTabs
    (h : ltX = LocalTableau.byLocalRule lrA rfl subTabs)
    (Y_in : Y ∈ lrA.C)
    {Z : Sequent}
    (Z_in : Z ∈ endNodesOf (subTabs Y Y_in))
    : Z ∈ endNodesOf ltX :=
  by
  cases h' : subTabs Y Y_in -- No induction needed for this!
  case sim Y_isSimp =>
    subst h
    simp only [endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, ↓existsAndEq]
    grind
  case byLocalRule C' subTabs' lrA' =>
    subst h
    rw [h'] at Z_in
    simp only [endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, ↓existsAndEq]
    grind

/-! ## Overall Soundness and Invertibility of LocalTableau -/

theorem localTableauTruth {X} (lt : LocalTableau X) {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ X  ↔ ∃ Y ∈ endNodesOf lt, (M, w) ⊨ Y := by
  induction lt
  case byLocalRule Y lrA X_def next IH  =>
    have := localRuleTruth lrA M w
    aesop
  case sim =>
    simp_all

open HasSat

theorem localTableauSat {X} (lt : LocalTableau X) :
    satisfiable X ↔ ∃ Y ∈ endNodesOf lt, satisfiable Y := by
  constructor
  · rintro ⟨W, M, w, w_X⟩
    rw [localTableauTruth lt M w] at w_X
    rcases w_X with ⟨Y, Y_in, w_Y⟩
    use Y, Y_in, W, M, w
  · rintro ⟨Y, Y_in, ⟨W, M, w, w_Y⟩⟩
    use W, M, w
    apply (localTableauTruth lt M w).2
    use Y

/-! ## Local Tableaux make progress

These lemmas are used to show soundness, in particular `loadedDiamondPaths`.
-/

/-- End nodes of any local tableau are basic. -/
lemma endNodesOf_basic {X Z} {ltZ : LocalTableau Z} : X ∈ endNodesOf ltZ → X.basic := by
  induction ltZ
  case byLocalRule B lrA next IH =>
    intro X_in
    simp [endNodesOf] at X_in
    aesop
  case sim X =>
    simp_all

/-- If `X` is not basic, then all end nodes `Y` of a local tableau `lt` for `X`
are strictly lower than `X` according to the DM-ordering of their multisets. -/
theorem endNodesOf_nonbasic_lt_Sequent {X Y} (lt : LocalTableau X) (X_nonbas : ¬ X.basic) :
    Y ∈ endNodesOf lt → lt_Sequent Y X := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    subst X_def
    intro Y_in
    simp at Y_in
    rcases Y_in with ⟨Z, Z_in_B, Y_in_l⟩
    by_cases Z.basic
    case pos Z_basic =>
      have next_Z_is_end : endNodesOf (next Z Z_in_B) = [Z] := by
        cases next Z Z_in_B <;> simp
        case byLocalRule lrA next Z_def =>
          absurd nonbasic_of_localRuleApp lrA
          subst Z_def
          exact Z_basic
      have Z_eq_Y : Z = Y := by aesop
      subst Z_eq_Y
      exact localRuleApp.decreases_DM lra _ Z_in_B
    case neg Z_nonbas =>
      -- We use that lt_Sequent is transitive.
      apply @Multiset.IsDershowitzMannaLT.trans _ _ _ (node_to_multiset Z)
      · exact IH Z Z_in_B Z_nonbas Y_in_l
      · exact localRuleApp.decreases_DM lra _ Z_in_B
  case sim =>
    exfalso
    tauto

/-- If a sequent is lower according the DM-ordering, then it is different. -/
lemma non_eq_of_ltSequent : lt_Sequent X Y → X ≠ Y := by
  intro lt X_eq_Y
  subst X_eq_Y
  absurd lt
  -- This is easy, because the DM ordering is irreflexive.
  have := WellFounded.irrefl (instWellFoundedRelationSequent.2)
  apply this.1

/-- If `X` is not basic, then for all end nodes `Y` of a
local tableau `lt` for `X` we have that `Y ≠ X`. -/
theorem endNodesOf_nonbasic_non_eq {X Y} (lt : LocalTableau X) (X_nonbas : ¬ X.basic) :
    Y ∈ endNodesOf lt → Y ≠ X := by
  intro Y_in
  apply non_eq_of_ltSequent
  apply endNodesOf_nonbasic_lt_Sequent lt X_nonbas Y_in

-- upstream me / Haitian? ;-)
lemma IsDershowitzMannaLT.irrefl [Preorder α] [WellFoundedLT α] (X : Multiset α) :
    ¬ Multiset.IsDershowitzMannaLT X X := by
  apply (WellFounded.irrefl (?_)).1
  exact (@Multiset.instWellFoundedIsDershowitzMannaLT α _ _).2

/-- If a sequent is lower according to the DM-ordering, then they are multiset-different.
(The analogue with finset instead of multiset does not hold.) -/
lemma non_multisetEqTo_of_ltSequent : lt_Sequent X Y → ¬ X.multisetEqTo Y := by
  intro lt X_eq_Y
  unfold lt_Sequent at lt
  have : node_to_multiset X ≠ node_to_multiset Y := by
    intro hyp
    rw [hyp] at lt
    absurd lt
    apply IsDershowitzMannaLT.irrefl
  clear lt
  rcases X with ⟨L,R,_|(lfl|lfr)⟩ <;> rcases Y with ⟨L',R',_|(lfl'|lfr')⟩
  <;> simp [Sequent.multisetEqTo, node_to_multiset] at *
  · exact this (List.Perm.append X_eq_Y.1 X_eq_Y.2)
  · simp_all
    exact this (List.Perm.append X_eq_Y.1 X_eq_Y.2.1)
  · simp_all
    exact this (List.Perm.append X_eq_Y.1 X_eq_Y.2.1)
