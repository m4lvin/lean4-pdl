import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.Linarith

import Pdl.Substitution
import Pdl.Star

/-! # Local Box Unfolding (Section 3.1) -/

/-! ## Preparation for Boxes: Test Profiles -/

/-- Type of test profiles for a given program. -/
def TP (α : Program) : Type := {τ // τ ∈ testsOfProgram α} → Bool

instance : Fintype (TP α) := by
  unfold TP
  apply Pi.instFintype

theorem TP_eq_iff {α} {ℓ ℓ' : TP α} : (ℓ = ℓ') ↔ ∀ τ ∈ (testsOfProgram α).attach, ℓ τ = ℓ' τ := by
  constructor
  · intro ℓ_eq_ℓ _ _
    simp_all
  · intro rhs
    simp_all only [List.mem_attach, forall_const, Subtype.forall]
    unfold TP at *
    ext τ
    apply rhs

-- Coercions of TP α to the subprograms of α.
-- These are needed to re-use `ℓ` in recursive calls of `F` and `P` below.
instance : CoeOut (TP (α ⋓ β)) (TP α) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by
    cases τ; simp only [testsOfProgram, List.mem_append]; left; assumption⟩ ⟩
instance : CoeOut (TP (α ⋓ β)) (TP β) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by
   cases τ; simp only [testsOfProgram, List.mem_append]; right; assumption⟩ ⟩
instance : CoeOut (TP (α ;' β)) (TP α) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by
   cases τ; simp only [testsOfProgram, List.mem_append]; left; assumption⟩ ⟩
instance : CoeOut (TP (α ;' β)) (TP β) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by
   cases τ; simp only [testsOfProgram, List.mem_append]; right; assumption⟩ ⟩
instance : CoeOut (TP (∗α)) (TP α) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram]; exact f_in⟩⟩

/-- List of all test profiles for a given program.
Note that in contrast to `Fintype.elems : Finset (TP α)`
here we get a computable List (TP α). -/
def allTP α : List (TP α) := (testsOfProgram α).sublists.map (fun l ⟨τ, _⟩ => τ ∈ l)

/-- All test profiles are in the list of all test profiles.
Thanks to Floris van Doorn
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/List.20of.20.28provably.29.20all.20functions.20from.20given.20List.20to.20Bool
-/
theorem allTP_mem (ℓ : TP α) : ℓ ∈ allTP α := by
  simp_rw [allTP, List.mem_map, List.mem_sublists]
  use (testsOfProgram α).filter (fun τ ↦ ∃ h : τ ∈ testsOfProgram α, ℓ ⟨τ, h⟩)
  simp (config := {contextual := true}) [TP, List.mem_filter, funext_iff]

/-- σ^ℓ -/
def signature (α : Program) (ℓ : TP α) : Formula :=
  Con <| (testsOfProgram α).attach.map (fun τ => if ℓ τ then τ.val else ~τ.val)

theorem signature_iff {W} {M : KripkeModel W} {w : W} :
    evaluate M w (signature α ℓ) ↔ ∀ τ ∈ (testsOfProgram α).attach, ℓ τ ↔ evaluate M w τ.val := by
  simp only [signature, conEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, forall_const, Subtype.forall]
  constructor
  · intro w_ℓ τ τ_in
    cases em (ℓ ⟨τ, τ_in⟩)
    · specialize w_ℓ τ τ τ_in
      aesop
    · specialize w_ℓ (~τ) τ τ_in
      aesop
  · aesop

-- Now come two out of the three facts about test profiles and signatures.

-- unused
theorem top_equiv_disj_TP : ∀ α, tautology (dis ((allTP α).map (signature α))) := by
  intro α W M w
  rw [disEval]
  simp only [List.mem_map, exists_exists_and_eq_and]
  have := Classical.propDecidable
  let ℓ : TP α := fun τ => evaluate M w τ
  use ℓ
  constructor
  · apply allTP_mem
  · simp only [signature, conEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index]
    intro f τ τ_in def_f
    subst def_f
    aesop

-- unused?
theorem signature_contradiction_of_neq_TPs {ℓ ℓ' : TP α} :
    ℓ ≠ ℓ' → contradiction (signature α ℓ ⋀ signature α ℓ') := by
  simp only [ne_eq]
  rw [TP_eq_iff]
  intro ldiff W M w
  simp_all only [List.mem_attach, forall_true_left, Subtype.forall, not_forall, evaluate, not_and]
  rcases ldiff with ⟨τ, τ_in, disagree⟩
  simp_all only [signature, conEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, not_forall, exists_and_right, ↓existsAndEq, exists_prop]
  intro ℓ_conform
  cases em (ℓ ⟨τ,τ_in⟩)
  · specialize ℓ_conform τ τ τ_in
    simp_all only [ite_true, forall_true_left]
    use τ
    simp_all
  · specialize ℓ_conform (~τ) τ τ_in
    simp_all only [Bool.not_eq_true, evaluate]
    use τ
    simp_all

-- unused?
theorem equiv_iff_TPequiv : φ ≡ ψ  ↔  ∀ ℓ : TP α, φ ⋀ signature α ℓ ≡ ψ ⋀ signature α ℓ := by
  constructor
  · intro phi_iff_psi ℓ W M w
    simp only [evaluate, and_congr_left_iff]
    specialize phi_iff_psi W M w
    tauto
  · intro hyp W M w
    have := Classical.propDecidable
    let ℓ : TP α := fun τ => evaluate M w τ
    specialize hyp ℓ W M w
    simp only [evaluate, and_congr_left_iff] at hyp
    apply hyp
    unfold ℓ
    simp only [signature, decide_eq_true_eq, List.map_subtype, List.unattach_attach, conEval,
      List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro τ _
    split <;> simp_all

/-!
## Boxes: F, P, X and unfoldBox

Note: In P and Xset we use lists not sets, to eventually make formulas.
-/

def F : (α : Program) → (ℓ : TP α) → List Formula
| ·_ , _ => ∅
| ?'τ, ℓ => if ℓ ⟨τ, by simp [testsOfProgram]⟩ then ∅ else [~ τ]
| α⋓β, ℓ => F α ℓ ∪ F β ℓ
| α;'β, ℓ => F α ℓ ∪ F β ℓ
| ∗α, ℓ => F α ℓ

lemma F_sub_testsOfProgram_map_neg (α : Program) (ℓ : TP α) :
    F α ℓ ⊆ (testsOfProgram α).map Formula.neg := by
  cases α <;> simp_all only [F, List.empty_eq, testsOfProgram, List.map_nil, List.Subset.refl]
  case sequence α β =>
    have IHα := F_sub_testsOfProgram_map_neg α
    have IHβ := F_sub_testsOfProgram_map_neg β
    grind
  case union α β =>
    have IHα := F_sub_testsOfProgram_map_neg α
    have IHβ := F_sub_testsOfProgram_map_neg β
    grind
  case star α =>
    have IHα := F_sub_testsOfProgram_map_neg α
    grind
  case test =>
    split <;> grind

def P : (α : Program) →  (ℓ : TP α) → List (List Program)
| ·a, _ => [ [(·a : Program)] ]
| ?' τ, ℓ => if ℓ ⟨τ, by simp [testsOfProgram]⟩ then [ [] ] else ∅
| α ⋓ β, ℓ => P α ℓ ∪ P β ℓ
| α;'β, ℓ => ((P α ℓ).filter (· != [])).map (fun as => as ++ [β])
             ∪ (if [] ∈ P α ℓ then (P β ℓ) else [])
| ∗α, ℓ => [ [] ] ∪ ((P α ℓ).filter (· != [])).map (fun as => as ++ [∗α])

def Xset (α : Program) (ℓ : TP α) (ψ : Formula) : List Formula :=
  F α ℓ ++ (P α ℓ).map (fun as => Formula.boxes as ψ)

/-- unfold_□(α,ψ) -/
def unfoldBox (α : Program) (φ : Formula) : List (List Formula) :=
  (allTP α).map (fun ℓ => Xset α ℓ φ)

theorem F_mem_iff_neg α (ℓ : TP α) φ :
    φ ∈ F α ℓ ↔ ∃ τ, ∃ (h : τ ∈ testsOfProgram α), φ = (~τ) ∧ ℓ ⟨τ,h⟩ = false := by
  simp_all only [exists_and_left]
  cases α
  all_goals
    simp_all only [F, List.empty_eq, List.not_mem_nil, testsOfProgram, IsEmpty.exists_iff,
      and_false, exists_const]
  case sequence α β =>
    have := F_mem_iff_neg α ℓ φ
    have := F_mem_iff_neg β ℓ φ
    aesop
  case union α β =>
    have := F_mem_iff_neg α ℓ φ
    have := F_mem_iff_neg β ℓ φ
    aesop
  case star α =>
    have := F_mem_iff_neg α ℓ φ
    aesop
  case test τ =>
    aesop

theorem P_monotone α (ℓ ℓ' : TP α) (h : ∀ τ, ℓ τ → ℓ' τ) δ : δ ∈ P α ℓ → δ ∈ P α ℓ' := by
  cases α
  case atom_prog _ =>
    simp_all only [testsOfProgram, Subtype.forall, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, P, List.mem_cons, or_false]
  case union α β =>
    intro δ_in
    have IHα := P_monotone α ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    have IHβ := P_monotone β ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    simp only [testsOfProgram, Subtype.forall, List.mem_append, P, List.mem_union_iff] at *
    cases δ_in <;> simp_all
  case sequence α β =>
    intro δ_in
    have IHα := P_monotone α ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    have IHβ := P_monotone β ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    simp only [testsOfProgram, Subtype.forall, List.mem_append, P, List.mem_union_iff, List.mem_map,
      List.mem_filter, bne_iff_ne, ne_eq, List.mem_ite_nil_right] at *
    cases δ_in
    case inl δ_in =>
      rcases δ_in with ⟨δ', δ'_in, def_δ⟩
      subst def_δ
      left
      use δ'
      simp_all
    case inr h' =>
      simp_all
  case star α =>
    intro δ_in
    cases em (δ = [])
    · simp_all [testsOfProgram, P]
    · have IHα := P_monotone α ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
      simp_all only [testsOfProgram, Subtype.forall, P, List.cons_union, List.nil_union,
        List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, List.append_eq_nil_iff, List.cons_ne_self,
        and_false, exists_const, not_false_eq_true, List.insert_of_not_mem, List.mem_cons, false_or]
      rcases δ_in with ⟨δ', δ'_in, def_δ⟩
      subst def_δ
      use δ'
      simp_all
  case test τ =>
    simp_all [testsOfProgram, P]

-- prove this via boxHelperTermination instead?
theorem PgoesDown : γ ∈ δ → δ ∈ P α ℓ →
  (if α.isAtomic
    then γ = α
    else if α.isStar then lengthOfProgram γ ≤ lengthOfProgram α
                     else lengthOfProgram γ < lengthOfProgram α) := by
  intro γ_in δ_in
  cases α
  case sequence α β =>
    simp_all only [P, List.mem_union_iff, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq,
      List.mem_ite_nil_right, Program.isAtomic, Bool.false_eq_true, ↓reduceIte, Program.isStar,
      lengthOfProgram]
    cases δ_in
    case inl δ_in =>
      rcases δ_in with ⟨αs, αs_in, def_δ⟩
      subst def_δ
      simp_all only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      cases γ_in
      case inl γ_in =>
        have IH := PgoesDown γ_in αs_in.1
        cases em α.isAtomic <;> cases em α.isStar
        all_goals (simp_all;try linarith)
      case inr γ_in =>
        subst γ_in
        linarith
    case inr δ_in =>
      cases em ([] ∈ P α ℓ)
      · simp_all only [true_and]
        have IH := PgoesDown γ_in δ_in
        cases em β.isAtomic <;> cases em β.isStar
        all_goals (simp_all;try linarith)
      · simp_all
  case union α β =>
    simp_all only [P, List.mem_union_iff, Program.isAtomic, Bool.false_eq_true, ↓reduceIte,
      Program.isStar, lengthOfProgram]
    cases δ_in
    case inl δ_in =>
      have IH := PgoesDown γ_in δ_in
      cases em α.isAtomic <;> cases em α.isStar
      all_goals (simp_all;try linarith)
    case inr δ_in =>
      have IH := PgoesDown γ_in δ_in
      cases em β.isAtomic <;> cases em β.isStar
      all_goals (simp_all;try linarith)
  case star α =>
    simp_all only [P, List.cons_union, List.nil_union, List.mem_map, List.mem_filter, bne_iff_ne,
      ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, exists_const, not_false_eq_true,
      List.insert_of_not_mem, List.mem_cons, Program.isAtomic, Bool.false_eq_true, ↓reduceIte,
      Program.isStar, lengthOfProgram]
    cases δ
    case nil =>
      exfalso; cases γ_in
    case cons =>
      simp only [reduceCtorEq, false_or] at δ_in
      rcases δ_in with ⟨αs, ⟨αs_in, αs_not_null⟩, def_δ⟩
      cases em (γ ∈ αs)
      case inl γ_in =>
        have IH := PgoesDown γ_in αs_in
        cases em (α.isAtomic) <;> cases em α.isStar
        all_goals (simp_all;try linarith)
      case inr γ_not_in =>
        have : γ = (∗α) := by
          rw [← def_δ] at γ_in; simp at γ_in; tauto
        subst_eqs
        simp
  all_goals -- test and atom_prog
    simp_all [Program.isAtomic, Program.isStar, P]

theorem F_goes_down : φ ∈ F α ℓ → lengthOfFormula φ < lengthOfProgram α := by
  intro φ_in
  cases α
  all_goals
    simp only [F, List.mem_union_iff, lengthOfProgram] at *
  case atom_prog =>
    simp only [List.empty_eq, List.not_mem_nil] at φ_in
  case sequence α β =>
    cases φ_in
    case inl φ_in_Fα =>
      have IHα := F_goes_down φ_in_Fα
      linarith
    case inr φ_in_Fβ =>
      have IHβ := F_goes_down φ_in_Fβ
      linarith
  case union α β =>
    cases φ_in
    case inl φ_in_Fα =>
      have IHα := F_goes_down φ_in_Fα
      linarith
    case inr φ_in_Fβ =>
      have IHβ := F_goes_down φ_in_Fβ
      linarith
  case star α =>
    have IHα := F_goes_down φ_in
    linarith
  case test τ =>
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩)
    · simp_all
    · simp_all

theorem keepFreshF α ℓ (x_notin : x ∉ α.voc) : ∀ φ ∈ F α ℓ, x ∉ φ.voc := by
  intro φ φ_in
  cases α
  case test τ =>
    simp only [Program.voc, F, List.empty_eq, List.mem_ite_nil_left, Bool.not_eq_true,
      List.mem_cons, List.not_mem_nil, or_false] at *
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩) <;> simp_all [Formula.voc]
  case sequence α β =>
    simp only [Program.voc, Finset.mem_union, not_or, F, List.mem_union_iff] at *
    have := keepFreshF α ℓ x_notin.1
    have := keepFreshF β ℓ x_notin.2
    aesop
  case union α β =>
    simp only [Program.voc, Finset.mem_union, not_or, F, List.mem_union_iff] at *
    have := keepFreshF α ℓ x_notin.1
    have := keepFreshF β ℓ x_notin.2
    aesop
  case star α =>
    simp only [Program.voc, F] at *
    have := keepFreshF α ℓ x_notin
    aesop
  case atom_prog =>
    simp [Program.voc, F] at *

theorem keepFreshP α ℓ (x_notin : x ∉ α.voc) : ∀ δ ∈ P α ℓ, x ∉ δ.pvoc := by
  intro δ δ_in
  cases α
  all_goals
    simp_all only [ Finset.mem_singleton, Finset.mem_sup, Finset.mem_union, IsEmpty.forall_iff,
      List.empty_eq, List.mem_cons, List.mem_filter, List.mem_ite_nil_right, List.mem_map,
      List.mem_toFinset, List.mem_union_iff, List.not_mem_nil, List.pvoc, P, Program.voc,
      Vocab.fromList, bne_iff_ne, exists_exists_and_eq_and, id_eq, implies_true, implies_true,
      ne_eq, not_and, not_exists, not_false_eq_true, not_or, or_false ]
  case sequence α β =>
    have IHα := keepFreshP α ℓ x_notin.1
    have IHβ := keepFreshP β ℓ x_notin.2
    simp_all only [List.pvoc, Vocab.fromList, Finset.mem_sup, List.mem_toFinset, List.mem_map,
      id_eq, exists_exists_and_eq_and, not_exists, not_and]
    rcases δ_in with (⟨δ', δ'_in, def_δ⟩ | δ_in)
    · subst def_δ
      have := IHα _ δ'_in.1
      simp_all
      aesop
    · cases em ([] ∈ P α ℓ) <;> simp_all
      have := IHβ _ δ_in
      simp_all
  case union α β =>
    intro y y_in
    rcases δ_in with δ_in|δ_in
    · have IHα := keepFreshP α ℓ x_notin.1 _ δ_in
      simp_all
    · have IHβ := keepFreshP β ℓ x_notin.2 _ δ_in
      simp_all
  case star α =>
    have IHα := keepFreshP α ℓ x_notin
    rcases δ_in with (_ | ⟨δ', δ'_in, def_δ⟩)
    · subst_eqs
      simp_all
    · subst def_δ
      simp_all only [List.pvoc, Vocab.fromList, Finset.mem_sup, List.mem_toFinset, List.mem_map,
        id_eq, exists_exists_and_eq_and, not_exists, not_and, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro γ (γ_in_δ' | γ_def)
      · exact IHα _ δ'_in.1 _ γ_in_δ'
      · subst_eqs; assumption

set_option maxHeartbeats 2000000 in -- for simp and aesop timeouts
/-- Depending on α we know what can occur inside `δ ∈ P α ℓ` for unfoldBox. -/
theorem boxHelperTermination α (ℓ : TP α) :
  ∀ δ ∈ P α ℓ,
      ( α.isAtomic → δ = [α] )
    ∧ ( ∀ β, α = (∗β) →
          δ = []
        ∨ ∃ a δ1n, (δ = [(·a : Program)] ++ δ1n ++ [∗β]
                    ∧ ((·a : Program)::δ) ⊆ subprograms α) )
    ∧ ( (¬ α.isAtomic ∧ ¬ α.isStar) →
          δ = []
        ∨ ∃ a δ1n, (δ = [(·a : Program)] ++ δ1n
                    ∧ ((·a : Program)::δ) ⊆ subprograms α) )
    := by
  intro δ δ_in
  cases α
  all_goals
    simp_all only [Bool.false_eq_true, IsEmpty.exists_iff, IsEmpty.forall_iff,
      List.append_eq_nil_iff, List.cons.injEq, List.cons_append, List.cons_ne_self,
      List.cons_subset, List.empty_eq, List.mem_cons, List.mem_filter, List.mem_ite_nil_right,
      List.mem_map, List.mem_union_iff, List.nil_append, List.nil_eq, List.nil_subset,
      List.not_mem_nil, P, Program.atom_prog.injEq, Program.isAtomic, Program.isStar,
      Program.star.injEq, and_self, and_true, bne_iff_ne, exists_and_right, exists_const,
      false_and, forall_const, forall_eq', implies_true, ne_eq, not_false_eq_true,
      not_isEmpty_of_nonempty, not_true_eq_false, or_false, or_self, or_true, reduceCtorEq,
      subprograms.refl, true_and]
  case sequence α β =>
    rcases δ_in with ⟨δ', ⟨ ⟨δ'_in, δ'_ne⟩, def_δ⟩⟩ | δ_in
    · subst def_δ
      simp_all only [List.append_eq_nil_iff, List.cons_ne_self, and_self, List.append_subset,
        List.cons_subset, List.nil_subset, and_true, false_or]
      have IH := boxHelperTermination α ℓ δ' δ'_in
      simp_all only [List.cons_append, List.nil_append, List.cons_subset, exists_and_right,
        false_or, and_imp]
      by_cases α.isAtomic <;> by_cases α.isStar
      · simp_all only [List.cons_ne_self, not_false_eq_true, forall_const, not_true_eq_false,
          not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and, implies_true, and_true,
          List.cons_append, List.nil_append, List.cons.injEq, exists_and_left, ↓existsAndEq,
          List.cons_subset, List.nil_subset]
        exfalso
        rw [Program.isAtomic_iff] at *
        rw [Program.isStar_iff] at *
        rename _ => hyp1
        rcases hyp1 with ⟨γ, α_def⟩
        subst α_def
        rename _ => hyp2
        rcases hyp2 with ⟨a, α_def⟩
        cases α_def
      case neg isAt notStar =>
        simp_all only [List.cons_ne_self, not_false_eq_true, forall_const, not_true_eq_false,
          not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and, implies_true, and_true,
          List.cons_append, List.nil_append, List.cons.injEq, exists_and_left, ↓existsAndEq,
          List.cons_subset, List.nil_subset]
        rw [Program.isAtomic_iff] at isAt
        rcases isAt with ⟨a, α_def⟩
        use a
        subst α_def
        simp [subprograms]
      · simp_all only [IsEmpty.forall_iff, not_false_eq_true, not_true_eq_false,
          not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and, implies_true, and_true]
        rw [Program.isStar_iff] at *
        rename _ => hyp
        rcases hyp with ⟨γ, α_def⟩
        specialize IH γ
        simp_all only [subprograms, List.cons_append, List.nil_append, List.mem_cons, reduceCtorEq,
          false_or, forall_const, List.mem_append, subprograms.refl, or_true, and_true]
        rcases IH with ⟨a, ⟨δ1n, δ'_def⟩, ⟨a_in, δ'_sub⟩⟩
        use a
        subst δ'_def
        simp only [reduceCtorEq, not_false_eq_true, List.cons_subset, List.mem_cons, false_or,
          List.append_subset, true_or, List.nil_subset, List.subset_cons_of_subset, and_self,
          and_true, List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq, true_and,
          exists_eq', List.mem_append, and_self_left] at *
        constructor
        · left; exact a_in
        · subst α_def
          intro α α_in
          have := δ'_sub.2 α_in
          aesop
      · simp_all only [IsEmpty.forall_iff, not_false_eq_true, forall_const, true_and]
        rcases IH.2 with ⟨a, ⟨δ1n, δ'_def⟩, ⟨_, δ'_sub⟩⟩
        subst δ'_def
        simp [subprograms] at *
        aesop
    · by_cases [] ∈ P α ℓ
      · simp_all only [true_and, subprograms, List.cons_append, List.nil_append, List.mem_cons,
        reduceCtorEq, List.mem_append, false_or]
        have IH := boxHelperTermination β ℓ δ δ_in
        simp_all only [List.cons_append, List.nil_append, List.cons_subset, exists_and_right,
          and_imp]
        by_cases β.isAtomic <;> by_cases β.isStar
        · simp_all only [forall_const, not_true_eq_false, not_isEmpty_of_nonempty,
            IsEmpty.exists_iff, true_and, or_true, implies_true, and_true,
            List.cons_ne_self, List.cons.injEq, List.nil_eq, exists_eq_right, List.cons_subset,
            subprograms.refl, List.nil_subset, and_self, List.subset_append_of_subset_right,
            List.subset_cons_of_subset, false_or]
          exfalso
          rw [Program.isAtomic_iff] at *
          rw [Program.isStar_iff] at *
          rename _ => hyp1
          rcases hyp1 with ⟨γ, α_def⟩
          subst α_def
          rename _ => hyp2
          rcases hyp2 with ⟨a, α_def⟩
          cases α_def
        · simp_all only [forall_const, not_true_eq_false, not_isEmpty_of_nonempty,
            IsEmpty.exists_iff, true_and, or_true, implies_true, and_true,
            List.cons_ne_self, List.cons.injEq, List.nil_eq, exists_eq_right, List.cons_subset,
            subprograms.refl, List.nil_subset, and_self, List.subset_append_of_subset_right,
            List.subset_cons_of_subset, false_or]
          rw [Program.isAtomic_iff] at *
          cases IH
          subst_eqs
          simp_all [subprograms]
          aesop
        · simp_all only [IsEmpty.forall_iff, not_false_eq_true, not_true_eq_false,
            not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and, or_true, implies_true,
            and_true]
          rw [Program.isStar_iff] at *
          rename _ => hyp
          rcases hyp with ⟨γ, α_def⟩
          specialize IH γ
          simp_all
          rcases IH with ⟨a, δ1n, δ'_def⟩ <;> aesop
        · cases IH
          simp_all [subprograms]
          aesop
      · simp_all
  case union α β =>
    cases δ_in
    case inl δ_in =>
      by_cases α.isAtomic <;> by_cases α.isStar <;>
        simp_all only [Program.isAtomic_iff, Program.isStar_iff, subprograms, List.cons_append,
          List.nil_append, List.mem_cons, reduceCtorEq, List.mem_append, false_or]
      case pos hyp1 hyp2 =>
        rcases hyp1 with ⟨γ, α_def⟩
        rcases hyp2 with ⟨γ, α_def⟩
        subst_eqs
      case pos hyp1 hyp2 =>
        rcases hyp2 with ⟨γ, α_def⟩
        subst α_def
        simp_all
        have IH := boxHelperTermination (∗γ) ℓ δ δ_in
        aesop
      case neg hyp1 hyp2 =>
        rcases hyp1 with ⟨a, α_def⟩
        subst α_def
        have IH := boxHelperTermination (·a : Program) ℓ δ δ_in
        simp_all [Program.isAtomic_iff, Program.isStar_iff, subprograms]
      · have IH := boxHelperTermination (α) ℓ δ δ_in
        simp_all [Program.isAtomic_iff, Program.isStar_iff]
        aesop
    case inr δ_in =>
      by_cases β.isAtomic <;> by_cases β.isStar <;>
        simp_all only [Program.isAtomic_iff, Program.isStar_iff, subprograms, List.cons_append,
          List.nil_append, List.mem_cons, reduceCtorEq, List.mem_append, false_or]
      case pos hyp1 hyp2 =>
        rcases hyp1 with ⟨γ, β_def⟩
        rcases hyp2 with ⟨γ, β_def⟩
        subst_eqs
      case pos hyp1 hyp2 =>
        rcases hyp2 with ⟨γ, β_def⟩
        subst β_def
        simp_all
        have IH := boxHelperTermination (∗γ) ℓ δ δ_in
        aesop
      case neg hyp1 hyp2 =>
        rcases hyp1 with ⟨a, β_def⟩
        subst β_def
        have IH := boxHelperTermination (·a : Program) ℓ δ δ_in
        simp_all [Program.isAtomic_iff, Program.isStar_iff, subprograms]
      · have IH := boxHelperTermination (β) ℓ δ δ_in
        simp_all [Program.isAtomic_iff, Program.isStar_iff]
        aesop
  case star β =>
    cases δ_in
    · left; assumption
    · right
      rename _ => hyp
      rcases hyp with ⟨δ', ⟨δ'_in, bla⟩, def_δ⟩
      subst def_δ
      have IH := boxHelperTermination β ℓ δ' δ'_in
      cases em β.isAtomic <;> cases em β.isStar
      · simp_all only [List.cons_ne_self, not_false_eq_true, forall_const, List.cons_append,
        List.nil_append, List.cons_subset, exists_and_right, not_true_eq_false, and_self,
        not_isEmpty_of_nonempty, IsEmpty.exists_iff, or_true, implies_true, and_true,
        List.cons.injEq, List.self_eq_append_left, exists_eq_right, subprograms.refl,
        List.nil_subset]
        simp_all only [Program.isAtomic_iff, Program.isStar_iff]
        rename _ => hyp
        rcases hyp with ⟨γ, β_def⟩
        subst β_def
        have := IH.2 γ rfl
        simp_all
      · simp_all only [List.cons_ne_self, not_false_eq_true, forall_const, List.cons_append,
        List.nil_append, List.cons_subset, exists_and_right, not_true_eq_false, and_self,
        not_isEmpty_of_nonempty, IsEmpty.exists_iff, or_true, implies_true, and_true,
        List.cons.injEq, List.self_eq_append_left, exists_eq_right, subprograms.refl,
        List.nil_subset]
        simp_all only [Program.isAtomic_iff, Program.isStar_iff]
        rename ∃ a, β = (·a : Program) => hyp
        rcases hyp with ⟨a, β_def⟩
        subst β_def
        simp [subprograms]
      · simp_all only [IsEmpty.forall_iff, List.cons_append, List.nil_append, List.cons_subset,
          exists_and_right, false_or, not_false_eq_true, not_true_eq_false, and_false,
          not_isEmpty_of_nonempty, IsEmpty.exists_iff, or_self, and_true, true_and,
          List.append_subset, subprograms.refl, List.nil_subset, and_self]
        simp_all only [Program.isAtomic_iff, not_exists, Program.isStar_iff]
        rename ∃ α, β = (∗α) => hyp
        rcases hyp with ⟨α, β_def⟩
        subst β_def
        specialize IH α rfl
        simp only [reduceCtorEq, not_false_eq_true, implies_true, subprograms, List.cons_append,
          List.nil_append, List.mem_cons, false_or] at *
        rcases IH with ⟨a, ⟨δ1n, δ'_def⟩, ⟨a_in, δ'_sub⟩⟩
        use a
        constructor
        · use δ1n ++ [∗ α]
          subst δ'_def
          simp
        · aesop
      · simp_all only [IsEmpty.forall_iff, List.cons_append, List.nil_append, List.cons_subset,
          exists_and_right, false_or, not_false_eq_true, and_self, forall_const, true_and,
          List.append_subset, subprograms.refl, List.nil_subset, and_true]
        simp_all only [Program.isAtomic_iff, not_exists, Program.isStar_iff,
          not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and, implies_true]
        rcases IH with ⟨a, ⟨δ1n, δ'_def⟩, ⟨a_in, δ'_sub⟩⟩
        subst δ'_def
        use a
        constructor
        · use δ1n
          simp
        · simp_all [subprograms]

/-- Where formulas in the unfolding can come from.
The article also says `φ ∈ fischerLadner [⌈α⌉ψ]` which we prove later in `unfoldBox_in_FL`. -/
theorem unfoldBoxContent α ψ :
    ∀ X ∈ (unfoldBox α ψ),
    ∀ φ ∈ X,
        -- φ ∈ fischerLadner [⌈α⌉ψ] -- not done for now.
        -- ∧
        (  (φ = ψ)
         ∨ (∃ τ ∈ testsOfProgram α, φ = (~τ))
         ∨ (∃ (a : Nat), ∃ δ, φ = (⌈·a⌉⌈⌈δ⌉⌉ψ) ∧ ∀ γ ∈ ((·a : Program)::δ), γ ∈ subprograms α))
    := by
  intro X X_in φ φ_in_X
  simp only [unfoldBox, Xset, List.mem_map] at X_in
  rcases X_in with ⟨ℓ, ℓ_in, def_X⟩
  subst def_X
  simp only [List.mem_append, List.mem_map] at φ_in_X
  -- constructor
  -- · -- φ ∈ fischerLadner [⌈α⌉ψ]
  · rcases φ_in_X with φ_in_F | ⟨δ, δ_in, def_φ⟩
    · -- φ is in F so it must be a test
      right
      cases α
      case atom_prog => simp_all [F]
      case test => simp_all [F, testsOfProgram]
      case union α β =>
        simp_all only [F, testsOfProgram, List.mem_union_iff, F_mem_iff_neg, exists_and_left,
          List.mem_append, List.mem_cons, forall_eq_or_imp]
        rcases φ_in_F with
          (⟨τ, τ_in, φ_def, _⟩ | ⟨τ, τ_in, φ_def, _⟩)
          <;> simp_all
      case sequence α β =>
        simp_all only [F, testsOfProgram, List.mem_union_iff, F_mem_iff_neg, exists_and_left,
          List.mem_append, List.mem_cons, forall_eq_or_imp]
        rcases φ_in_F with
          (⟨τ, τ_in, φ_def, _⟩ | ⟨τ, τ_in, φ_def, _⟩)
          <;> simp_all
      case star β =>
        simp_all only [F, F_mem_iff_neg, exists_and_left, testsOfProgram, List.mem_cons,
          forall_eq_or_imp]
        rcases φ_in_F with (⟨τ, τ_in, φ_def, _⟩)
        simp_all
    · -- φ is made from some δ from P α ℓ
      have bht := boxHelperTermination α ℓ δ δ_in
      subst def_φ
      cases α
      case atom_prog a =>
        simp_all only [P, Program.isAtomic, List.mem_cons, List.not_mem_nil, or_false, forall_const,
          reduceCtorEq, List.cons_append, List.nil_append, subprograms, List.cons_subset,
          Program.atom_prog.injEq, or_true, true_and, not_isEmpty_of_nonempty, IsEmpty.exists_iff,
          implies_true, not_true_eq_false, Program.isStar, Bool.false_eq_true, not_false_eq_true,
          and_true, and_self, Formula.boxes_cons, Formula.boxes_nil, and_false, exists_const,
          Formula.box.injEq, forall_eq_or_imp, ↓existsAndEq, false_or]
        subst bht
        right
        use []
        simp
      case sequence α β =>
        simp_all only [P, List.mem_union_iff, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq,
          List.mem_ite_nil_right, Program.isAtomic, Bool.false_eq_true, IsEmpty.forall_iff,
          reduceCtorEq, List.cons_append, List.nil_append, subprograms, List.cons_subset,
          List.mem_cons, List.mem_append, false_or, not_isEmpty_of_nonempty, IsEmpty.exists_iff,
          or_true, implies_true, not_false_eq_true, Program.isStar, and_self, exists_and_right,
          forall_const, true_and, forall_eq_or_imp]
        rcases bht with _ | ⟨a, ⟨δ1n, δ_def⟩, ⟨a_in, δ_sub⟩⟩
        · subst_eqs; simp
        · subst δ_def
          simp_all only [List.cons_subset, List.mem_cons, reduceCtorEq, List.mem_append, or_true,
            true_and, Formula.boxes_cons, and_false, exists_const, Formula.box.injEq,
            Program.atom_prog.injEq, ↓existsAndEq, false_or]
          right
          use δ1n
          simp_all only [true_and]
          intro γ γ_in
          specialize δ_sub γ_in
          simp_all
      case union α β =>
        simp_all only [P, List.mem_union_iff, Program.isAtomic, Bool.false_eq_true,
          IsEmpty.forall_iff, reduceCtorEq, List.cons_append, List.nil_append, subprograms,
          List.cons_subset, List.mem_cons, List.mem_append, false_or, not_isEmpty_of_nonempty,
          IsEmpty.exists_iff, or_true, implies_true, not_false_eq_true, Program.isStar, and_self,
          exists_and_right, forall_const, true_and, forall_eq_or_imp]
        rcases bht with _ | ⟨a, ⟨δ1n, δ_def⟩, ⟨a_in, δ_sub⟩⟩
        · subst_eqs; simp
        · subst δ_def
          simp_all only [List.cons_subset, List.mem_cons, reduceCtorEq, List.mem_append, or_true,
            true_and, Formula.boxes_cons, and_false, exists_const, Formula.box.injEq,
            Program.atom_prog.injEq, ↓existsAndEq, false_or]
          right
          use δ1n
          simp
          grind
      case star β =>
        simp_all only [P, List.cons_union, List.nil_union, List.mem_map, List.mem_filter,
          bne_iff_ne, ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, exists_const,
          not_false_eq_true, List.insert_of_not_mem, List.mem_cons, Program.isAtomic,
          Bool.false_eq_true, IsEmpty.forall_iff, Program.star.injEq, List.cons_append,
          List.nil_append, subprograms, List.cons_subset, reduceCtorEq, false_or, exists_and_right,
          forall_eq', Program.isStar, not_true_eq_false, not_isEmpty_of_nonempty,
          IsEmpty.exists_iff, or_true, and_true, true_and, forall_eq_or_imp]
        rcases bht with _ | ⟨a, ⟨δ1n, δ_def⟩, ⟨a_in, δ_sub⟩⟩
        · subst_eqs; simp
        · subst δ_def
          simp_all only [reduceCtorEq, false_or, List.cons_subset, List.mem_cons, or_true,
            List.append_subset, true_or, List.nil_subset, List.subset_cons_of_subset, and_self,
            and_true, true_and, Formula.boxes_cons, and_false, exists_const, Formula.box.injEq,
            Program.atom_prog.injEq, ↓existsAndEq]
          right
          use δ1n ++ [∗β]
          grind
      case test τ =>
        simp_all [P, subprograms, Program.isAtomic, Program.isStar]

theorem unfoldBox_voc {x α φ} {L} (L_in : L ∈ unfoldBox α φ) {ψ} (ψ_in : ψ ∈ L)
    (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  rcases unfoldBoxContent _ _ _ L_in _ ψ_in with ψ_def | ⟨τ, τ_in, ψ_def⟩ | ⟨a, δ, ψ_def, sub_α⟩
  all_goals subst ψ_def
  · right; exact x_in_voc_ψ
  · simp only [Formula.voc] at x_in_voc_ψ
    left
    have := testsOfProgram.voc _ τ_in
    tauto
  · simp only [List.mem_cons, forall_eq_or_imp, Formula.voc, Program.voc, Finset.singleton_union,
    Finset.mem_insert] at *
    simp only [Formula.voc_boxes, List.pvoc, Finset.mem_union] at x_in_voc_ψ
    rcases x_in_voc_ψ with (x_def|x_in|x_in)
    · subst x_def
      left
      apply subprograms_voc sub_α.1
      simp
    · left
      rw [Vocab.fromListProgram_map_iff] at x_in
      rcases x_in with ⟨β, β_in, x_in_βvoc⟩
      exact subprograms_voc (sub_α.2 β β_in) x_in_βvoc
    · exact Or.inr x_in

theorem boxHelperTP α (ℓ : TP α) :
    (∀ τ, (~τ.val) ∈ F α ℓ → ℓ τ = false)
  ∧ (Con (F α ℓ) ⋀ signature α ℓ ≡ signature α ℓ)
  ∧ ∀ ψ, (Con (Xset α ℓ ψ) ⋀ signature α ℓ ≡ Con ((P α ℓ).map (fun αs => ⌈⌈αs⌉⌉ψ)) ⋀ signature α ℓ )
    := by
  refine ⟨?_, ?_, ?_⟩
  · intro τ τ_in
    have := F_mem_iff_neg α ℓ (~τ)
    aesop
  · intro W M w
    simp only [evaluate, conEval, signature, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, forall_exists_index, and_iff_right_iff_imp]
    intro w_ℓ φ φ_in
    have := F_mem_iff_neg α ℓ φ
    rw [this] at φ_in
    clear this
    rcases φ_in with ⟨τ, τ_in, φ_def, not_ℓ_τ⟩
    specialize w_ℓ φ τ
    aesop
  · intro ψ W M w
    simp only [evaluate, Xset, conEval, List.mem_append, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, and_congr_left_iff]
    intro w_sign
    constructor
    · intro lhs δ δ_in
      aesop
    · rintro rhs φ (φ_in_F | ⟨δ,δ_in,def_φ⟩)
      · rw [F_mem_iff_neg α ℓ φ] at φ_in_F
        rcases φ_in_F with ⟨τ, τ_in, φ_def, not_ℓ_τ⟩
        subst φ_def
        simp_all [signature, conEval]
        specialize w_sign (~τ) τ
        aesop
      · aesop

theorem guardToStar (x : Nat) β χ0 χ1 ρ ψ
    (x_notin_beta : Sum.inl x ∉ β.voc)
    (beta_equiv : (⌈β⌉·x) ≡ (((·x) ⋀ χ0) ⋁ χ1))
    (rho_imp_repl : ρ ⊨ (repl_in_F x ρ) (χ0 ⋁ χ1))
    (rho_imp_psi : ρ ⊨ ψ)
  : ρ ⊨ ⌈(∗β)⌉ψ := by
  -- "The key observation in this proof is the following:"
  have threepointsix :
       ∀ W M (w v : W), (M,w) ⊨ ρ → relate M β w v → (M,v) ⊨ ρ := by
    intro W M w v w_rho w_β_v
    have : (M,w) ⊨ ⌈β⌉ρ := by
      have by_ass : (M,w) ⊨ (repl_in_F x ρ) (χ0 ⋁ χ1) := by
        apply rho_imp_repl
        · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
          exact w_rho
        · simp
      have obvious : (M,w) ⊨ (repl_in_F x ρ) (·x) := by simpa
      have : (M,w) ⊨ (repl_in_F x ρ) (((·x) ⋀ χ0) ⋁ χ1) := by
        simp [evaluate, modelCanSemImplyForm] at *
        tauto
      -- Now we want to "rewrite" with beta_equiv.
      have := repl_in_F_equiv x ρ beta_equiv
      simp only [repl_in_F, beq_self_eq_true, reduceIte, Formula.or] at this
      have nox : repl_in_P x ρ β = β := repl_in_P_non_occ_eq x_notin_beta
      rw [nox] at this
      rw [equiv_iff _ _ this]
      simp_all
    -- It is then immediate...
    simp only [modelCanSemImplyForm, evaluatePoint, evaluate] at this
    exact this v w_β_v -- This finishes the proof of (46).
  -- To see how the Lemma follows from this...
  intro W M w
  simp only [List.mem_singleton, forall_eq, evaluate, relate]
  intro w_rho v w_bS_v
  induction w_bS_v using Relation.ReflTransGen.head_induction_on
  · apply rho_imp_psi <;> simp_all
  case head u1 u2 u1_b_u2 _ IH =>
    exact IH (threepointsix W M u1 u2 w_rho u1_b_u2)

/-- Show "suffices" part outside, to use `localBoxTruth` for star case in `localBoxTruthI`. -/
theorem localBoxTruth_connector γ ψ :
    (goal : ∀ ℓ, (⌈γ⌉ψ) ⋀ signature γ ℓ ≡ Con (Xset γ ℓ ψ) ⋀ signature γ ℓ) →
    (⌈γ⌉ψ) ≡ dis ( (allTP γ).map (fun ℓ => Con (Xset γ ℓ ψ)) ) := by
  -- By the properties of the signature formulas clearly ;-)
  -- `localBoxTruthI` suffices to prove `localBoxTruth`.
  intro goal W M w
  constructor
  · intro w_γψ
    rw [disEval]
    -- decidable semantics would be nice, but here we can also
    -- accept something noncomputable, as we only want proof :-)
    have := Classical.propDecidable
     -- get a test profile ℓ from the model:
    let ℓ : TP γ := fun ⟨τ,_⟩ => decide (evaluate M w τ)
    have ℓ_in : ℓ ∈ allTP γ := by
      unfold ℓ;
      simp only [allTP, List.mem_map, List.mem_sublists];
      use ((testsOfProgram γ).filter (fun τ => evaluate M w τ))
      simp only [List.filter_sublist, true_and]
      apply funext
      simp only [Subtype.forall]
      intro τ τ_in
      simp [List.mem_filter]
      tauto
    have := goal ℓ W M w -- using the claim proven by induction
    simp_all only [evaluate, implies_true, true_and, iff_and_self, List.mem_map,
      exists_exists_and_eq_and]
    refine ⟨ℓ, ℓ_in, ?_⟩
    apply this
    unfold ℓ
    simp_all only [signature, conEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
      forall_exists_index, decide_eq_true_eq, List.map_subtype, List.unattach_attach, and_imp,
      forall_apply_eq_imp_iff₂]
    intro τ _
    split_ifs <;> simp_all
  · intro w_Cons
    rw [disEval] at w_Cons
    rcases w_Cons with ⟨φ, φ_in, w_Xℓ⟩
    simp only [List.mem_map] at φ_in
    rcases φ_in with ⟨ℓ, _, def_φ⟩
    subst def_φ
    have := Classical.propDecidable
    -- again we get a test profile ℓ from the model:
    let ℓ' : TP γ := fun ⟨τ,_⟩ => decide (evaluate M w τ)
    have w_Xℓ' : evaluate M w (Con (Xset γ ℓ' ψ)) := by
      simp only [Xset, conEval, List.mem_append, List.mem_map]
      intro φ φ_in
      cases φ_in
      case inl φ_in_Fℓ' =>
        simp only [F_mem_iff_neg _ ℓ' φ, exists_and_left] at φ_in_Fℓ'
        rcases φ_in_Fℓ' with ⟨τ, φ_def, τ_in, ℓ'_τ_false⟩
        unfold ℓ' at ℓ'_τ_false
        simp_all
      case inr φ_in_Pℓ' =>
        rcases φ_in_Pℓ' with ⟨δ, δ_in_P, def_φ⟩
        simp_all only [Xset, conEval, List.mem_append, List.mem_map]
        apply w_Xℓ φ
        right
        use δ
        simp_all only [and_true]
        apply P_monotone γ ℓ' ℓ ?_ δ δ_in_P
        intro τ ℓ_τ
        by_contra hyp
        absurd ℓ_τ
        simp only [Bool.not_eq_true] at *
        unfold ℓ'
        simp only [decide_eq_false_iff_not]
        have := w_Xℓ (~τ)
        simp only [evaluate] at this
        apply this
        left
        rw [F_mem_iff_neg]
        tauto
    have : evaluate M w ((⌈γ⌉ψ)⋀signature γ ℓ') := by
      apply (goal ℓ' W M w).2
      simp only [evaluate]
      constructor
      · assumption
      · simp_all [signature, conEval]
        aesop
    simp_all

set_option maxHeartbeats 2000000 in -- for simp timeouts (also triggering kernel error?)
/-- Induction claim for `localBoxTruth`. -/
theorem localBoxTruthI γ ψ (ℓ : TP γ) :
    (⌈γ⌉ψ) ⋀ signature γ ℓ ≡ Con (Xset γ ℓ ψ) ⋀ signature γ ℓ := by
  intro W M w
  cases γ
  case atom_prog a =>
    simp_all [testsOfProgram, signature, Xset, P, F]
  case test τ =>
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩ )
    · simp_all [testsOfProgram, signature, Xset, P, F]
    · simp_all [testsOfProgram, signature, Xset, P, F]
  case union α β =>
    have IHα := localBoxTruthI α ψ ℓ W M w
    have IHβ := localBoxTruthI β ψ ℓ W M w
    simp only [evaluate, and_congr_left_iff, relate] at *
    intro w_sign_ℓ
    specialize IHα ?_
    · simp_all [signature, conEval, testsOfProgram]
    specialize IHβ ?_
    · simp_all [signature, conEval, testsOfProgram]
    -- rewrite using semantics of union and the two IH:
    have : (∀ (v : W), relate M α w v ∨ relate M β w v → evaluate M v ψ)
        ↔ ((∀ (v : W), relate M α w v → evaluate M v ψ)
         ∧ (∀ (v : W), relate M β w v → evaluate M v ψ)) := by aesop
    rw [this, IHα, IHβ]
    clear this IHα IHβ
    -- signature is true, so we can add it for free:
    have : ∀ φ, evaluate M w φ
              ↔ evaluate M w (φ ⋀ signature (α⋓β) ℓ) := by simp_all
    rw [this (Con (Xset (α⋓β) ℓ ψ))]
    clear this
    -- using part (3) of Lemma:
    have := (boxHelperTP (α⋓β) ℓ).2.2 ψ W M w
    rw [this]
    clear this
    simp only [P, evaluate]
    constructor
    · intro lhs
      simp only [conEval] at lhs
      constructor
      · rw [conEval]
        intro φ φ_in
        simp only [List.mem_map, List.mem_union_iff] at φ_in
        rcases φ_in with ⟨δ, δ_in, def_φ⟩
        subst def_φ
        cases δ_in
        · apply lhs.1
          simp only [Xset, List.mem_append, List.mem_map]
          right
          use δ
        · apply lhs.2
          simp only [Xset, List.mem_append, List.mem_map]
          right
          use δ
      · assumption
    · intro rhs
      rw [conEval] at rhs
      constructor -- α and β parts, analogous
      · simp only [Xset, conEval, List.mem_append, List.mem_map]
        intro φ φ_in
        cases φ_in
        case inl φ_in_F =>
          rw [F_mem_iff_neg α ℓ φ] at φ_in_F
          rcases φ_in_F with ⟨τ, τ_in, def_φ, not_ℓ_τ⟩
          simp only [signature, conEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
            forall_exists_index] at w_sign_ℓ
          apply w_sign_ℓ _ τ
          · simp_all
          · simp_all [testsOfProgram]
        case inr φ_from_P =>
          rcases φ_from_P with ⟨δ, bla, def_φ⟩
          apply rhs.1 φ
          simp only [List.mem_map, List.mem_union_iff]
          use δ
          tauto
      · simp only [Xset, conEval, List.mem_append, List.mem_map]
        intro φ φ_in
        cases φ_in
        case inl φ_in_F =>
          rw [F_mem_iff_neg β ℓ φ] at φ_in_F
          rcases φ_in_F with ⟨τ, τ_in, def_φ, not_ℓ_τ⟩
          simp only [signature, conEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
            forall_exists_index] at w_sign_ℓ
          apply w_sign_ℓ _ τ
          · simp_all
          · simp_all [testsOfProgram]
        case inr φ_from_P =>
          rcases φ_from_P with ⟨δ, bla, def_φ⟩
          apply rhs.1 φ
          simp only [List.mem_map, List.mem_union_iff]
          use δ
          tauto
  case sequence α β =>
    have IHα := localBoxTruthI α (⌈β⌉ψ) ℓ W M w
    have IHβ := localBoxTruthI β ψ ℓ W M w -- ??
    simp only [evaluate, relate, forall_exists_index, and_imp, and_congr_left_iff] at *
    intro w_sign_ℓ
    specialize IHα ?_
    · simp_all [signature, conEval, testsOfProgram]
    specialize IHβ ?_
    · simp_all [signature, conEval, testsOfProgram]
    -- only rewriting with IHα here, but not yet IHβ
    have : (∀ (v x : W), relate M α w x → relate M β x v → evaluate M v ψ)
          ↔ ∀ (v : W), relate M α w v → ∀ (v_1 : W), relate M β v v_1 → evaluate M v_1 ψ := by
      clear IHα IHβ
      aesop
    rw [this, IHα]
    clear this IHα
    constructor
    · intro lhs
      rw [conEval]
      simp_all only [signature, testsOfProgram, List.attach_append, List.map_append, List.map_map,
        conEval, List.mem_append, List.mem_map, List.mem_attach, Function.comp_apply, true_and,
        Subtype.exists, Xset, F, P, List.mem_union_iff, List.mem_filter, bne_iff_ne, ne_eq,
        List.mem_ite_nil_right]
      rintro φ ((φ_in_Fα|φ_in_Fβ) | ⟨δ, ⟨(δ_from_Pα|δ_from_Pβ), def_φ⟩⟩)
      · tauto
      · rw [F_mem_iff_neg β ℓ φ] at φ_in_Fβ
        rcases φ_in_Fβ with ⟨τ, τ_in, def_φ, not_ℓ_τ⟩
        apply w_sign_ℓ φ
        subst def_φ
        simp_all only [testsOfProgram]
        right
        use τ, τ_in
        simp_all
      · subst def_φ
        apply lhs
        right
        rcases δ_from_Pα with ⟨δ_α, bla, def_δ⟩
        use δ_α
        subst def_δ
        simp_all [boxes_append]
      · subst def_φ
        cases em ([] ∈ P α ℓ)
        · simp_all only [true_and]
          apply IHβ.1 ?_ (⌈⌈δ⌉⌉ψ) <;> clear IHβ
          · right; aesop
          · have := lhs (⌈β⌉ψ)
            simp only [evaluate] at this; apply this; clear this -- sounds like daft punk ;-)
            right
            use []
            simp_all
        · simp_all
    · intro rhs
      rw [conEval]
      simp_all only [signature, testsOfProgram, List.attach_append, List.map_append, List.map_map,
        conEval, List.mem_append, List.mem_map, List.mem_attach, Function.comp_apply, true_and,
        Subtype.exists, Xset, F, P, List.mem_union_iff, List.mem_filter, bne_iff_ne, ne_eq,
        List.mem_ite_nil_right]
      rintro φ (φ_in_Fα|⟨δ, φ_in_Pα, def_φ⟩)
      · tauto
      · subst def_φ
        cases em (δ = [])
        · simp_all only [Formula.boxes_nil, evaluate] -- uses IHβ
          clear IHβ
          rintro φ ((φ_in_Fβ) | ⟨δ, ⟨(δ_from_Pβ), def_φ⟩⟩)
          · apply rhs
            simp_all
          · subst_eqs
            apply rhs
            right
            use δ
            simp_all
        · apply rhs
          right
          use δ ++ [β]
          simp [boxes_append]
          cases em ([] ∈ P α ℓ)
          · simp_all
          · simp_all
  case star β =>
    let ρ := dis ((allTP (∗β)).map (fun ℓ => Con (Xset (∗β) ℓ ψ)))
    suffices goal : (⌈∗β⌉ψ) ≡ ρ by
      specialize goal W M w
      simp only [evaluate, relate] at goal
      constructor
      · intro lhs
        simp only [evaluate, relate] at lhs
        simp only [evaluate]
        constructor
        · unfold ρ at goal
          have := goal.1 lhs.1
          rw [disEval] at this
          simp only [List.mem_map, exists_exists_and_eq_and] at this
          rcases this with ⟨ℓ', _, w_Xℓ'⟩
          clear goal ρ
          simp only [Xset, F, P, List.cons_union, List.nil_union, List.mem_map, List.mem_filter,
            bne_iff_ne, ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, exists_const,
            not_false_eq_true, List.insert_of_not_mem, List.map_cons, Formula.boxes_nil,
            List.map_map, conEval, List.mem_append, List.mem_cons, Function.comp_apply] at *
          rintro f (f_in_Fβ|(f_eq_ψ|f_from_Pβ))
          · simp only [signature, conEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
              forall_exists_index] at lhs
            have := lhs.2 f
            clear lhs
            rw [F_mem_iff_neg] at f_in_Fβ
            simp only [exists_and_left] at f_in_Fβ
            rcases f_in_Fβ with ⟨τ, f_def, ⟨τ_in, bla⟩⟩
            apply this τ <;> simp_all [testsOfProgram]
          · apply w_Xℓ'
            right
            left
            assumption
          · rcases f_from_Pβ with ⟨δ, δ_in, def_f⟩
            apply w_Xℓ'
            right
            right
            use δ
            constructor
            · cases em (δ = [])
              · subst_eqs
                simp_all
              · simp_all only [not_false_eq_true, and_true]
                have := P_monotone β ℓ ℓ' -- or flip order?
                simp only [Subtype.forall] at this
                apply this _ _ δ_in
                clear this
                -- remains to show that ℓ τ → ℓ' τ
                -- this might have been easier if F would be same as σ.
                -- but we can do it.
                intro τ τ_in ℓ_τ
                have := lhs.2
                simp only [signature, conEval, List.mem_map, List.mem_attach, true_and,
                  Subtype.exists, forall_exists_index] at this
                specialize this τ τ (by simpa [testsOfProgram])
                simp_all only [ite_true, true_implies]
                by_contra hyp
                absurd this
                specialize w_Xℓ' (~τ)
                simp only [evaluate] at w_Xℓ'
                apply w_Xℓ'
                left
                rw [F_mem_iff_neg]
                simp_all
            · assumption
        · exact lhs.2
      · intro rhs -- the easy direction
        simp only [evaluate] at rhs
        simp only [evaluate, relate]
        constructor
        · rw [goal]
          unfold ρ
          rw [disEval]
          use Con (Xset (∗β) ℓ ψ)
          simp_all only [List.mem_map, and_true]
          use ℓ -- seems to be only place where we actually use the given ℓ
          simp only [and_true]
          exact allTP_mem ℓ
        · exact rhs.2
    -- now show `goal`
    -- Notes discuss IHβ_thm here, we do it below.
    clear ℓ -- goal does not depend on given ℓ and given model
    -- switching model, but that seems okay
    clear W M w
    intro W M w
    -- Left to right, relatively short in the notes ;-)
    -- We show left_to_right as a claim because we need left_to_right for right to left.
    have left_to_right : (⌈∗β⌉ψ) ⊨ ρ := by
      intro W M w
      suffices step : ∀ ℓ, (⌈∗β⌉ψ) ⋀ signature (∗β) ℓ ⊨ Con ((P (∗β) ℓ).map fun αs => ⌈⌈αs⌉⌉ψ) by
        have := Classical.propDecidable
        let ℓ' : TP (∗β) := fun ⟨τ,_⟩ => decide (evaluate M w τ)
        intro w_bSpsi
        unfold ρ
        simp only [List.mem_singleton, forall_eq, disEval, List.mem_map, exists_exists_and_eq_and]
        use ℓ'
        constructor
        · exact allTP_mem ℓ'
        · simp only [Xset, conEval, List.mem_append, List.mem_map]
          rintro f (f_in_F| ⟨δ, δ_in, def_f⟩)
          · simp only [F_mem_iff_neg, exists_and_left] at f_in_F
            unfold ℓ' at f_in_F
            aesop
          · subst def_f
            specialize step ℓ' W M w
            simp only [List.mem_singleton, forall_eq] at step
            rw [conEval] at step
            simp only [evaluate, relate, signature, conEval, List.mem_map, List.mem_attach,
              true_and, Subtype.exists, forall_exists_index, and_imp,
              forall_apply_eq_imp_iff₂] at step
            apply step <;> aesop
      intro ℓ W M w
      simp only [List.mem_singleton, forall_eq]
      intro hyp
      rw [conEval]
      intro f f_in
      simp only [List.mem_map] at f_in
      rcases f_in with ⟨αs, αs_in, def_f⟩
      subst def_f
      cases em (αs = [])
      · subst_eqs
        simp only [Formula.boxes, List.foldr_nil]
        simp only [evaluate, relate] at hyp
        apply hyp.1
        exact Relation.ReflTransGen.refl
      · simp only [P, List.cons_union, List.nil_union, List.mem_map, List.mem_filter, bne_iff_ne,
        ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, exists_const,
        not_false_eq_true, List.insert_of_not_mem, List.mem_cons] at αs_in
        simp_all only [evaluate, relate, false_or]
        rcases αs_in with ⟨δ, δ_in, def_αs⟩
        subst def_αs
        -- Notes now prove a ⊨ but we prove → to avoid a model switch here.
        have : evaluate M w (⌈β⌉⌈∗β⌉ψ) → evaluate M w (⌈⌈δ⌉⌉⌈∗β⌉ψ) := by
          have IHβ_thm := localBoxTruth_connector _ _ (localBoxTruthI β (⌈∗β⌉ψ))
          have := (IHβ_thm  W M w).1
          clear IHβ_thm
          simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true,
            evaluate, relate, Xset, disEval, List.mem_map, exists_exists_and_eq_and, conEval,
            List.mem_append] at *
          intro hyp2
          specialize this hyp2
          rcases this with ⟨ℓ', _, w_Xℓ'⟩
          apply w_Xℓ'
          right
          use δ
          rcases δ_in with ⟨δ_in, _⟩
          simp_all only [and_true]
          apply P_monotone β ℓ ℓ' -- γ ℓ' ℓ ?_ δ δ_in_P
          · simp only [Subtype.forall]
            -- again remains to show that ℓ τ → ℓ' τ
            intro τ τ_in ℓ_τ
            by_contra wrong
            absurd w_Xℓ'
            simp only [not_forall, exists_prop]
            use ~τ
            rw [F_mem_iff_neg]
            constructor
            · left
              simp_all
            · have := hyp.2
              simp only [signature, conEval, List.mem_map, List.mem_attach, true_and,
                Subtype.exists, forall_exists_index, Bool.not_eq_true, evaluate, not_not] at *
              specialize this τ τ τ_in
              simp only [ite_eq_left_iff, Bool.not_eq_true] at this
              apply this
              intro
              simp_all
          · exact δ_in
        simp only [boxes_append, Formula.boxes_cons, Formula.boxes_nil]
        simp only [evaluate, relate] at this
        apply this
        intro v w_β_v u v_βS_u
        apply hyp.1
        apply Relation.ReflTransGen.head w_β_v v_βS_u
    constructor
    · specialize left_to_right W M w
      simp only [List.mem_singleton, forall_eq] at left_to_right
      exact left_to_right
    · -- Right to left, "more work is required"
      let x : Nat := freshVarProg β
      have x_not_in_β : Sum.inl x ∉ β.voc := by apply freshVarProg_is_fresh
      let φ ℓ := Con ((P β ℓ).map (fun αs => ⌈⌈αs⌉⌉·x))
      let T0 := (allTP β).filter (fun ℓ => [] ∈ P β ℓ)
      let T1 := (allTP β).filter (fun ℓ => [] ∉ P β ℓ)
      let φ' ℓ := Con (((P β ℓ).filter (fun αs => αs ≠ [])).map (fun αs => ⌈⌈αs⌉⌉·x))
      let χ0 : Formula := dis (T0.map (fun ℓ => Con (F _ ℓ) ⋀ φ' ℓ))
      let χ1 : Formula := dis (T1.map (fun ℓ => Con (F _ ℓ) ⋀ φ' ℓ))
      have := guardToStar x β χ0 χ1 ρ ψ x_not_in_β ?_ ?_ ?_ W M w
      · simp only [List.mem_singleton, forall_eq] at this
        exact this
      all_goals
        clear W M w
        intro W M w
      -- remaining goals are the conditions of `guardToStar`
      · -- ⌈β⌉x ≡ (x⋀χ0)⋁χ1
        have IHβ_thm := localBoxTruth_connector _ _ (localBoxTruthI β (·x)) W M w
        rw [IHβ_thm]
        clear IHβ_thm
        simp only [Xset, evalDis, disEval, List.mem_map, exists_exists_and_eq_and, conEval,
          List.mem_append, evaluate]
        constructor
        · rintro ⟨ℓ, ℓ_in, w_Xβ⟩
          -- now need to choose x⋀χ0 or χ1
          cases em ([] ∈ P β ℓ)
          case inl empty_in_Pβ =>
            left -- choose x⋀χ0
            constructor
            · specialize w_Xβ (·x) (Or.inr ⟨[], empty_in_Pβ, by simp [Formula.boxes]⟩)
              simp only [evaluate] at w_Xβ
              exact w_Xβ
            · unfold χ0 T0 φ'
              simp only [ne_eq, decide_not, disEval, List.mem_map, List.mem_filter,
                decide_eq_true_eq, exists_exists_and_eq_and, evaluate, conEval,
                Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, forall_exists_index,
                and_imp]
              use ℓ
              simp_all only [and_self, true_or, implies_true, true_and]
              intro f δ δ_in _ def_f
              apply w_Xβ
              right
              aesop
          · right -- choose χ1
            unfold χ1 T1 φ'
            simp only [ne_eq, decide_not, disEval, List.mem_map, List.mem_filter,
              Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
              exists_exists_and_eq_and, evaluate, conEval, forall_exists_index, and_imp]
            use ℓ
            simp_all only [not_false_eq_true, and_self, true_or, implies_true, true_and]
            intro f δ δ_in _ def_f
            apply w_Xβ
            right
            aesop
        · rintro (⟨w_c, w_χ0⟩ | w_χ1)
          · unfold χ0 T0 φ' at w_χ0
            simp only [ne_eq, decide_not, disEval, List.mem_map, List.mem_filter, decide_eq_true_eq,
              exists_exists_and_eq_and, evaluate, conEval, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not, forall_exists_index, and_imp] at w_χ0
            rcases w_χ0 with ⟨ℓ, w_Xℓ⟩
            use ℓ
            simp_all only [true_and]
            rintro φ (φ_in_Fβ | ⟨δ, δ_in, def_φ⟩)
            · aesop
            · subst def_φ
              cases em (δ = [])
              · simp_all
              case inr δ_not_empty =>
                apply w_Xℓ.2.2 _ _ δ_in δ_not_empty
                simp [Formula.boxes]
          · unfold χ1 T1 φ' at w_χ1
            simp only [ne_eq, decide_not, disEval, List.mem_map, List.mem_filter,
              Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
              exists_exists_and_eq_and, evaluate, conEval, forall_exists_index, and_imp] at w_χ1
            rcases w_χ1 with ⟨ℓ, w_Xℓ⟩
            use ℓ
            constructor
            · apply allTP_mem
            · rintro φ (φ_in_Fβ | ⟨δ, δ_in, def_φ⟩)
              · apply w_Xℓ.2.1 _ φ_in_Fβ
              · subst def_φ
                cases em (δ = [])
                · simp_all
                case inr δ_not_empty =>
                  apply w_Xℓ.2.2 _ _ δ_in δ_not_empty
                  simp [Formula.boxes]
      · -- ρ ⊨ (χ0⋁χ1) [ρ/x]
        simp only [List.mem_singleton, forall_eq]
        intro w_ρ
        unfold ρ at w_ρ
        simp only [disEval, List.mem_map, exists_exists_and_eq_and] at w_ρ
        rcases w_ρ with ⟨ℓ, _, w_Xℓ⟩ -- here we get ℓ
        simp only [repl_in_or, evalDis]
        simp only [Xset, conEval, List.mem_append, List.mem_map] at w_Xℓ
        unfold χ0 χ1 T0 T1 φ'
        clear χ0 χ1 T0 T1 φ φ'
        cases em ([] ∈ P β ℓ) -- based on this, go left or right
        case inl empty_in_Pβ =>
          left
          simp_all only [ne_eq, decide_not, repl_in_dis, List.map_map, disEval, List.mem_map,
            List.mem_filter, decide_eq_true_eq, Function.comp_apply, repl_in_F, repl_in_Con,
            exists_exists_and_eq_and, evaluate, conEval, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          use ℓ
          simp_all only [and_true]
          constructor
          · apply allTP_mem
          · constructor
            · intro φ φ_in_Fβ
              apply w_Xℓ
              left
              simp only [F]
              convert φ_in_Fβ
              -- now we use that x ∉ β implies x ∉ φ ∈ Fβ
              apply repl_in_F_non_occ_eq
              apply keepFreshF β ℓ x_not_in_β
              exact φ_in_Fβ
            · intro f δ δ_in_Pβ δ_not_empty def_f
              subst def_f
              have : repl_in_F x ρ (⌈⌈δ⌉⌉·x) = ⌈⌈δ⌉⌉ρ :=
                repl_in_boxes_non_occ_eq_pos _ (keepFreshP β ℓ x_not_in_β δ δ_in_Pβ)
              rw [this]; clear this
              specialize w_Xℓ (⌈⌈δ ++ [∗β]⌉⌉ψ) (Or.inr ?_)
              · use δ ++ [∗β]
                simp [P, List.mem_filter]
                simp_all only [not_false_eq_true, and_self, x]
              simp [boxes_append] at w_Xℓ
              -- need ⌈∗β⌉ψ ⊨ ρ now, and that is the other direction we have already shown :-)
              specialize left_to_right W M
              simp [evalBoxes] at left_to_right w_Xℓ
              simp [evalBoxes]
              aesop
        case inr empty_not_in_Pβ =>
          right
          -- exactly the same as inl case!
          simp_all only [ne_eq, decide_not, repl_in_dis, List.map_map, disEval, List.mem_map,
            List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
            Function.comp_apply, repl_in_F, repl_in_Con, exists_exists_and_eq_and, evaluate,
            conEval, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          use ℓ
          simp_all only [not_false_eq_true, and_true]
          constructor
          · apply allTP_mem
          · constructor
            · intro φ φ_in_Fβ
              apply w_Xℓ
              left
              simp only [F]
              convert φ_in_Fβ
              -- now we use that x ∉ β implies x ∉ φ ∈ Fβ
              apply repl_in_F_non_occ_eq
              apply keepFreshF β ℓ x_not_in_β
              exact φ_in_Fβ
            · intro f δ δ_in_Pβ δ_not_empty def_f
              subst def_f
              have : repl_in_F x ρ (⌈⌈δ⌉⌉·x) = ⌈⌈δ⌉⌉ρ :=
                repl_in_boxes_non_occ_eq_pos _ (keepFreshP β ℓ x_not_in_β δ δ_in_Pβ)
              rw [this]; clear this
              specialize w_Xℓ (⌈⌈δ ++ [∗β]⌉⌉ψ) (Or.inr ?_)
              · use δ ++ [∗β]
                simp [P, List.mem_filter]
                simp_all only [not_false_eq_true, and_self, x]
              simp [boxes_append] at w_Xℓ
              -- need ⌈∗β⌉ψ ⊨ ρ which is the other direction we have already shown :-)
              specialize left_to_right W M
              simp [evalBoxes] at left_to_right w_Xℓ
              simp [evalBoxes]
              aesop
      · -- ρ ⊨ ψ
        unfold ρ
        simp only [Xset, P, List.cons_union, List.nil_union, List.mem_map, List.mem_filter,
          bne_iff_ne, ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, exists_const,
          not_false_eq_true, List.insert_of_not_mem, List.map_cons, Formula.boxes_nil, List.map_map,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq, disEval, exists_exists_and_eq_and,
          conEval, List.mem_append, Function.comp_apply, forall_exists_index, and_imp]
        intro ℓ_whatever _ hyp
        apply hyp
        right
        left
        rfl

theorem localBoxTruth γ ψ : (⌈γ⌉ψ) ≡ dis ( (allTP γ).map (fun ℓ => Con (Xset γ ℓ ψ)) ) :=
  localBoxTruth_connector γ ψ (localBoxTruthI γ ψ)

theorem existsBoxFP γ (v_γ_w : relate M γ v w) (ℓ : TP γ) (v_conF : (M, v) ⊨ Con (F γ ℓ)) :
    ∃ δ ∈ P γ ℓ, relateSeq M δ v w := by
  cases γ
  case atom_prog =>
    simp only [relate, F, List.empty_eq, Con.eq_1, Formula.insTop, P, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_left, relateSeq, exists_eq_right] at *
    exact v_γ_w
  case test τ =>
    simp only [relate] at v_γ_w
    rcases v_γ_w with ⟨v_is_w, v_τ⟩
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩ )
    all_goals
      simp_all [modelCanSemImplyForm, evaluatePoint, F, P, relateSeq, testsOfProgram]
  case union α β =>
    simp only [relate] at v_γ_w
    cases v_γ_w
    case inl v_α_w =>
      have v_Fℓα : evaluate M v (Con (F α ℓ)) := by
        simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHα := existsBoxFP α v_α_w ℓ v_Fℓα -- using coercion from above :-)
      rcases IHα with ⟨δ, _⟩
      use δ
      simp_all [P]
    case inr v_β_w =>
      have v_Fℓβ : evaluate M v (Con (F β ℓ)) := by
        simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHβ := existsBoxFP β v_β_w ℓ v_Fℓβ -- using coercion from above :-)
      rcases IHβ with ⟨δ, _⟩
      use δ
      simp_all [P]
  case sequence α β =>
    simp only [relate] at v_γ_w
    rcases v_γ_w with ⟨u, v_α_u, u_β_w⟩
    have v_Fℓα : evaluate M v (Con (F α ℓ)) := by
      simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
    have IHα := existsBoxFP α v_α_u ℓ v_Fℓα -- using coercion from above :-)
    rcases IHα with ⟨δ, ⟨δ_in, v_δ_u⟩⟩
    -- "We make a further case distinction"
    cases em (δ = [])
    case inl hyp =>
      subst hyp
      simp only [relateSeq] at v_δ_u
      subst v_δ_u
      rename relate M β v w => v_β_w
      have v_Fℓβ : evaluate M v (Con (F β ℓ)) := by
        simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHβ := existsBoxFP β v_β_w ℓ v_Fℓβ -- using coercion from above :-)
      rcases IHβ with ⟨η, ⟨η_in, v_η_w⟩⟩
      use η
      simp_all [P]
    case inr _ =>
      use δ ++ [β]
      simp_all only [P, List.mem_union_iff, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq,
        List.append_cancel_right_eq, exists_eq_right, not_false_eq_true, and_self,
        List.mem_ite_nil_right, true_or, relateSeq_append, relateSeq, true_and]
      use u
  case star β =>
    simp only [relate] at v_γ_w
    cases ReflTransGen.cases_tail_eq_neq v_γ_w
    case inl v_is_w =>
      subst v_is_w
      use []
      simp_all [P,relateSeq]
    case inr hyp =>
      rcases hyp with ⟨v_neq_w, ⟨u, v_neq_u, v_β_u, u_βS_w⟩⟩
      have v_Fℓβ : evaluate M v (Con (F β ℓ)) := by
        simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHβ := existsBoxFP β v_β_u ℓ v_Fℓβ
      rcases IHβ with ⟨δ, ⟨δ_in, v_δ_w⟩⟩
      have claim : δ ≠ [] := by by_contra hyp; subst hyp; simp_all [relateSeq];
      use δ ++ [∗β]
      simp_all only [ne_eq, P, List.cons_union, List.nil_union, List.mem_map, List.mem_filter,
        bne_iff_ne, List.append_eq_nil_iff, List.cons_ne_self, and_false, exists_const,
        not_false_eq_true, List.insert_of_not_mem, List.mem_cons, and_self,
        List.append_cancel_right_eq, exists_eq_right, or_true, relateSeq_append, relateSeq, relate,
        true_and]
      use u
