import Mathlib.Tactic.Linarith

import Pdl.Substitution
import Pdl.Star

/-! # Local Diamond Unfolding (Section 3.2 and 3.3) -/

/-! ## Diamonds: H, Y and Φ_⋄ -/

-- TODO: change map + flatten to flatmap
def H : Program → List (List Formula × List Program)
| ·a => [ ([], [·a]) ]
| ?'τ => [ ([τ], []) ]
| α ⋓ β => H α ∪ H β
| α;'β => ((H α).map (fun ⟨F,δ⟩ =>
            if δ = []
              then ((H β).map (fun ⟨G,δ'⟩ => [⟨F ∪ G, δ'⟩])).flatten
              else [⟨F, δ ++ [β]⟩])
          ).flatten
| ∗α => [ (∅,[]) ] ∪ ((H α).map (fun (F,δ) => if δ = [] then [] else [(F, δ ++ [∗α])])).flatten

/-- Like `H`, but applied to a whole list of programs.
This is used to deal with loaded diamonds. -/
def Hl : List Program → List (List Formula × List Program)
| [] => [([],[])]
| [α] => H α
| α :: rest => (H α).flatMap (fun ⟨F,δ⟩ => -- inspired by `;` case of `H`
            if δ = []
              then ((Hl rest).flatMap (fun ⟨G,δ'⟩ => [⟨F ∪ G, δ'⟩]))
              else [⟨F, δ ++ rest⟩])

@[simp]
lemma Hl_singleton : Hl [α] = H α := by simp [Hl]

@[simp]
lemma Hl_atomic_cons : Hl (·a :: αs) =  [ ([], ((·a : Program) :: αs)) ] := by
  unfold Hl
  cases αs <;> simp_all [H]

theorem relateSeq_H_imp_relate {X : List Formula} {δ : List Program}
  : (X, δ) ∈ H α → (M, w) ⊨ Con X →  relateSeq M δ w v → relate M α w v :=
  let me := (evaluate M w <| Con .)
  let mr := (relateSeq M . w v)
  fun in_H ev rel => match α with
  | ·_ =>
    let hδ := congr_arg mr (Prod.eq_iff_fst_eq_snd_eq.mp (List.eq_of_mem_singleton in_H)).2
    relateSeq_singleton.mp (cast hδ rel)

  | ?'_ =>
    let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton in_H
    ⟨hδ.subst (motive := mr) rel, hX.subst (motive := me) ev⟩

  | _⋓_ => (List.mem_union_iff.mp in_H).elim
    (.inl <| relateSeq_H_imp_relate . ev rel)
    (.inr <| relateSeq_H_imp_relate . ev rel)

  | _;'_ =>
    let ⟨⟨_, δα⟩, in_Hα, h⟩ := List.exists_of_mem_flatMap in_H
    if c : δα = []
      then
        let h := (if_pos c).subst h
        let ⟨_, in_Hβ, h⟩ := List.exists_of_mem_flatMap h
        let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton <| h
        let relα := c.symm.subst (motive := (relateSeq _ . _ _)) <| relateSeq_nil.mpr rfl
        let relβ := hδ.subst (motive := mr) rel
        let ev := hX.subst (motive := me) ev
        let evα := conEval.mpr (List.forall_mem_union.mp <| conEval.mp ev).1
        let evβ := conEval.mpr (List.forall_mem_union.mp <| conEval.mp ev).2
        ⟨w, relateSeq_H_imp_relate in_Hα evα relα, relateSeq_H_imp_relate in_Hβ evβ relβ⟩
      else
        let h := (if_neg c).subst h
        let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton <| h
        let ⟨u, relα, relβ⟩ :=  relateSeq_append.mp <| hδ.subst (motive := mr) rel
        let evα := hX.subst (motive := me) ev
        ⟨u, relateSeq_H_imp_relate in_Hα evα relα, relateSeq_singleton.mp relβ⟩

  | ∗_ =>
    (List.mem_union_iff.mp in_H).elim (
      let ⟨_, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton .
      (relateSeq_nil.mp <| hδ.subst (motive := mr) rel) ▸ .refl
    ) (
      let ⟨_, in_Hα, h⟩ := List.exists_of_mem_flatMap .
      let ⟨_, h⟩ := List.mem_ite_nil_left.mp h
      let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton h
      let evα := hX.subst (motive := me) ev
      let ⟨_, relα, relαS⟩ :=  relateSeq_append.mp <| hδ.subst (motive := mr) rel
      let relα := relateSeq_H_imp_relate in_Hα evα relα
      let relαS := relateSeq_singleton.mp relαS
      .head relα relαS
    )


/-- A test formula coming from `H` comes from a test in the given program. -/
theorem H_mem_test α φ {Fs δ} (in_H : ⟨Fs, δ⟩ ∈ H α) (φ_in_Fs: φ ∈ Fs) :
    ∃ τ, ∃ (_ : τ ∈ testsOfProgram α), φ = τ := by
  cases α
  case atom_prog =>
    simp_all only [H, List.mem_singleton, Prod.mk.injEq, testsOfProgram, List.not_mem_nil,
      IsEmpty.exists_iff, exists_const]
  case union α β =>
    simp_all only [H, List.mem_union_iff, testsOfProgram, List.mem_append, exists_prop,
      exists_eq_right']
    rcases in_H with in_Hα | in_Hβ
    · have IHα := H_mem_test α φ in_Hα φ_in_Fs
      aesop
    · have IHβ := H_mem_test β φ in_Hβ φ_in_Fs
      aesop
  case sequence α β =>
    simp_all only [H, List.mem_flatten, List.mem_map, Prod.exists, testsOfProgram, List.mem_append,
      exists_prop, exists_eq_right']
    rcases in_H with ⟨l, ⟨Fs', δ', in_Hα, def_l⟩ , in_l⟩
    subst def_l
    by_cases δ' = []
    · simp_all only [List.nil_append, ite_true, List.mem_flatten, List.mem_map, Prod.exists]
      subst_eqs
      rcases in_l with ⟨l', ⟨Fs'', δ'', in_Hβ, def_l'⟩ , in_l'⟩
      subst def_l'
      simp_all only [List.mem_singleton, Prod.mk.injEq, List.mem_union_iff]
      cases in_l'
      subst_eqs
      rcases φ_in_Fs with φ_in_Fs' | φ_in_Fs''
      · have IHβ := H_mem_test α φ in_Hα φ_in_Fs'
        aesop
      · have IHβ := H_mem_test β φ in_Hβ φ_in_Fs''
        aesop
    · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq]
      cases in_l
      subst_eqs
      have IHα := H_mem_test α φ in_Hα φ_in_Fs
      aesop
  case star β =>
    simp_all only [H, List.empty_eq, List.cons_union, List.nil_union, List.mem_insert_iff,
      Prod.mk.injEq, List.mem_flatten, List.mem_map, Prod.exists, testsOfProgram, exists_prop,
      exists_eq_right']
    rcases in_H with both_nil | ⟨l, ⟨Fs', δ', in_Hβ, def_l⟩, in_l⟩
    · exfalso; aesop
    · by_cases δ' = []
      · subst_eqs
        simp_all only [List.nil_append, ite_true, List.not_mem_nil]
      · subst def_l
        simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq]
        cases in_l
        subst_eqs
        have IHβ := H_mem_test β φ in_Hβ φ_in_Fs
        aesop
  case test τ =>
    simp_all [H, testsOfProgram]

/-- A list of programs coming from `H` is either empty or starts with an atom. -/
theorem H_mem_sequence α {Fs δ} (in_H : ⟨Fs, δ⟩ ∈ H α) :
    δ = [] ∨ ∃ a δ', δ = (·a : Program) :: δ' := by
  cases α
  case atom_prog =>
    simp_all [H]
  case union α β =>
    simp_all [H]
    rcases in_H with in_Hα | in_Hβ
    · have IHα := H_mem_sequence α in_Hα
      aesop
    · have IHβ := H_mem_sequence β in_Hβ
      aesop
  case sequence α β =>
    simp_all only [H, List.mem_flatten, List.mem_map, Prod.exists]
    rcases in_H with ⟨l, ⟨Fs', δ', in_Hα, def_l⟩ , in_l⟩
    subst def_l
    by_cases δ' = []
    · simp_all only [List.nil_append, ite_true, List.mem_flatten, List.mem_map, Prod.exists]
      rcases in_l with ⟨l', ⟨Fs'', δ'', in_Hβ, def_l'⟩, in_l'⟩
      subst def_l'
      simp_all only [List.mem_singleton, Prod.mk.injEq]
      have IHβ := H_mem_sequence β in_Hβ
      aesop
    · have IHα := H_mem_sequence α in_Hα
      aesop
  case star β =>
    simp_all only [H, List.empty_eq, List.cons_union, List.nil_union, List.mem_insert_iff,
      Prod.mk.injEq, List.mem_flatten, List.mem_map, Prod.exists]
    rcases in_H with ⟨Fs_nil, δ_nil⟩ | ⟨l, ⟨Fs', δ', in_Hβ, def_l⟩ , in_l⟩
    · subst_eqs
      aesop
    · subst def_l
      by_cases δ' = []
      · aesop
      · have IHβ := H_mem_sequence β in_Hβ
        aesop
  case test τ =>
    simp_all [H]

theorem keepFreshH α : x ∉ α.voc → ∀ F δ, (F,δ) ∈ H α → x ∉ F.fvoc ∧ x ∉ δ.pvoc := by
  intro x_notin F δ Fδ_in_H
  cases α
  all_goals
    simp [H, Program.voc] at *
  case atom_prog a =>
    cases Fδ_in_H
    subst_eqs
    simp [Program.voc]
    assumption
  case test =>
    cases Fδ_in_H
    subst_eqs
    aesop
  all_goals
    constructor -- FIXME: delay this to shorten the proof?
  case sequence.left α β =>
    rcases Fδ_in_H with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in, def_l⟩⟩, Fδ_in_l⟩⟩
    subst def_l
    cases em (δ' = []) <;> simp_all
    · subst_eqs
      have IHα := keepFreshH α x_notin.1 F' [] Fδ'_in
      simp_all [Vocab.fromList]
      rcases Fδ_in_l with ⟨l', ⟨⟨a', b', ⟨a'b'_in_Hβ, def_l'⟩⟩, Fδ_in_l'⟩⟩
      subst_eqs
      simp_all
      intro y y_in
      cases y_in
      · apply IHα
        assumption
      · have IHβ := keepFreshH β x_notin.2 a' b' a'b'_in_Hβ
        simp_all
    · have := keepFreshH α x_notin.1 F' δ' Fδ'_in
      simp_all
  case sequence.right α β =>
    rcases Fδ_in_H with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in, def_l⟩⟩, Fδ_in_l⟩⟩
    subst def_l
    cases em (δ' = []) <;> simp_all
    · subst_eqs
      rcases Fδ_in_l with ⟨l', ⟨⟨a', b', ⟨a'b'_in_Hβ, def_l'⟩⟩, Fδ_in_l'⟩⟩
      subst_eqs
      simp_all
      have IHβ := keepFreshH β x_notin.2 a' b' a'b'_in_Hβ
      simp_all
    · intro y y_in
      cases Fδ_in_l
      subst_eqs
      have IHα := keepFreshH α x_notin.1 F δ' Fδ'_in
      aesop
  case union.left α β =>
    cases Fδ_in_H
    · have IHα := keepFreshH α x_notin.1 F δ
      simp_all
    · have IHβ := keepFreshH β x_notin.2 F δ
      simp_all
  case union.right α β =>
    cases Fδ_in_H
    · have IHα := keepFreshH α x_notin.1 F δ
      simp_all
    · have IHβ := keepFreshH β x_notin.2 F δ
      simp_all
  case star.left α =>
    cases Fδ_in_H
    · simp_all
    case inr hyp =>
      rcases hyp with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in_Hα, def_l⟩⟩, Fδ_in_l⟩⟩
      subst def_l
      have IHα := keepFreshH α x_notin F' δ' Fδ'_in_Hα
      cases em (δ' = []) <;> simp_all
  case star.right α =>
    cases Fδ_in_H
    · simp_all
    case inr hyp =>
      rcases hyp with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in_Hα, def_l⟩⟩, Fδ_in_l⟩⟩
      subst def_l
      have IHα := keepFreshH α x_notin F' δ' Fδ'_in_Hα
      cases em (δ' = []) <;> aesop

-- FIXME is this in the notes? implicit somewhere?
theorem H_goes_down_prog (α : Program) {Fs δ} (in_H : (Fs, δ) ∈ H α) {γ} (in_δ: γ ∈ δ) :
  (if α.isAtomic then γ = α else if α.isStar
    then lengthOfProgram γ ≤ lengthOfProgram α
    else lengthOfProgram γ < lengthOfProgram α) := by
  cases α
  · simp_all [H, Program.isAtomic]
  case sequence α β =>
    simp only [Program.isAtomic, Bool.false_eq_true, ↓reduceIte, Program.isStar, lengthOfProgram]
    simp only [H, List.mem_flatten, List.mem_map, Prod.exists] at in_H
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
        have IHβ := H_goes_down_prog β in_Hβ in_δ
        cases β
        all_goals
          simp_all [H, lengthOfProgram, Program.isAtomic, Program.isStar]
          try linarith
      · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq, List.mem_append]
        cases in_l
        subst_eqs
        rcases in_δ with bla | γ_eq_β
        · have IHα := H_goes_down_prog α in_H bla
          cases α
          all_goals
            simp_all [H, lengthOfProgram, Program.isAtomic, Program.isStar]
            try linarith
        · subst γ_eq_β
          linarith
  case union α β =>
    simp only [Program.isAtomic, Bool.false_eq_true, ↓reduceIte, Program.isStar, lengthOfProgram]
    simp only [H, List.mem_union_iff] at in_H
    rcases in_H with hyp | hyp
    · have IHα := H_goes_down_prog α hyp in_δ
      by_cases α.isAtomic <;> by_cases α.isStar <;> simp_all <;> linarith
    · have IHβ := H_goes_down_prog β hyp in_δ
      by_cases β.isAtomic <;> by_cases β.isStar <;> simp_all <;> linarith
  case star α =>
    simp only [Program.isAtomic, Bool.false_eq_true, ↓reduceIte, Program.isStar, lengthOfProgram]
    simp only [H, List.empty_eq, List.cons_union, List.nil_union, List.mem_insert_iff,
      Prod.mk.injEq, List.mem_flatten, List.mem_map, Prod.exists] at in_H
    rcases in_H with _ | ⟨l, ⟨Fs', δ', in_H', def_l⟩, in_l⟩
    · simp_all only [List.not_mem_nil]
    · subst def_l
      by_cases δ' = []
      · simp_all
      · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq, List.mem_append]
        cases in_l
        subst_eqs
        rcases in_δ with hyp | hyp
        · have IHα := H_goes_down_prog α in_H' hyp
          by_cases α.isAtomic <;> by_cases α.isStar <;> simp_all <;> linarith
        · subst hyp
          simp [lengthOfProgram]
  case test τ =>
    simp_all [H]

-- NOTE: this intermediate definition is no longer in the notes.
def Yset : (List Formula × List Program) → Formula → List Formula
| ⟨F, δ⟩, φ => F ∪ [ ~ Formula.boxes δ φ ]

/-- Φ_◇(α,ψ) -/
def unfoldDiamond (α : Program) (φ : Formula) : List (List Formula) :=
  (H α).map (fun Fδ => Yset Fδ φ)

/-- Where formulas in the diamond unfolding can come from. Inspired by unfoldBoxContent. -/
theorem unfoldDiamondContent α ψ :
    ∀ X ∈ (unfoldDiamond α ψ),
    ∀ φ ∈ X,
        (  (φ = (~ψ))
         ∨ (∃ τ ∈ testsOfProgram α, φ = τ)
         ∨ (∃ (a : Nat), ∃ δ, φ = (~⌈·a⌉⌈⌈δ⌉⌉ψ)))
    := by
  intro X X_in φ φ_in_X
  simp [unfoldDiamond, Yset] at X_in
  rcases X_in with ⟨Fs, δ, in_H, def_X⟩
  subst def_X
  simp at φ_in_X
  rcases φ_in_X with φ_in_Fs | φ_def
  · -- φ is in F so it must be a test
    right
    left
    have := H_mem_test α φ in_H φ_in_Fs
    rcases this with ⟨τ, τ_in, φ_def⟩
    use τ
  · -- φ is made from some δ from H α
    have := H_mem_sequence α in_H
    aesop

theorem unfoldDiamond_voc {x α φ} {L} (L_in : L ∈ unfoldDiamond α φ) {ψ} (ψ_in : ψ ∈ L)
    (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  simp [unfoldDiamond, Yset] at L_in
  rcases L_in with ⟨Fs, δ, in_H, def_L⟩
  subst def_L
  simp at ψ_in
  cases ψ_in
  case inl hyp =>
    left
    have := H_mem_test α ψ in_H hyp
    rcases this with ⟨τ, τ_in, ψ_def⟩
    subst ψ_def
    exact testsOfProgram.voc α τ_in x_in_voc_ψ
  case inr ψ_def =>
    have := H_mem_sequence
    subst ψ_def
    simp only [Formula.voc, Formula.voc_boxes, Finset.mem_union] at x_in_voc_ψ
    cases x_in_voc_ψ
    case inl hyp =>
      left
      rw [Vocab.fromListProgram_map_iff] at *
      rcases hyp with ⟨α', α'_in, x_in⟩
      by_contra hyp
      have := (keepFreshH α hyp Fs δ in_H).2
      unfold List.pvoc at this
      rw [Vocab.fromListProgram_map_iff] at this
      push_neg at this
      specialize this _ α'_in
      tauto
    · right
      assumption

theorem guardToStarDiamond (x : Nat)
    (x_notin_beta : Sum.inl x ∉ β.voc)
    (beta_equiv : (~⌈β⌉~·x) ≡ (((·x) ⋀ σ0) ⋁ σ1))
    (repl_imp_rho : repl_in_F x ρ σ1 ⊨ ρ)
    (notPsi_imp_rho : (~ψ) ⊨ ρ)
  : (~⌈(∗β)⌉ψ) ⊨ ρ:= by
  intro W M
  have claim : ∀ u v, (M,v) ⊨ ρ → relate M β u v → (M,u) ⊨ ρ := by
    intro u v v_rho u_β_v
    have u_ : (M,u) ⊨ (~⌈β⌉~ρ) := by
      simp [modelCanSemImplyForm] at *
      use v
    have u_2 : (M, u) ⊨ (ρ ⋀ repl_in_F x ρ σ0) ⋁ (repl_in_F x ρ σ1) := by
      have repl_equiv := repl_in_F_equiv x ρ beta_equiv
      simp only [repl_in_F, beq_self_eq_true, reduceIte, Formula.or] at repl_equiv
      have nox : repl_in_P x ρ β = β := repl_in_P_non_occ_eq x_notin_beta
      rw [nox] at repl_equiv
      rw [equiv_iff _ _ repl_equiv] at u_
      simp [modelCanSemImplyForm, evaluatePoint, formCanSemImplyForm, semImpliesLists] at *
      tauto
    simp only [modelCanSemImplyForm, Formula.or, evaluatePoint, evaluate] at u_2
    rw [← @or_iff_not_and_not] at u_2
    specialize repl_imp_rho W M u
    aesop
  -- It remains to show the goal using claim.
  intro w hyp
  simp only [Formula.or, List.mem_singleton, forall_eq, evaluate, relate, not_forall, exists_prop] at *
  rcases hyp with ⟨v, w_bS_v, v_Psi⟩
  induction w_bS_v using Relation.ReflTransGen.head_induction_on
  case refl =>
    specialize notPsi_imp_rho W M v
    simp_all
  case head u1 u2 u1_b_u2 _ IH =>
    specialize claim u1 u2
    specialize notPsi_imp_rho W M u1
    simp [modelCanSemImplyForm, evaluatePoint, formCanSemImplyForm, semImpliesLists] at *
    simp_all

private theorem helper : ∀ (p : List Formula × List Program → Formula) X,
        (∃ f ∈ List.map p X, evaluate M w f)
      ↔ (∃ Fδ ∈ X, evaluate M w (p Fδ)) := by aesop

set_option maxHeartbeats 2000000 in
theorem localDiamondTruth γ ψ : (~⌈γ⌉ψ) ≡ dis ( (H γ).map (fun Fδ => Con (Yset Fδ ψ)) ) := by
  intro W M w
  cases γ
  case atom_prog a =>
    simp [H, Yset]
  case test τ =>
    simp [evaluate, H, Yset]
    rw [conEval]
    simp
  case union α β =>
    -- "This case is straightforward"
    have IHα := localDiamondTruth α ψ W M w
    have IHβ := localDiamondTruth β ψ W M w
    simp [evaluate, H, Yset, disEval] at *
    constructor
    · rintro ⟨v, v_claim⟩
      rw [or_and_right] at v_claim
      cases v_claim
      case inl hyp =>
        have : (∃ x, relate M α w x ∧ ¬evaluate M x ψ) := ⟨v, hyp⟩
        rw [IHα] at this
        rcases this with ⟨f, ⟨⟨a, b, ⟨ab_in, def_f⟩⟩, w_f⟩⟩
        exact ⟨f, ⟨⟨a, b, ⟨Or.inl ab_in, def_f⟩⟩, w_f⟩⟩
      case inr hyp =>
        have : (∃ x, relate M β w x ∧ ¬evaluate M x ψ) := ⟨v, hyp⟩
        rw [IHβ] at this
        rcases this with ⟨f, ⟨⟨a, b, ⟨ab_in, def_f⟩⟩, w_f⟩⟩
        exact ⟨f, ⟨⟨a, b, ⟨Or.inr ab_in, def_f⟩⟩, w_f⟩⟩
    · rintro ⟨f, ⟨a, b, ⟨(ab_in_Hα|ab_in_Hβ), def_f⟩⟩, w_f⟩
      · have : ∃ f, (∃ a b, (a, b) ∈ H α ∧ Con (a ∪ [~⌈⌈b⌉⌉ψ]) = f) ∧ evaluate M w f :=
          ⟨f, ⟨⟨a, b, ⟨ab_in_Hα, def_f⟩⟩, w_f⟩⟩
        rw [← IHα] at this
        rcases this with ⟨x, ⟨w_α_x, x_Psi⟩⟩
        exact ⟨x, ⟨Or.inl w_α_x, x_Psi⟩⟩
      · have : ∃ f, (∃ a b, (a, b) ∈ H β ∧ Con (a ∪ [~⌈⌈b⌉⌉ψ]) = f) ∧ evaluate M w f :=
          ⟨f, ⟨⟨a, b, ⟨ab_in_Hβ, def_f⟩⟩, w_f⟩⟩
        rw [← IHβ] at this
        rcases this with ⟨x, ⟨w_β_x, x_Psi⟩⟩
        exact ⟨x, ⟨Or.inr w_β_x, x_Psi⟩⟩
  case sequence α β =>
    -- "This case follows from the following computation"
    have : evaluate M w (~⌈α;'β⌉ψ) ↔ evaluate M w (~⌈α⌉⌈β⌉ψ) := by aesop
    rw [this]
    clear this
    have IHα := localDiamondTruth α (⌈β⌉ψ) W M w
    rw [IHα]
    clear IHα
    rw [disEval]
    rw [disEval]
    rw [helper, helper]
    constructor
    -- downwards direction in notes:
    · rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_Con⟩⟩
      cases em (δ = [])
      case inl δ_is_empty => -- tricky case where we actually need the IH for β
        subst δ_is_empty
        have claim : ∃ Gγ ∈ H β, evaluate M w (Con (Yset Gγ ψ)) := by
          rw [conEval] at w_Con
          simp [Yset] at w_Con
          have := w_Con (~⌈β⌉ψ)
          simp only [or_true, forall_true_left] at this
          have IHβ := localDiamondTruth β ψ W M w
          rw [IHβ] at this
          rw [disEval, helper] at this
          exact this
        rcases claim with ⟨⟨Gs,γ⟩, Gsγ_in, claim⟩
        unfold H
        use ⟨Fs ∪ Gs, γ⟩
        constructor
        · simp only [List.mem_flatten, List.mem_map, Prod.exists]
          use ((H β).map (fun ⟨Gs',δ'⟩ => [⟨Fs ∪ Gs', δ'⟩])).flatten
          simp only [List.mem_flatten, List.mem_map, Prod.exists]
          constructor
          · use Fs, []
            simp only [reduceIte, and_true]
            exact Fδ_in
          · tauto
        · simp only [Yset, conEval, List.mem_union_iff, List.mem_singleton] at *
          intro f f_in
          specialize w_Con f
          specialize claim f
          tauto
      case inr δ_not_empty => -- the easy case?
        unfold H
        use ⟨Fs, δ ++ [β]⟩
        constructor
        · simp
          use [(Fs, δ ++ [β])]
          constructor
          · use Fs, δ
            simp_all
          · simp_all
        · simp [Yset, conEval, boxes_append] at *
          intro f f_in
          apply w_Con
          tauto
    -- upwards direction in notes:
    · rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_Con⟩⟩ -- ⟨⟨l, ⟨⟨a, b, ⟨ab_in, def_l⟩⟩, f_in_l⟩⟩, w_f⟩⟩
      simp [H] at Fδ_in
      rcases Fδ_in with ⟨l, ⟨Gs, γ, ⟨Gγ_in, def_l⟩⟩, Gγ_in_l⟩
      subst def_l
      cases em (γ = [])
      case inl δ_is_empty => -- tricky case where we actually need the IH for β
        subst δ_is_empty
        simp at Gγ_in_l
        rcases Gγ_in_l with ⟨l, ⟨⟨aaa, bbb, ⟨_in_Hβ,def_l⟩ ⟩, Fsδ_in_l⟩ ⟩
        subst def_l
        simp
        use Gs, []
        constructor
        · exact Gγ_in
        · simp at Fsδ_in_l
          cases Fsδ_in_l
          subst_eqs
          simp [conEval, Yset]
          intro f f_in
          cases f_in
          case inl f_in =>
            rw [conEval] at w_Con
            simp [Yset] at *
            specialize w_Con f
            tauto
          case inr f_def =>
            subst f_def
            have IHβ := localDiamondTruth β ψ W M w
            rw [IHβ, disEval, helper]
            clear IHβ
            refine ⟨⟨aaa, δ⟩, ⟨_in_Hβ, ?_⟩⟩
            rw [conEval]
            rw [conEval] at w_Con
            simp [Yset] at *
            intro f
            specialize w_Con f
            tauto
      case inr δ_not_empty => -- the easy case
        simp_all
        cases Gγ_in_l
        subst_eqs
        simp_all [Yset, conEval, boxes_append]
        use Fs, γ
  case star β =>
    let ρ := dis ((H (∗β)).map (fun Fδ => Con (Yset Fδ ψ)))
    -- "then our goal will be ..."
    suffices goal : (~⌈∗β⌉ψ) ≡ ρ by
      have := @equiv_iff _ _ goal W M w
      simp only [modelCanSemImplyForm, evaluatePoint] at this
      rw [this]
    -- right to left, done first because we use it for the other direction
    have right_to_left_claim : ∀ W M (w : W), evaluate M w ρ → evaluate M w (~⌈∗β⌉ψ) := by
      -- Note that we are switching model now.
      clear W M w; intro W M w
      unfold ρ
      rw [disEval, helper]
      rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_Con⟩⟩
      rw [conEval] at w_Con
      simp [H] at Fδ_in
      cases Fδ_in
      case inl hyp =>
        cases hyp
        subst_eqs
        simp_all [Yset]
        use w
      case inr hyp =>
        have : ∃ γ, δ = γ ++ [∗β] ∧ γ ≠ [] ∧ (Fs,γ) ∈ H β := by aesop
        rcases this with ⟨γ, ⟨δ_def, _, Fγ_in⟩⟩
        subst δ_def
        simp only [Yset, List.mem_union_iff, List.mem_singleton] at w_Con
        suffices evaluate M w (~⌈β⌉⌈∗β⌉ψ) by
          simp at *
          rcases this with ⟨v, ⟨w_β_v, ⟨u, ⟨v_Sβ_u, u_nPsi⟩⟩⟩⟩
          refine ⟨u, ?_, u_nPsi⟩
          exact Relation.ReflTransGen.head w_β_v v_Sβ_u
        have IHβ := localDiamondTruth β (⌈∗β⌉ψ) W M w
        rw [disEval, helper] at IHβ
        rw [IHβ]
        refine ⟨⟨Fs, γ⟩, ⟨Fγ_in, ?_⟩⟩
        simp_all [conEval, Yset, boxes_append]
    -- switch model again
    clear W M w; intro W M w
    constructor
    · -- left to right, done second in notes
      -- NOTE: Here is why we switched from `Char` to `Nat` for atomic propositions.
      -- Char was finite so we could not get fresh variables. Now we can :-)
      -- An alternative idea to solve this would have been to refactor everything
      -- to allow different types, but that seemed harder and not (yet?!) needed.
      let x : Nat := freshVarProg β
      have x_not_in : Sum.inl x ∉ β.voc := by apply freshVarProg_is_fresh
      -- NOTE the use of ⊥ below - matters for rhs-to-lhs in first Lemma condition.
      let σ0 : Formula := dis $
        (H β).map (fun (F,δ) => if δ = [] then Con F else ⊥)
      let σ1 : Formula := dis $
        ((H β).map (fun (F,δ) => if δ ≠ [] then Con ((~ Formula.boxes δ (~(·x : Formula))) :: F) else ⊥))
      -- Now we use the previous Lemma:
      have := @guardToStarDiamond β σ0 σ1 ρ ψ x x_not_in
      simp only [formCanSemImplyForm, semImpliesLists, List.mem_singleton, forall_eq] at this
      apply this <;> (clear this W M w; intro W M w) -- Switching model again.
      · -- Use IH to show first Lemma condition:
        have IHβ := localDiamondTruth β (~·x) W M w
        rw [disEval,helper] at IHβ
        rw [IHβ]
        clear IHβ
        constructor
        · rintro ⟨⟨Fs, δ⟩, Fδ_in, w_⟩
          simp only [evaluate, Formula.or]
          rw [← or_iff_not_and_not]
          cases em (δ = [])
          · subst_eqs
            simp [conEval, Yset] at w_
            left
            unfold σ0
            simp_all
            rw [disEval, helper]
            constructor
            · have := w_ (~~·x)
              simp at this
              exact this
            · use (Fs, [])
              simp_all
              rw [conEval]
              intro f f_in
              apply w_
              left
              exact f_in
          · simp [conEval, Yset] at w_
            right
            unfold σ1
            simp_all
            rw [disEval, helper]
            use (Fs, δ)
            simp_all
            rw [conEval]
            intro f f_in
            apply w_ f
            simp at f_in
            tauto
        · intro rhs
          simp only [evaluate, Formula.or] at rhs
          rw [← or_iff_not_and_not] at rhs
          cases rhs
          case inl hyp =>
            unfold σ0 at hyp
            simp at hyp
            rw [disEval, helper] at hyp
            rcases hyp with ⟨w_x, ⟨⟨Fs,δ⟩, w_⟩⟩
            use (Fs,δ)
            simp [conEval, Yset]
            constructor
            · exact w_.1
            · cases em (δ = [])
              case inl δ_is_empty =>
                subst δ_is_empty
                simp_all [conEval]
                intro f f_in
                cases f_in
                · apply w_.2; assumption
                · subst_eqs; simp; assumption
              case inr δ_notEmpty => exfalso; simp_all
                -- this case works because we used ⊥ above!
          case inr hyp =>
            unfold σ1 at hyp
            simp at hyp
            rw [disEval, helper] at hyp
            rcases hyp with ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_⟩⟩
            use ⟨Fs,δ⟩
            simp [conEval, Yset] at *
            -- hmm
            constructor
            · exact Fδ_in
            · cases em (δ = [])
              case inl _ => exfalso; simp_all
                -- this case works because we used ⊥ above!
              case inr δ_notEmpty =>
                simp_all [conEval]
                intro f f_in
                cases f_in
                · apply w_.2; assumption
                · subst_eqs; simp; exact w_.1
      · -- Lemma condition that is done last in notes.
        unfold σ1
        simp only [ne_eq, Formula.instBot, ite_not]
        have : (repl_in_F x ρ (dis ((H β).map
          (fun Fδ => if Fδ.2 = [] then Formula.bottom else Con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)) ))) =
            (dis ((H β).map (fun Fδ => if Fδ.2 = [] then Formula.bottom else Con ((~⌈⌈Fδ.2⌉⌉~ρ) :: Fδ.1))))
            := by
          suffices (repl_in_F x ρ (dis ((H β).map
            (fun Fδ => if Fδ.2 = [] then Formula.bottom else Con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)) ))) =
              ((dis ((H β).map
                (fun Fδ => if Fδ.2 = [] then repl_in_F x ρ Formula.bottom else repl_in_F x ρ (Con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)) )))) by
            rw [this]
            simp only [repl_in_F, Formula.instBot]
            -- use that x not in β and thus also not in any element of H β
            have myFresh := keepFreshH β x_not_in
            apply listEq_to_disEq
            rw [List.map_inj_left]
            intro Fδ Fδ_in_Hβ
            cases em (Fδ.2 = [])
            · simp_all
            · simp_all only [evaluate, relate, not_forall, exists_prop, repl_in_F, Formula.instBot, ite_false]
              rw [repl_in_Con]
              simp only [List.map_cons, repl_in_F]
              apply listEq_to_conEq
              simp only [List.cons.injEq, Formula.neg.injEq]
              constructor
              · exact repl_in_boxes_non_occ_eq_neg _ ((myFresh _ _ (Fδ_in_Hβ)).2)
              · exact repl_in_list_non_occ_eq _ ((myFresh _ _ (Fδ_in_Hβ)).1)
          -- remains to push repl_in_F through dis and map
          convert repl_in_disMap x ρ (H β) (fun Fδ => Fδ.2 = []) (fun Fδ => (Con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)))
        rw [this, disEval, helper]
        clear this
        rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, repl_w_⟩⟩
        cases em (δ = [])
        case inl hyp =>
          subst hyp
          simp_all
        case inr hyp =>
          simp [hyp] at repl_w_
          rw [conEval] at repl_w_
          have := repl_w_ (~⌈⌈δ⌉⌉~ρ) (by simp)
          simp [evalBoxes] at this
          rcases this with ⟨v, w_ρ_v, v_ρ⟩ -- used for v_notStarβψ below!
          -- We now do bottom-up what the notes do, first reasoning "at w" then "at v"
          unfold ρ
          -- unsure from here on
          simp_all [disEval] -- affects v_notStarβψ :-/
          simp [H]
          use Con (Yset (Fs, δ ++ [∗β]) ψ)
          constructor
          · use Fs, δ ++ [∗β]
            simp_all
            use [(Fs, δ ++ [∗β])]
            simp
            use Fs, δ
            simp_all
          · simp [conEval, Yset]
            intro f f_in
            cases f_in
            case inl f_in_F => exact repl_w_.2 f f_in_F
            case inr f_def =>
              subst f_def
              simp [boxes_append,evalBoxes]
              have v_notStarβψ := right_to_left_claim W M v v_ρ
              exact ⟨v, ⟨w_ρ_v, v_notStarβψ⟩⟩
      · -- Second Lemma condition
        intro w_nPsi
        unfold ρ
        rw [disEval, helper]
        simp [H, conEval, Yset]
        left
        simp at w_nPsi
        exact w_nPsi
    · apply right_to_left_claim -- done above

/-- Helper function to trick "List.Chain r" to use a different r at each step. -/
def pairRel (M : KripkeModel W) : (Program × W) → (Program × W) → Prop
| (_, v), (α, w) => relate M α v w

-- use later for Modelgraphs
theorem relateSeq_toChain' {M} {δ} {v w : W} : relateSeq M δ v w → δ ≠ [] →
    ∃ (l : List W), l.length + 1 = δ.length ∧
    List.Chain' (pairRel M) (List.zip ((?'⊤) :: δ) (v :: l ++ [w]) ) := by
  induction δ generalizing v w
  case nil =>
    simp [relateSeq]
  case cons e δ IH =>
    cases em (δ = [])
    case inl δ_eq_empty =>
      subst δ_eq_empty
      intro _
      simp_all [pairRel]
    case inr δ_notEmpty =>
      simp only [relateSeq]
      rintro ⟨u, v_d_u, u_δ_w⟩ _
      specialize IH u_δ_w δ_notEmpty
      rcases IH with ⟨l, l_def, lchain⟩
      use (u :: l)
      constructor
      · simp_all
      · simp_all [pairRel]
        apply List.Chain'.cons'
        · have := List.Chain'.tail lchain
          simp_all
        · cases l <;> cases δ
          all_goals simp_all [pairRel]

theorem existsDiamondH (v_γ_w : relate M γ v w) :
    ∃ Fδ ∈ H γ, (M,v) ⊨ Fδ.1 ∧ relateSeq M Fδ.2 v w := by
  cases γ
  case atom_prog =>
    simp [H, relateSeq] at *
    exact v_γ_w
  case test τ =>
    simp [H, relateSeq] at *
    aesop
  case union α β =>
    simp [H] at *
    cases v_γ_w
    case inl hyp =>
      have IHα := existsDiamondH hyp
      aesop
    case inr hyp =>
      have IHβ := existsDiamondH hyp
      aesop
  case sequence α β =>
    simp only [relate] at v_γ_w
    rcases v_γ_w with ⟨u, v_α_u, u_β_w⟩
    have IHα := existsDiamondH v_α_u
    simp at IHα
    rcases IHα with ⟨Fs, δ, ⟨Fδ_in, u_Fs, v_δ_u⟩⟩
    cases em (δ = [])
    case inl hyp =>
      subst hyp
      simp only [relateSeq] at v_δ_u -- we have v = u
      subst v_δ_u
      have IHβ := existsDiamondH u_β_w
      simp at IHβ
      rcases IHβ with ⟨Gs, η, ⟨Gη_in, v_Gs, v_η_w⟩⟩
      refine ⟨ ⟨Fs ∪ Gs, η⟩, ⟨?_, ?_, v_η_w⟩ ⟩
      · simp_all [H]
        refine ⟨_, ⟨⟨Fs, [], ⟨Fδ_in, by rfl⟩⟩, ?_⟩⟩
        simp
        use [(Fs ∪ Gs, η)]
        aesop
      · intro f f_in
        simp at f_in
        cases f_in
        · specialize u_Fs f (by assumption)
          assumption
        · apply v_Gs f
          assumption
    case inr hyp =>
      refine ⟨⟨Fs, δ ++ [β]⟩, ⟨?_, ?_, ?_⟩⟩
      · simp_all [H]
        refine ⟨_, ⟨⟨Fs, δ, ⟨ Fδ_in , by rfl⟩⟩, ?_⟩⟩
        simp_all
      · intro f f_in
        simp at f_in
        specialize u_Fs f f_in
        assumption
      · simp [relateSeq_append]
        use u
  case star β =>
    simp only [relate] at v_γ_w
    have := ReflTransGen.cases_tail_eq_neq v_γ_w
    cases this
    · subst_eqs
      use ⟨∅, []⟩
      simp [H, relateSeq]
    case inr hyp =>
      rcases hyp with ⟨_, ⟨v1, v_neq_v1, v_β_v1, v1_βS_w⟩⟩
      have IHβ := existsDiamondH v_β_v1
      rcases IHβ with ⟨⟨Fs,δ⟩, Fδ_in, v_Fs, v_δ_v1⟩
      use ⟨Fs, δ ++ [∗β]⟩
      constructor
      · simp [H] at *
        have claim : δ ≠ [] := by
          by_contra hyp
          subst_eqs
          simp [relateSeq] at v_δ_v1
          tauto
        refine ⟨_, ⟨⟨Fs, δ, ⟨Fδ_in, by rfl⟩⟩, ?_⟩⟩
        simp_all
      · constructor
        · intro f f_in
          simp at f_in
          exact v_Fs f f_in
        · rw [relateSeq_append]
          use v1
          simp [relateSeq] at *
          tauto

/-! ## splitLast -/

/-- Helper function for `YsetLoad'` to get last list element. -/
def splitLast : List α → Option (List α × α)
| [] => none
| (x :: xs) => some $ match splitLast xs with
  | none => ([], x)
  | some (ys, y) => (x::ys, y)

@[simp]
theorem splitLast_nil : splitLast [] = (none : Option (List α × α)) := by simp [splitLast]

theorem splitLast_cons_eq_some (x : α) (xs : List α) :
    (splitLast (x :: xs)) = some ((x :: xs).dropLast, (x :: xs).getLast (List.cons_ne_nil x xs)) := by
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

/-! ## Loaded Diamonds (Section 3.3)

The `Option` is used here because unfolding of tests can lead to free nodes.
-/

def YsetLoad : (List Formula × List Program) → LoadFormula → (List Formula × Option NegLoadFormula)
| ⟨F, δ⟩, χ => ⟨F , ~' (LoadFormula.boxes δ χ)⟩

def YsetLoad' : (List Formula × List Program) → Formula → (List Formula × Option NegLoadFormula)
| ⟨F, δ⟩, φ => match splitLast δ with
    | none => ⟨F ∪ [~φ], none⟩
    | some (δ, β) => ⟨F , ~' (loadMulti δ β φ)⟩

/-- Loaded unfolding for ~'⌊α⌋(χ : LoadFormula) -/
def unfoldDiamondLoaded (α : Program) (χ : LoadFormula) : List (List Formula × Option NegLoadFormula) :=
  (H α).map (fun Fδ => YsetLoad Fδ χ)

/-- Loaded unfolding for ~'⌊α⌋(φ : Formula) -/
def unfoldDiamondLoaded' (α : Program) (φ : Formula) : List (List Formula × Option NegLoadFormula) :=
  (H α).map (fun Fδ => YsetLoad' Fδ φ)

def pairUnload : List Formula × Option NegLoadFormula → List Formula
| (xs, none) => xs
| (xs, some nlf) => xs ∪ [negUnload nlf]

theorem unfoldDiamondLoaded_eq α χ : (unfoldDiamondLoaded α χ).map pairUnload = unfoldDiamond α χ.unload := by
  simp [unfoldDiamondLoaded, unfoldDiamond, YsetLoad, Yset, pairUnload]

theorem unfoldDiamondLoaded'_eq α φ : (unfoldDiamondLoaded' α φ).map pairUnload = unfoldDiamond α φ := by
  simp [unfoldDiamondLoaded', unfoldDiamond, YsetLoad', Yset, pairUnload]
  intro F δ in_H
  cases δ
  · simp
  case cons x xs =>
    simp only [splitLast_cons_eq_some, unload_loadMulti, Formula.boxes_cons]
    have := (@boxes_append (x :: xs).dropLast [(x :: xs).getLast (List.cons_ne_nil x xs)] φ).symm
    simp only [Formula.boxes_cons, Formula.boxes_nil] at this
    rw [this]
    rw [List.dropLast_append_getLast]
    simp_all
