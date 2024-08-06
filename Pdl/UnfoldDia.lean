-- Local unfolding of diamonds

-- import Mathlib.Data.Fintype.Pi

import Pdl.Substitution
import Pdl.Fresh
import Pdl.Star

open HasVocabulary

-- ### Diamonds: H, Y and Φ_⋄

def H : Program → List (List Formula × List Program)
| ·a => [ ([], [·a]) ]
| ?'τ => [ ([τ], []) ]
| α ⋓ β => H α ∪ H β
| α;'β => ((H α).map (fun ⟨F,δ⟩ =>
            if δ = []
              then ((H β).map (fun ⟨G,δ'⟩ => [⟨F ∪ G, δ'⟩])).join
              else [⟨F, δ ++ [β]⟩])
          ).join
| ∗α => [ (∅,[]) ] ∪ ((H α).map (fun (F,δ) => if δ = [] then [] else [(F, δ ++ [∗α])])).join

theorem keepFreshH α : x ∉ voc α → ∀ F δ, (F,δ) ∈ H α → x ∉ voc F ∧ x ∉ voc δ := by
  intro x_notin F δ Fδ_in_H
  cases α
  all_goals
    simp [H, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList] at *
  case atom_prog a =>
    cases Fδ_in_H
    subst_eqs
    simp [vocabOfProgram, Vocab.fromList]
    assumption
  case test =>
    cases Fδ_in_H
    subst_eqs
    simp [Vocab.fromList]
    aesop
  all_goals
    constructor -- FIXME: delay this to shorten the proof?
  case sequence.left α β =>
    rcases Fδ_in_H with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in, def_l⟩⟩, Fδ_in_l⟩⟩
    subst def_l
    cases em (δ' = []) <;> simp_all
    · subst_eqs
      have IHα := keepFreshH α x_notin.1 F' [] Fδ'_in
      simp_all [H, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList]
      rcases Fδ_in_l with ⟨l', ⟨⟨a', b', ⟨a'b'_in_Hβ, def_l'⟩⟩, Fδ_in_l'⟩⟩
      subst_eqs
      simp_all [Vocab.fromListFormula_map_iff]
      intro y y_in
      cases y_in
      · apply IHα
        assumption
      · have IHβ := keepFreshH β x_notin.2 a' b' a'b'_in_Hβ
        simp_all [H, voc, vocabOfFormula, vocabOfProgram, Vocab.fromListFormula_map_iff]
    · have := keepFreshH α x_notin.1 F' δ' Fδ'_in
      simp_all [H, voc,vocabOfFormula,vocabOfProgram]
  case sequence.right α β =>
    rcases Fδ_in_H with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in, def_l⟩⟩, Fδ_in_l⟩⟩
    subst def_l
    cases em (δ' = []) <;> simp_all
    · subst_eqs
      have IHα := keepFreshH α x_notin.1 F' [] Fδ'_in
      simp_all [H, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList]
      rcases Fδ_in_l with ⟨l', ⟨⟨a', b', ⟨a'b'_in_Hβ, def_l'⟩⟩, Fδ_in_l'⟩⟩
      subst_eqs
      simp_all
      have IHβ := keepFreshH β x_notin.2 a' b' a'b'_in_Hβ
      simp_all [H, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList]
    · have : List.map vocabOfProgram δ' ++ [vocabOfProgram β]
          = List.map vocabOfProgram (δ' ++ [β]) := by induction δ' <;> simp_all
      rw [this, Vocab.fromListProgram_map_iff]
      simp
      intro y y_in
      cases y_in
      · have IHα := keepFreshH α x_notin.1 F' δ' Fδ'_in
        simp_all [H, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList, Vocab.fromListFormula_map_iff, Vocab.fromListProgram_map_iff]
      · subst_eqs
        tauto
  case union.left α β =>
    cases Fδ_in_H
    · have IHα := keepFreshH α x_notin.1 F δ
      simp_all [H, voc,vocabOfFormula,vocabOfProgram]
    · have IHβ := keepFreshH β x_notin.2 F δ
      simp_all [H, voc,vocabOfFormula,vocabOfProgram]
  case union.right α β =>
    cases Fδ_in_H
    · have IHα := keepFreshH α x_notin.1 F δ
      simp_all [H, voc,vocabOfFormula,vocabOfProgram]
    · have IHβ := keepFreshH β x_notin.2 F δ
      simp_all [H, voc,vocabOfFormula,vocabOfProgram]
  case star.left α =>
    cases Fδ_in_H
    · simp_all [Vocab.fromList]
    case inr hyp =>
      rcases hyp with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in_Hα, def_l⟩⟩, Fδ_in_l⟩⟩
      subst def_l
      have IHα := keepFreshH α x_notin F' δ' Fδ'_in_Hα
      cases em (δ' = []) <;> simp_all [H, voc,vocabOfFormula,vocabOfProgram]
  case star.right α =>
    cases Fδ_in_H
    · simp_all [Vocab.fromList]
    case inr hyp =>
      rcases hyp with ⟨l, ⟨⟨F', δ', ⟨Fδ'_in_Hα, def_l⟩⟩, Fδ_in_l⟩⟩
      subst def_l
      have IHα := keepFreshH α x_notin F' δ' Fδ'_in_Hα
      cases em (δ' = [])
      · simp_all [H, voc,vocabOfFormula,vocabOfProgram]
      · simp_all [H, voc,vocabOfFormula,vocabOfProgram]
        cases Fδ_in_l
        subst_eqs
        have : List.map vocabOfProgram δ' ++ [vocabOfProgram α]
             = List.map vocabOfProgram (δ' ++ [α]) := by induction δ' <;> simp_all
        rw [this, Vocab.fromListProgram_map_iff]
        clear this
        simp
        intro y y_in
        cases y_in
        · have := keepFreshH α x_notin F δ' Fδ'_in_Hα
          simp_all [H, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList, Vocab.fromListFormula_map_iff, Vocab.fromListProgram_map_iff]
        · subst_eqs
          tauto

def Yset : (List Formula × List Program) → (Formula) → List Formula
| ⟨F, δ⟩, φ => F ∪ [ ~ Formula.boxes δ φ ]

/-- Φ_◇(α,ψ) -/
def unfoldDiamond (α : Program) (φ : Formula) : List (List Formula) :=
  (H α).map (fun Fδ => Yset Fδ φ)

theorem guardToStarDiamond (x : Nat)
    (x_notin_beta : Sum.inl x ∉ HasVocabulary.voc β)
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

theorem helper : ∀ (p : List Formula × List Program → Formula) X,
        (∃ f ∈ List.map p X, evaluate M w f)
      ↔ (∃ Fδ ∈ X, evaluate M w (p Fδ)) := by aesop

set_option maxHeartbeats 1000000 -- FIXME: added since Lean v4.10.0 -- how to speed up proof below?

theorem localDiamondTruth γ ψ : (~⌈γ⌉ψ) ≡ dis ( (H γ).map (fun Fδ => Con (Yset Fδ ψ)) ) := by
  intro W M w
  cases γ
  case atom_prog a =>
    simp [H]
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
          simp [Yset, Con] at w_Con
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
        · simp only [List.mem_join, List.mem_map, Prod.exists]
          use ((H β).map (fun ⟨Gs',δ'⟩ => [⟨Fs ∪ Gs', δ'⟩])).join
          simp only [List.mem_join, List.mem_map, Prod.exists]
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
      unfold_let ρ
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
        have := w_Con (~⌈⌈γ ++ [∗β]⌉⌉ψ)
        simp at this
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
      have x_not_in : Sum.inl x ∉ HasVocabulary.voc β := by apply freshVarProg_is_fresh
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
            unfold_let σ0
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
            unfold_let σ1
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
            unfold_let σ0 at hyp
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
            unfold_let σ1 at hyp
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
        unfold_let σ1
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
            · simp_all only [evaluate, relate, not_forall, exists_prop, repl_in_F, Formula.instBot, Prod.forall, ite_false]
              rw [repl_in_Con]
              simp only [List.map_cons, repl_in_F]
              apply listEq_to_conEq
              simp only [List.cons.injEq, Formula.neg.injEq]
              constructor
              · exact repl_in_boxes_non_occ_eq_neg _ ((myFresh _ _ (Fδ_in_Hβ)).2)
              · exact repl_in_list_non_occ_eq _ ((myFresh _ _ (Fδ_in_Hβ)).1)
          -- remains to push repl_in_F through dis and map
          convert repl_in_disMap x ρ (H β) (fun Fδ => Fδ.2 = []) (fun Fδ => (Con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)))
          simp
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
          unfold_let ρ
          -- unsure from here on
          simp_all [disEval, helper] -- affects v_notStarβψ :-/
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
        unfold_let ρ
        rw [disEval, helper]
        simp [H, conEval, Yset]
        left
        simp at w_nPsi
        exact w_nPsi
    · apply right_to_left_claim -- done above

-- Helper function to trick "List.Chain r" to use a different r at each step.
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
    simp [H, relateSeq] at *
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
    simp [H, relateSeq] at IHα
    rcases IHα with ⟨Fs, δ, ⟨Fδ_in, u_Fs, v_δ_u⟩⟩
    cases em (δ = [])
    case inl hyp =>
      subst hyp
      simp only [relateSeq] at v_δ_u -- we have v = u
      subst v_δ_u
      have IHβ := existsDiamondH u_β_w
      simp [H, relateSeq] at IHβ
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

-- ### Loaded Diamonds

-- NOTE: Do we actually need "Option" here?
-- I.e. can the loading disappear during unfolding? (See old DagTableau.loadDagEndNodes?)

-- for (~'⌊α⌋(χ : LoadFormula))
def unfoldDiamondLoad (α : Program) (χ : LoadFormula) : List (List Formula × Option NegLoadFormula) :=
  sorry
  -- TODO -- (H α).map (fun Fδ => Yset Fδ χ)
-- for (~'⌊α⌋(φ : Formula))
def unfoldDiamondLoad' (α : Program) (φ : Formula) : List (List Formula × Option NegLoadFormula) :=
  sorry
  -- TODO -- (H α).map (fun Fδ => Yset Fδ φ)
