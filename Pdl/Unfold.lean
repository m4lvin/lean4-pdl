-- UNFOLD

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

import Pdl.Substitution
import Pdl.Fresh
import Pdl.Star

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

open HasVocabulary

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

-- TODO: it seems default 200000 is not enough for theorem below?!
set_option maxHeartbeats 2000000

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
            rw [List.map_eq_map_iff]
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



-- ### Preparation for Boxes: Test Profiles

-- def TestProfile (α : Program) : Type := {L // L ∈ (testsOfProgram α).sublists}
-- NOTE: Replaced "TestProfile" with "List Formula".

/-- Type of test profiles for a given program. -/
def TP (α : Program) : Type := {τ // τ ∈ testsOfProgram α} → Bool

instance : Fintype (TP α) := by
  unfold TP
  apply Pi.fintype

theorem TP_eq_iff {α} {ℓ ℓ' : TP α} : (ℓ = ℓ') ↔ ∀ τ ∈ (testsOfProgram α).attach, ℓ τ = ℓ' τ := by
  constructor
  · intro ℓ_eq_ℓ _ _
    simp_all
  · intro rhs
    simp_all
    unfold TP at *
    ext τ
    apply rhs

-- Coercions of TP α to the subprograms of α.
-- These are needed to re-use `ℓ` in recursive calls of `F` and `P` below.
instance : CoeOut (TP (α ⋓ β)) (TP α) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by cases τ; simp [testsOfProgram]; left; assumption⟩  ⟩
instance : CoeOut (TP (α ⋓ β)) (TP β) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by cases τ; simp [testsOfProgram]; right; assumption⟩  ⟩
instance : CoeOut (TP (α ;' β)) (TP α) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by cases τ; simp [testsOfProgram]; left; assumption⟩  ⟩
instance : CoeOut (TP (α ;' β)) (TP β) :=
  ⟨fun ℓ => fun τ => ℓ ⟨τ.val, by cases τ; simp [testsOfProgram]; right; assumption⟩  ⟩
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
  simp (config := {contextual := true}) [TP, List.mem_filter, Function.funext_iff]

/-- σ^ℓ -/
def signature (α : Program) (ℓ : TP α) : Formula :=
  Con $ (testsOfProgram α).attach.map (fun τ => if ℓ τ then τ.val else ~τ.val)

theorem signature_iff {W} {M : KripkeModel W} {w : W} :
    evaluate M w (signature α ℓ) ↔ ∀ τ ∈ (testsOfProgram α).attach, ℓ τ ↔ evaluate M w τ.val := by
  simp [signature, conEval]
  constructor
  · intro w_ℓ
    intro τ τ_in
    cases em (ℓ ⟨τ, τ_in⟩)
    · specialize w_ℓ τ τ τ_in
      aesop
    · specialize w_ℓ (~τ) τ τ_in
      aesop
  · aesop

-- Now come the three facts about test profiles and signatures.

-- unused
theorem top_equiv_disj_TP {L} : ∀ α, L = testsOfProgram α → tautology (dis ((allTP α).map (signature α))) := by
  intro α
  intro L_def
  intro W M w
  rw [disEval]
  induction L generalizing α -- probably bad idea, try `cases α` at start instead?
  case nil =>
    simp [TP,signature,allTP]
    rw [← L_def]
    simp
  case cons τ L IH =>
    simp [TP,signature,allTP,conEval] at *
    rw [← L_def]
    cases em (evaluate M w τ)
    · sorry
    · sorry

-- unused?
theorem signature_conbot_iff_neq : contradiction (signature α ℓ ⋀ signature α ℓ') ↔  ℓ ≠ ℓ' := by
  simp only [ne_eq]
  rw [TP_eq_iff]
  constructor
  · intro contrasign
    simp_all [TP, contradiction, signature_iff]
    -- QUESTION: do we need to choose a model here? How to do it?
    -- specialize contrasign Bool sorry false -- ??
    sorry
  · intro ldiff
    intro W M w
    simp_all only [List.mem_attach, forall_true_left, Subtype.forall, not_forall, evaluate, not_and]
    rcases ldiff with ⟨τ, τ_in, disagree⟩
    simp_all [signature, conEval]
    intro ℓ_conform
    cases em (ℓ ⟨τ,τ_in⟩)
    · specialize ℓ_conform τ τ τ_in
      simp_all only [ite_true, forall_true_left]
      use (~τ)
      constructor
      · use τ, τ_in
        simp_all
      · simp
        assumption
    · specialize ℓ_conform (~τ) τ τ_in
      simp_all only [Bool.not_eq_true, ite_false, evaluate, forall_true_left]
      use τ
      constructor
      · use τ, τ_in
        simp_all
      · assumption

-- unused?
theorem equiv_iff_TPequiv : φ ≡ ψ  ↔  ∀ ℓ : TP α, φ ⋀ signature α ℓ ≡ ψ ⋀ signature α ℓ := by
  sorry

-- ### Boxes: F, P, X and the Φ_□ set

-- NOTE: In P and Xset we use lists not sets, to eventually make formulas.

def F : (α : Program) → (ℓ : TP α) → List Formula
| ·_ , _ => ∅
| ?'τ, ℓ => if ℓ ⟨τ, by simp [testsOfProgram]⟩ then [τ] else [~τ]
| α⋓β, ℓ => F α ℓ ∪ F β ℓ
| α;'β, ℓ => F α ℓ ∪ F β ℓ
| ∗α, ℓ => F α ℓ

def P : (α : Program) →  (ℓ : TP α) → List (List Program)
| ·a, _ => [ [(·a : Program)] ]
| ?' τ, ℓ => if ℓ ⟨τ, by simp [testsOfProgram]⟩ then [ [] ] else ∅
| α ⋓ β, ℓ => P α ℓ ∪ P β ℓ
| α;'β, ℓ => ((P α ℓ).filter (. != [])).map (fun as => as ++ [β])
             ∪ (if [] ∈ P α ℓ then (P β ℓ) else [])
| ∗α, ℓ => [ [] ] ∪ ((P α ℓ).filter (. != [])).map (fun as => as ++ [∗α])

def Xset (α : Program) (ℓ : TP α) (ψ : Formula) : List Formula :=
  F α ℓ ++ (P α ℓ).map (fun as => Formula.boxes as ψ)

/-- Φ_□(αs,ψ) -/
def unfoldBox (α : Program) (φ : Formula) : List (List Formula) :=
  (allTP α).map (fun ℓ => Xset α ℓ φ)

theorem F_mem_iff_neg α (ℓ : TP α) φ :
    φ ∈ F α ℓ ↔ ∃ τ, ∃ (h : τ ∈ testsOfProgram α), φ = (~τ) ∧ ℓ ⟨τ,h⟩ = false ∨ φ = τ ∧ ℓ ⟨τ,h⟩ = true := by

  cases α
  all_goals
    simp_all [testsOfProgram, F]
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
    simp_all [testsOfProgram, P]
  case union α β =>
    intro δ_in
    have IHα := P_monotone α ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    have IHβ := P_monotone β ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    simp [testsOfProgram, P] at *
    cases δ_in <;> simp_all
  case sequence α β =>
    intro δ_in
    have IHα := P_monotone α ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    have IHβ := P_monotone β ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
    simp [testsOfProgram, P] at *
    cases δ_in
    case inl δ_in =>
      rcases δ_in with ⟨δ', δ'_in, def_δ⟩
      subst def_δ
      left
      use δ'
      constructor
      · apply List.mem_filter_of_mem
        · have := List.filter_subset _ δ'_in
          simp_all only
        · have := List.of_mem_filter δ'_in
          simp_all only
      · rfl
    · aesop
  case star α =>
    intro δ_in
    cases em (δ = [])
    · simp_all [testsOfProgram, P]
    · have IHα := P_monotone α ℓ ℓ' (by intro τ τ_in; apply h; simp_all)
      simp_all [testsOfProgram, P]
      rcases δ_in with ⟨δ', δ'_in, def_δ⟩
      subst def_δ
      use δ'
      constructor
      · simp_all only [List.append_eq_nil, List.cons_ne_self, and_false, not_false_eq_true]
        apply List.mem_filter_of_mem
        · have := List.filter_subset _ δ'_in
          simp_all only
        · have := List.of_mem_filter δ'_in
          simp_all only
      · rfl
  case test τ =>
    simp_all [testsOfProgram, P]
    aesop

theorem P_goes_down : γ ∈ δ → δ ∈ P α ℓ → (if isAtomic α then γ = α else if isStar α then lengthOfProgram γ ≤  lengthOfProgram α else lengthOfProgram γ < lengthOfProgram α) := by
  intro γ_in δ_in
  cases α
  all_goals
    simp_all [isAtomic, isStar, P]
  case sequence α β =>
    cases δ_in
    case inl δ_in =>
      rcases δ_in with ⟨αs, αs_in, def_δ⟩
      subst def_δ
      simp_all
      cases γ_in
      case inl γ_in =>
        have IH := P_goes_down γ_in (List.mem_of_mem_filter αs_in)
        cases em (isAtomic α) <;> cases em (isStar α)
        all_goals (simp_all;try linarith)
      case inr γ_in =>
        subst γ_in
        linarith
    case inr δ_in =>
      cases em ([] ∈ P α ℓ)
      · simp_all
        have IH := P_goes_down γ_in δ_in
        cases em (isAtomic β) <;> cases em (isStar β)
        all_goals (simp_all;try linarith)
      · simp_all
  case union α β =>
    cases δ_in
    case inl δ_in =>
      have IH := P_goes_down γ_in δ_in
      cases em (isAtomic α) <;> cases em (isStar α)
      all_goals (simp_all;try linarith)
    case inr δ_in =>
      have IH := P_goes_down γ_in δ_in
      cases em (isAtomic β) <;> cases em (isStar β)
      all_goals (simp_all;try linarith)
  case star α =>
    cases δ
    case nil =>
      exfalso; cases γ_in
    case cons =>
      simp_all only [false_or]
      rcases δ_in with ⟨αs, αs_in, def_δ⟩
      cases em (γ ∈ αs)
      case inl γ_in =>
        have IH := P_goes_down γ_in (List.mem_of_mem_filter αs_in)
        cases em (isAtomic α) <;> cases em (isStar α)
        all_goals (simp_all;try linarith)
      case inr γ_not_in =>
        have : γ = (∗α) := by rw [← def_δ] at γ_in; simp at γ_in; tauto
        subst_eqs
        simp
  case test τ =>
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩)
    · simp_all
    · simp_all

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

theorem keepFreshF α ℓ (x_notin : x ∉ voc α) : ∀ φ ∈ F α ℓ, x ∉ voc φ := by
  intro φ φ_in
  cases α
  all_goals
    simp [F, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList] at *
  case test τ =>
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩) <;> simp_all [vocabOfFormula]
  case sequence α β =>
    have := keepFreshF α ℓ x_notin.1
    have := keepFreshF β ℓ x_notin.2
    aesop
  case union α β =>
    have := keepFreshF α ℓ x_notin.1
    have := keepFreshF β ℓ x_notin.2
    aesop
  case star α =>
    have := keepFreshF α ℓ x_notin
    aesop

theorem keepFreshP α ℓ (x_notin : x ∉ voc α) : ∀ δ ∈ P α ℓ, x ∉ voc δ := by
  intro δ δ_in
  cases α
  all_goals
    simp_all [P, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList]
  case test τ =>
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩) <;> simp_all [vocabOfFormula, Vocab.fromList]
  case sequence α β =>
    have IHα := keepFreshP α ℓ x_notin.1
    have IHβ := keepFreshP β ℓ x_notin.2
    simp_all [P, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList, List.mem_filter, Vocab.fromListProgram_map_iff]
    rcases δ_in with (⟨δ', δ'_in, def_δ⟩ | δ_in)
    · subst def_δ
      have := IHα _ δ'_in.1
      simp_all [Vocab.fromListProgram_map_iff]
      aesop
    · cases em ([] ∈ P α ℓ) <;> simp_all
      have := IHβ _ δ_in
      simp_all [Vocab.fromListProgram_map_iff]
  case union α β =>
    have IHα := keepFreshP α ℓ x_notin.1
    have IHβ := keepFreshP β ℓ x_notin.2
    simp_all [P, voc, vocabOfFormula, vocabOfProgram, Vocab.fromList, List.mem_filter]
    aesop
  case star α =>
    have IHα := keepFreshP α ℓ x_notin
    rcases δ_in with (_ | ⟨δ', δ'_in, def_δ⟩)
    · subst_eqs
      simp_all [voc, Vocab.fromList, Finset.not_mem_empty, not_false_eq_true]
    · subst def_δ
      rw [Vocab.fromListProgram_map_iff]
      simp_all [voc, Vocab.fromList, Finset.not_mem_empty, not_false_eq_true]
      rintro γ (γ_in_δ' | γ_def)
      · simp_all [List.mem_filter]
        have := IHα _ δ'_in.1
        simp_all [Vocab.fromListProgram_map_iff]
      · subst γ_def
        simp [vocabOfProgram]
        aesop

-- NOTE: see `P_goes_down` for proof inspiration, and later make it a consequence of this?
-- Maybe unused / to be deleted?
theorem boxHelperTermination γ (ℓ : TP γ) ψ :
    ( ∀ δ ∈ P γ ℓ,
        (∀ α ∈ δ, α ∈ subprograms γ)
      ∧ ((h : δ.length > 0) → isAtomic (δ.get (Fin.ofNat' 0 h)))
      ∧ (∀ iα ∈ δ.enum, iα.2 = γ ↔ ((isAtomic γ ∧ iα.1 = n ∧ iα.1 = 1) ∨ (isStar (γ) ∧ iα.1 = n)))
    )
    ∧
    ( ∀ φ ∈ (unfoldBox γ ψ).join,
        φ ∈ fischerLadner [⌈γ⌉ψ]
      ∧ (  (φ = ψ)
         ∨ (∃ τ ∈ testsOfProgram γ, φ = (~τ))
         ∨ (∃ δ, φ = (⌈a⌉⌈⌈δ⌉⌉ψ) ∧ ∀ α ∈ δ, α ∈ subprograms γ))
    ) := by
  constructor
  · sorry
  · sorry

theorem boxHelperTP α (ℓ : TP α) :
 --    (∀ τ, (~τ.val) ∈ F α ℓ → (ℓ τ = false ∨ ℓ (~τ) = true)) -- removed.
    (Con (F α ℓ) ≡ signature α ℓ)
  ∧ ∀ ψ, (Con (Xset α ℓ ψ) ≡ Con ((P α ℓ).map (fun αs => ⌈⌈αs⌉⌉ψ)) ⋀ signature α ℓ )
    := by
  refine ⟨?_, ?_⟩
  /-
  · intro τ τ_in
    have := F_mem_iff_neg α ℓ (~τ)
    aesop
    -/
  · intro W M w
    simp [conEval, signature, F]
    sorry
    /-
    intro w_ℓ
    intro φ φ_in
    have := F_mem_iff_neg α ℓ φ
    rw [this] at φ_in
    clear this
    rcases φ_in with ⟨τ, τ_in, φ_def, not_ℓ_τ⟩
    specialize w_ℓ φ τ
    aesop
    -/
  · intro ψ
    intro W M w
    simp [conEval, Xset]
    sorry
    /-
    constructor
    · intro lhs
      aesop
    · rintro rhs φ (φ_in_F | ⟨δ,δ_in,def_φ⟩)
      · rw [F_mem_iff_neg α ℓ φ] at φ_in_F
        rcases φ_in_F with ⟨τ, τ_in, φ_def, not_ℓ_τ⟩
        subst φ_def
        simp_all [signature, conEval, F]
        specialize w_sign (~τ) τ
        aesop
      · aesop
    -/

theorem guardToStar (x : Nat) β χ0 χ1 ρ ψ
    (x_notin_beta : Sum.inl x ∉ HasVocabulary.voc β)
    (beta_equiv : (⌈β⌉·x) ≡ (((·x) ⋀ χ0) ⋁ χ1))
    (rho_imp_repl : ρ ⊨ (repl_in_F x ρ) (χ0 ⋁ χ1))
    (rho_imp_psi : ρ ⊨ ψ)
  : ρ ⊨ ⌈(∗β)⌉ψ := by
  -- The key observation in this proof is the following:
  have fortysix :
       ∀ W M (w v : W), (M,w) ⊨ ρ → relate M β w v → (M,v) ⊨ ρ := by
    intro W M w v w_rho w_β_v
    have : (M,w) ⊨ ⌈β⌉ρ := by
      have by_ass : (M,w) ⊨ (repl_in_F x ρ) (χ0 ⋁ χ1) := by apply rho_imp_repl; simp; exact w_rho; simp
      have obvious : (M,w) ⊨ (repl_in_F x ρ) (·x) := by simp; exact w_rho
      have : (M,w) ⊨ (repl_in_F x ρ) (((·x) ⋀ χ0) ⋁ χ1) := by
        simp [evaluate,relate,modelCanSemImplyForm] at *
        tauto
      -- Now we want to "rewrite" with beta_equiv.
      have := repl_in_F_equiv x ρ beta_equiv
      simp only [repl_in_F, beq_self_eq_true, reduceIte, Formula.or] at this
      have nox : repl_in_P x ρ β = β := repl_in_P_non_occ_eq x_notin_beta
      rw [nox] at this
      rw [equiv_iff _ _ this]
      simp_all
    -- It is then immediate...
    simp [evaluate,relate,modelCanSemImplyForm] at this
    exact this v w_β_v -- This finishes the proof of (46).
  -- To see how the Lemma follows from this...
  intro W M w
  simp only [List.mem_singleton, forall_eq, evaluate, relate]
  intro w_rho v w_bS_v
  induction w_bS_v using Relation.ReflTransGen.head_induction_on
  · apply rho_imp_psi; simp; assumption; simp
  case head u1 u2 u1_b_u2 _ IH =>
    apply IH
    exact fortysix W M u1 u2 w_rho u1_b_u2

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
      unfold_let ℓ;
      simp [allTP];
      use ((testsOfProgram γ).filter (fun τ => evaluate M w τ))
      simp only [List.filter_sublist, true_and]
      apply funext
      simp only [Subtype.forall]
      intro τ τ_in
      simp [List.mem_filter]
      tauto
    have := goal ℓ W M w -- using the claim proven by induction
    simp_all
    refine ⟨ℓ, ℓ_in, ?_⟩
    apply this
    unfold_let ℓ
    simp_all [signature, conEval]
    intro τ _
    split_ifs <;> simp_all
  · intro w_Cons
    rw [disEval] at w_Cons
    rcases w_Cons with ⟨φ, φ_in, w_Xℓ⟩
    simp at φ_in
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
        unfold_let ℓ' at ℓ'_τ_false
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
        unfold_let ℓ'
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
      · unfold_let
        simp_all [signature, conEval]
        aesop
    simp_all

/-- Induction claim for `localBoxTruth`. -/
theorem localBoxTruthI γ ψ (ℓ :TP γ) :
    (⌈γ⌉ψ) ⋀ signature γ ℓ ≡ Con (Xset γ ℓ ψ) ⋀ signature γ ℓ := by
  intro W M w
  cases γ
  case atom_prog a =>
    simp_all [TP, testsOfProgram, signature, conEval, Xset, P, F]
  case test τ =>
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩ )
    · simp_all [TP, testsOfProgram, signature, conEval, Xset, P, F]
    · simp_all [TP, testsOfProgram, signature, conEval, Xset, P, F]
  case union α β =>
    have IHα := localBoxTruthI α ψ ℓ W M w
    have IHβ := localBoxTruthI β ψ ℓ W M w
    simp only [evaluate, and_congr_left_iff, relate] at *
    intro w_sign_ℓ
    specialize IHα ?_
    · simp_all [signature, conEval, testsOfProgram]; intro f τ τ_in; apply w_sign_ℓ; aesop
    specialize IHβ ?_
    · simp_all [signature, conEval, testsOfProgram]; intro f τ τ_in; apply w_sign_ℓ; aesop
    -- rewrite using semantics of union and the two IH:
    have : (∀ (v : W), relate M α w v ∨ relate M β w v → evaluate M v ψ)
        ↔ ((∀ (v : W), relate M α w v → evaluate M v ψ)
         ∧ (∀ (v : W), relate M β w v → evaluate M v ψ)) := by aesop
    rw [this, IHα, IHβ]
    clear this IHα IHβ
    -- signature is true, so we can add it for free:
    have : ∀ φ, evaluate M w φ
              ↔ evaluate M w (φ ⋀ signature (α⋓β) ℓ) := by simp_all [conEval]
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
          simp [signature,conEval] at w_sign_ℓ
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
          simp [signature,conEval] at w_sign_ℓ
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
    · simp_all [signature, conEval, testsOfProgram]; intro f τ τ_in; apply w_sign_ℓ; aesop
    specialize IHβ ?_
    · simp_all [signature, conEval, testsOfProgram]; intro f τ τ_in; apply w_sign_ℓ; aesop
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
      simp_all [TP, testsOfProgram, signature, conEval, Xset, P, F]
      rintro φ ((φ_in_Fα|φ_in_Fβ) | ⟨δ, ⟨(δ_from_Pα|δ_from_Pβ), def_φ⟩⟩)
      · tauto
      · rw [F_mem_iff_neg β ℓ φ] at φ_in_Fβ
        rcases φ_in_Fβ with ⟨τ, τ_in, def_φ, not_ℓ_τ⟩
        apply w_sign_ℓ _ τ
        · simp_all
        · simp_all [testsOfProgram]
      · subst def_φ
        apply lhs
        right
        rcases δ_from_Pα with ⟨δ_α, bla, def_δ⟩
        use δ_α
        subst def_δ
        simp_all [boxes_append, List.mem_filter]
      · subst def_φ
        cases em ([] ∈ P α ℓ)
        · simp_all
          apply IHβ.1 ?_ (⌈⌈δ⌉⌉ψ) <;> clear IHβ
          · right; aesop
          · have := lhs (⌈β⌉ψ)
            simp at this; apply this; clear this -- sounds like daft punk ;-)
            right
            use []
            simp_all
        · simp_all
    · intro rhs
      rw [conEval]
      simp_all [TP, testsOfProgram, signature, conEval, Xset, P, F]
      rintro φ (φ_in_Fα|⟨δ, φ_in_Pα, def_φ⟩)
      · tauto
      · subst def_φ
        cases em (δ = [])
        · simp_all only [Formula.boxes.eq_1, evaluate, ite_true] -- uses IHβ
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
            left
            rw [List.mem_filter]
            aesop
          · simp_all
            rw [List.mem_filter]
            aesop
  case star β =>
    let ρ := dis ((allTP (∗β)).map (fun ℓ => Con (Xset (∗β) ℓ ψ)))
    suffices goal : (⌈∗β⌉ψ) ≡ ρ by
      specialize goal W M w
      simp only [evaluate, relate] at goal
      constructor
      · intro lhs
        simp at lhs
        simp
        constructor
        · unfold_let ρ at goal
          have := goal.1 lhs.1
          rw [disEval] at this
          simp at this
          rcases this with ⟨ℓ', _, w_Xℓ'⟩
          clear goal ρ
          simp [conEval, Xset, F, P] at *
          rintro f (f_in_Fβ|(f_eq_ψ|f_from_Pβ))
          · simp [signature, conEval] at lhs
            have := lhs.2 f
            clear lhs
            rw [F_mem_iff_neg] at f_in_Fβ
            simp at f_in_Fβ
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
              · have := (List.mem_filter.1 δ_in).2
                subst_eqs
              · rw [List.mem_filter]
                rw [List.mem_filter] at δ_in
                simp_all only [bne_iff_ne, ne_eq, not_false_eq_true, and_true]
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
                specialize this τ τ (by simp [testsOfProgram]; exact τ_in)
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
          unfold_let ρ
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
        unfold_let ρ
        simp only [List.mem_singleton, forall_eq, disEval, List.mem_map, exists_exists_and_eq_and]
        use ℓ'
        constructor
        · exact allTP_mem ℓ'
        · simp [conEval, Xset]
          rintro f (f_in_F| ⟨δ, δ_in, def_f⟩)
          · simp [F_mem_iff_neg] at f_in_F
            unfold_let ℓ' at f_in_F
            aesop
          · subst def_f
            specialize step ℓ' W M w
            simp only [List.mem_singleton, forall_eq, and_imp] at step
            rw [conEval] at step
            simp [evaluate, relate, signature,conEval] at step
            apply step <;> aesop
      intro ℓ W M w
      simp only [List.mem_singleton, forall_eq]
      intro hyp
      rw [conEval]
      intro f f_in
      simp at f_in
      rcases f_in with ⟨αs, αs_in, def_f⟩
      subst def_f
      cases em (αs = [])
      · subst_eqs
        simp [Formula.boxes]
        simp at hyp
        apply hyp.1
        exact Relation.ReflTransGen.refl
      · simp [P] at αs_in
        simp_all
        rcases αs_in with ⟨δ, δ_in, def_αs⟩
        subst def_αs
        -- Notes now prove a ⊨ but we prove → to avoid a model switch here.
        have : evaluate M w (⌈β⌉⌈∗β⌉ψ) → evaluate M w (⌈⌈δ⌉⌉⌈∗β⌉ψ) := by
          have IHβ_thm := localBoxTruth_connector _ _ (localBoxTruthI β (⌈∗β⌉ψ))
          have := (IHβ_thm  W M w).1
          clear IHβ_thm
          simp [disEval, conEval, Xset] at *
          intro hyp2
          specialize this hyp2
          rcases this with ⟨ℓ', ℓ'_in, w_Xℓ'⟩
          apply w_Xℓ'
          right
          use δ
          rw [List.mem_filter] at δ_in
          rcases δ_in with ⟨δ_in, δ_not_empty⟩
          simp_all
          apply P_monotone β ℓ ℓ' -- γ ℓ' ℓ ?_ δ δ_in_P
          · simp
            -- again remains to show that ℓ τ → ℓ' τ
            intro τ τ_in ℓ_τ
            by_contra wrong
            absurd w_Xℓ'
            simp
            use ~τ
            rw [F_mem_iff_neg]
            constructor
            · left
              simp_all
            · have := hyp.2
              simp [evaluate, signature, conEval] at *
              specialize this τ τ (by simp [testsOfProgram]; exact τ_in)
              simp at this
              apply this
              intro
              simp_all
          · simp; exact δ_in
        simp [boxes_append]
        simp at this
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
      have x_not_in_β : Sum.inl x ∉ HasVocabulary.voc β := by apply freshVarProg_is_fresh
      let φ ℓ := Con ((P β ℓ).map (fun αs => ⌈⌈αs⌉⌉·x))
      let T0 := (allTP β).filter (fun ℓ => [] ∈ P β ℓ)
      let T1 := (allTP β).filter (fun ℓ => [] ∉ P β ℓ)
      let φ' ℓ := Con (((P β ℓ).filter (fun αs => αs ≠ [])).map (fun αs => ⌈⌈αs⌉⌉·x))
      let χ0 : Formula := dis (T0.map (fun ℓ => Con (F _ ℓ) ⋀ φ' ℓ))
      let χ1 : Formula := dis (T1.map (fun ℓ => Con (F _ ℓ) ⋀ φ' ℓ))
      have := guardToStar x β χ0 χ1 ρ ψ x_not_in_β ?_ ?_ ?_ W M w
      simp only [List.mem_singleton, forall_eq] at this
      exact this
      all_goals
        clear W M w
        intro W M w
      -- remaining goals are the conditions of `guardToStar`
      · -- ⌈β⌉x ≡ (x⋀χ0)⋁χ1
        have IHβ_thm := localBoxTruth_connector _ _ (localBoxTruthI β (·x)) W M w
        rw [IHβ_thm]
        clear IHβ_thm
        simp only [Xset, evalDis, disEval, List.mem_map, exists_exists_and_eq_and, conEval, List.mem_append, evaluate]
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
            · unfold_let χ0 T0 φ'
              simp [disEval, conEval]
              use ℓ
              simp_all [List.mem_filter]
              intro δ δ_in δ_not_empty
              apply w_Xβ
              right
              aesop
          · right -- choose χ1
            unfold_let χ1 T1 φ'
            simp [disEval, conEval]
            use ℓ
            simp_all [List.mem_filter]
            intro δ δ_in _
            apply w_Xβ
            right
            aesop
        · rintro (⟨w_c, w_χ0⟩ | w_χ1)
          · unfold_let χ0 T0 φ' at w_χ0
            simp [disEval, conEval, List.mem_filter] at w_χ0
            rcases w_χ0 with ⟨ℓ, w_Xℓ⟩
            use ℓ
            simp_all
            rintro φ (φ_in_Fβ | ⟨δ, δ_in, def_φ⟩)
            · aesop
            · subst def_φ
              cases em (δ = [])
              · simp_all
              case inr δ_not_empty =>
                apply w_Xℓ.2.2 _ _ δ_in δ_not_empty
                simp [Formula.boxes]
          · unfold_let χ1 T1 φ' at w_χ1
            simp [disEval, conEval, List.mem_filter] at w_χ1
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
        unfold_let ρ at w_ρ
        simp [disEval] at w_ρ
        rcases w_ρ with ⟨ℓ, _, w_Xℓ⟩ -- here we get ℓ
        simp only [repl_in_or, evalDis]
        simp [conEval, conEval, Xset] at w_Xℓ
        unfold_let χ0 χ1 T0 T1 φ φ'
        clear χ0 χ1 T0 T1 φ φ'
        cases em ([] ∈ P β ℓ) -- based on this, go left or right
        case inl empty_in_Pβ =>
          left
          simp_all [disEval, conEval, repl_in_dis, repl_in_Con]
          use ℓ
          simp_all [List.mem_filter]
          constructor
          · apply allTP_mem
          · constructor
            · intro φ φ_in_Fβ
              apply w_Xℓ
              left
              simp [F]
              convert φ_in_Fβ
              -- now we use that x ∉ β implies x ∉ φ ∈ Fβ
              apply repl_in_F_non_occ_eq
              apply keepFreshF β ℓ x_not_in_β
              simp
              exact φ_in_Fβ
            · intro δ δ_in_Pβ δ_not_empty
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
          simp_all [disEval, conEval, repl_in_dis, repl_in_Con]
          use ℓ
          simp_all [List.mem_filter]
          constructor
          · apply allTP_mem
          · constructor
            · intro φ φ_in_Fβ
              apply w_Xℓ
              left
              simp [F]
              convert φ_in_Fβ
              -- now we use that x ∉ β implies x ∉ φ ∈ Fβ
              apply repl_in_F_non_occ_eq
              apply keepFreshF β ℓ x_not_in_β
              simp
              exact φ_in_Fβ
            · intro δ δ_in_Pβ δ_not_empty
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
        unfold_let ρ
        simp [disEval, conEval, Xset, P]
        intro ℓ_whatever _ hyp
        apply hyp
        right
        left
        rfl

theorem localBoxTruth γ ψ : (⌈γ⌉ψ) ≡ dis ( (allTP γ).map (fun ℓ => Con (Xset γ ℓ ψ)) ) :=
  localBoxTruth_connector γ ψ (localBoxTruthI γ ψ)

theorem existsBoxFP γ (v_γ_w : relate M γ v w) (ℓ : TP γ) (v_conF : (M,v) ⊨ Con (F γ ℓ)) :
    ∃ δ ∈ P γ ℓ, relateSeq M δ v w := by
  cases γ
  case atom_prog =>
    simp [F, P, relateSeq] at *
    exact v_γ_w
  case test τ =>
    simp only [relate] at v_γ_w
    rcases v_γ_w with ⟨v_is_w, v_τ⟩
    cases em (ℓ ⟨τ, by simp [testsOfProgram]⟩ )
    all_goals
      simp_all [modelCanSemImplyForm, evaluatePoint, F, P, relateSeq, TP, testsOfProgram]
  case union α β =>
    simp at v_γ_w
    cases v_γ_w
    case inl v_α_w =>
      have v_Fℓα : evaluate M v (Con (F α ℓ)) := by simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHα := existsBoxFP α v_α_w ℓ v_Fℓα -- using coercion from above :-)
      rcases IHα with ⟨δ, _⟩
      use δ
      simp_all [P]
    case inr v_β_w =>
      have v_Fℓβ : evaluate M v (Con (F β ℓ)) := by simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHβ := existsBoxFP β v_β_w ℓ v_Fℓβ -- using coercion from above :-)
      rcases IHβ with ⟨δ, _⟩
      use δ
      simp_all [P]
  case sequence α β =>
    simp only [relate] at v_γ_w
    rcases v_γ_w with ⟨u, v_α_u, u_β_w⟩
    have v_Fℓα : evaluate M v (Con (F α ℓ)) := by simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
    have IHα := existsBoxFP α v_α_u ℓ v_Fℓα -- using coercion from above :-)
    rcases IHα with ⟨δ, ⟨δ_in, v_δ_u⟩⟩
    -- "We make a further case distinction"
    cases em (δ = [])
    case inl hyp =>
      subst hyp
      simp [relateSeq] at v_δ_u
      subst v_δ_u
      rename relate M β v w => v_β_w
      have v_Fℓβ : evaluate M v (Con (F β ℓ)) := by simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHβ := existsBoxFP β v_β_w ℓ v_Fℓβ -- using coercion from above :-)
      rcases IHβ with ⟨η, ⟨η_in, v_η_w⟩⟩
      use η
      simp_all [P]
    case inr _ =>
      use δ ++ [β]
      simp_all [P, relateSeq]
      constructor
      · left
        apply List.mem_filter_of_mem δ_in (by aesop)
      · simp [relateSeq_append]
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
      have v_Fℓβ : evaluate M v (Con (F β ℓ)) := by simp_all [conEval, F, modelCanSemImplyForm, evaluatePoint]
      have IHβ := existsBoxFP β v_β_u ℓ v_Fℓβ
      rcases IHβ with ⟨δ, ⟨δ_in, v_δ_w⟩⟩
      have claim : δ ≠ [] := by by_contra hyp; subst hyp; simp_all [relateSeq];
      use δ ++ [∗β]
      simp_all [P, relateSeq]
      constructor
      · apply List.mem_filter_of_mem δ_in (by aesop)
      · simp [relateSeq_append]
        use u
