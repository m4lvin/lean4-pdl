-- UNFOLD

import Pdl.Semantics
import Pdl.Vocab
import Pdl.Discon
import Pdl.Substitution

def ε : List Program := [] -- the empty program

-- ### Diamonds: H, Y and Φ_⋄

def H : Program → List (List Formula × List Program)
| ·a => [ ([], [·a]) ]
| ?'τ => [ ([τ], ε) ]
| α ⋓ β => H α ∪ H β
| α;'β => ((H α).map (fun ⟨F,δ⟩ =>
            if δ = ε
              then ((H β).map (fun ⟨G,δ'⟩ => [⟨F ∪ G, δ'⟩])).join
              else [⟨F, δ ++ [β]⟩])
          ).join
| ∗α => [ (∅,ε) ] ∪ ((H α).map (fun (F,δ) => if δ = ε then [] else [(F, δ ++ [∗α])])).join

def Yset : (List Formula × List Program) → (Formula) → List Formula
| ⟨F, δ⟩, φ => F ∪ [ ~ Formula.boxes δ φ ]

/-- Φ_◇(α,ψ) -/
def unfoldDiamond (α : Program) (φ : Formula) : List (List Formula) :=
  (H α).map (fun Fδ => Yset Fδ φ)

theorem guardToStarDiamond (x : Char)
    (x_notin_beta : x ∉ HasVocabulary.voc β)
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

theorem localDiamondTruth γ ψ : (~⌈γ⌉ψ) ≡ dis ( (H γ).map (fun Fδ => Con (Yset Fδ ψ)) ) := by
  intro W M w
  cases γ
  case atom_prog a =>
    simp [evaluate, H]
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
      cases em (δ = ε)
      case inl δ_is_ε => -- tricky case where we actually need the IH for β
        subst δ_is_ε
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
          · use Fs, ε
            simp only [reduceIte, and_true]
            exact Fδ_in
          · tauto
        · simp only [Yset, conEval, List.mem_union_iff, List.mem_singleton] at *
          intro f f_in
          specialize w_Con f
          specialize claim f
          tauto
      case inr δ_not_ε => -- the easy case?
        unfold H
        use ⟨Fs, δ ++ [β]⟩
        constructor
        · simp
          use [(Fs, δ ++ [β])]
          constructor
          · use Fs, δ
            simp_all only [List.mem_map, Prod.exists, reduceIte, and_self]
          · simp_all only [List.mem_map, Prod.exists, List.mem_singleton]
        · simp [Yset, conEval, boxes_append] at *
          intro f f_in
          apply w_Con
          tauto
    -- upwards direction in notes:
    · rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_Con⟩⟩ -- ⟨⟨l, ⟨⟨a, b, ⟨ab_in, def_l⟩⟩, f_in_l⟩⟩, w_f⟩⟩
      simp [H] at Fδ_in
      rcases Fδ_in with ⟨l, ⟨Gs, γ, ⟨Gγ_in, def_l⟩⟩, Gγ_in_l⟩
      subst def_l
      cases em (γ = ε)
      case inl δ_is_ε => -- tricky case where we actually need the IH for β
        subst δ_is_ε
        simp at Gγ_in_l
        rcases Gγ_in_l with ⟨l, ⟨⟨aaa, bbb, ⟨_in_Hβ,def_l⟩ ⟩, Fsδ_in_l⟩ ⟩
        subst def_l
        simp
        use Gs, ε
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
      case inr δ_not_ε => -- the easy case
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
    -- Note that we are switching model now.
    clear W M w; intro W M w
    constructor
    · -- left to right, done second in notes
      -- BIG PROBLEM: Char is finite. We cannot get fresh variables!!
      -- ideas to solve this:
      -- - refactor everything to allow different types! - hard but useful?
      -- - replace Char with Nat? - easier?
      let x : Char := sorry
      have x_not_in : x ∉ HasVocabulary.voc β := sorry
      -- NOTE the use of ⊥ below - matters for rhs-to-lhs in first Lemma condition.
      let σ0 : Formula := dis $
        (H β).map (fun (F,δ) => if δ = ε then Con F else ⊥)
      let σ1 : Formula := dis $
        ((H β).map (fun (F,δ) => if δ ≠ ε then Con ((~ Formula.boxes δ (~(·x : Formula))) :: F) else ⊥))
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
          cases em (δ = ε)
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
            · use (Fs, ε)
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
            · cases em (δ = ε)
              case inl δ_is_ε =>
                subst δ_is_ε
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
            · cases em (δ = ε)
              case inl δ_is_ε => exfalso; simp_all
                -- this case works because we used ⊥ above!
              case inr δ_notEmpty =>
                simp_all [conEval]
                intro f f_in
                cases f_in
                · apply w_.2; assumption
                · subst_eqs; simp; exact w_.1
      · -- Lemma condition that is done last in notes:
        unfold_let σ1
        simp
        have := repl_in_model_sat_iff x ρ
        simp only [modelCanSemImplyForm, evaluatePoint] at this
        rw [this, disEval, helper]
        clear this
        rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, repl_w_⟩⟩
        unfold_let ρ
        have δ_notEmpty : δ ≠ ε := by by_contra; subst_eqs; simp at repl_w_
        -- unsure from here on
        simp_all [disEval, helper, H]
        -- on what formula do we actually want to apply th IH here?
        have IHβ := localDiamondTruth β ψ W M w
        -- QUESTION: do the notes use the first Lemma condition here for the first step?
        sorry
      · -- Second Lemma condition
        intro w_nPsi
        unfold_let ρ
        rw [disEval, helper]
        simp [H, conEval, Yset]
        left
        simp at w_nPsi
        exact w_nPsi
    · -- right to left, done first in notes
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
        have : ∃ γ, δ = γ ++ [∗β] ∧ γ ≠ ε ∧ (Fs,γ) ∈ H β := by aesop
        rcases this with ⟨γ, ⟨δ_def, γ_notEmpty, Fγ_in⟩⟩
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

-- TODO move to Semantics.lean when sure that this is a good way to define it
def relateSeq {W} (M : KripkeModel W) (δ : List Program) (w v : W) : Prop :=
  match δ with
  | [] => w = v
  | (α::as) => ∃ u, relate M α w u ∧ relateSeq M as u v

theorem existsDiamondH (w_γ_v : relate M γ w v) :
    ∃ Fδ ∈ H γ, (M,v) ⊨ Fδ.1 ∧ relateSeq M Fδ.2 w v := by
  cases γ
  case atom_prog =>
    simp [H, relateSeq] at *
    exact w_γ_v
  case test τ =>
    sorry
  case union =>
    sorry
  case sequence α β =>
    sorry
  case star α =>
    sorry

-- ### Preparation for Boxes: Test Profiles

-- def TestProfile (α : Program) : Type := {L // L ∈ (testsOfProgram α).sublists}
-- NOTE: Replaced "TestProfile" with "List Formula".

/-- List of all test profiles for a given program. -/
def TP (α : Program) : List (List Formula) := (testsOfProgram α).sublists

/-- σ^ℓ -/
def signature (α : Program) (ℓ : List Formula) : Formula :=
  Con $ (testsOfProgram α).map (fun τ => if τ ∈ ℓ then τ else ~τ)

-- Now come the three facts about test profiles and signatures.

theorem top_equiv_disj_TP {L} : ∀ α, L = testsOfProgram α → tautology (dis ((TP α).map (signature α))) := by
  intro α
  intro L_def
  intro W M w
  rw [disEval]
  induction L
  case nil =>
    simp [TP,signature]
    rw [← L_def]
    simp
  case cons τ L IH =>
    simp [TP,signature] at *
    rw [← L_def]
    cases em (evaluate M w τ)
    · sorry
    · sorry

theorem signature_conbot_iff_neq : contradiction (signature α ℓ ⋀ signature α ℓ')  ↔  ℓ ≠ ℓ' := by
  constructor
  · intro contrasign
    sorry
  · intro ldiff
    have := @List.ext _ ℓ ℓ'
    sorry

theorem equiv_iff_TPequiv : φ ≡ ψ  ↔  ∀ ℓ ∈ TP α, φ ⋀ signature α ℓ ≡ ψ ⋀ signature α ℓ := by
  sorry

/-
-- Coercion of TestProfiles to subprograms
-- These WERE needed to re-use `l` in the recursive calls of `F`.

instance : CoeOut (TestProfile (α ⋓ β)) (TestProfile α) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inl f_in⟩⟩
instance : CoeOut (TestProfile (α ⋓ β)) (TestProfile β) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inr f_in⟩⟩

instance : CoeOut (TestProfile (α ;' β)) (TestProfile α) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inl f_in⟩⟩
instance : CoeOut (TestProfile (α ;' β)) (TestProfile β) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inr f_in⟩⟩

instance : CoeOut (TestProfile (∗α)) (TestProfile α) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram]; exact f_in⟩⟩
-/

-- ### Boxes: F, P, X and the Φ_□ set

-- NOTE: In P and Xset we use lists not sets, to eventually make formulas.

def F : (Program × List Formula) → List Formula
| ⟨·_, _⟩ => ∅
| ⟨?' τ, l⟩ => if τ ∈ l then ∅ else {~τ}
| ⟨α ⋓ β, l⟩ => F ⟨α, l⟩ ∪ F ⟨β, l⟩
| ⟨α;'β, l⟩ => F ⟨α, l⟩ ∪ F ⟨β, l⟩
| ⟨∗α, l⟩ => F ⟨α, l⟩

def P : (Program × List Formula) → List (List Program)
| ⟨·a, _⟩ => [ [(·a : Program)] ]
| ⟨?' τ, l⟩ => if τ ∈ l then ∅ else [ [] ]
| ⟨α ⋓ β, l⟩ => P ⟨α, l⟩ ∪ P ⟨β, l⟩
| ⟨α;'β, l⟩ => (P ⟨α,l⟩ \ [ε]).map (fun as => as ++ [β])
             ∪ (if ε ∈ P ⟨α,l⟩ then (P ⟨β,l⟩ \ [ε]) else [])
| ⟨∗α, l⟩ => [ ε ] ∪ (P (⟨α, l⟩) \ [ε]).map (fun as => as ++ [∗α])

def Xset (α : Program) (l : List Formula) (ψ : Formula) : List Formula :=
  F ⟨α, l⟩ ++ (P ⟨α, l⟩).map (fun as => Formula.boxes as ψ)

/-- Φ_□(αs,ψ) -/
-- *Not* the same as `Formula.boxes`.
def unfoldBox α ψ := { Xset α l ψ | l ∈ TP α }

-- TODO Lemma 21 with parts 1) and 2)

-- TODO Lemma 22 with parts 1) and 2) and 3)

theorem guardToStar (x : Char)
    (x_notin_beta : x ∉ HasVocabulary.voc β)
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

/-- Induction claim for `localBoxTruth`. -/
-- NOTE: "signature γ" or should it be "signature α" here?!?
theorem localBoxTruth' γ ψ ℓ : (⌈γ⌉ψ) ⋀ signature γ ℓ ≡ Con (Xset γ ℓ ψ) ⋀ signature γ ℓ := by
  cases γ
  case atom_prog =>
    sorry
  case test =>
    sorry
  case union =>
    sorry
  case sequence =>
    sorry
  case star =>

    -- use guardToStar
    sorry

theorem localBoxTruth : (⌈γ⌉ψ) ≡ dis ( (TP γ).map (fun ℓ => Con (Xset γ ℓ ψ)) ) := by
  have := localBoxTruth' γ ψ
  -- clearly this suffices to prove the theorem ;-)
  sorry

theorem existsBoxFP (v_γ_w : relate M γ v w) (ℓ_in : ℓ ∈ TP γ) (v_conF : (M,v) ⊨ Con (F (γ,ℓ))) :
    ∃ δ ∈ P (γ,ℓ), relateSeq M δ v w := by
  cases γ
  case atom_prog =>
    simp [F, P, relateSeq] at *
    exact v_γ_w
  all_goals sorry
