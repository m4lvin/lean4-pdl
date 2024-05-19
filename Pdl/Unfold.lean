-- UNFOLD

import Pdl.Semantics
import Pdl.Vocab
import Pdl.Discon
import Pdl.Substitution

def ε : List Program := [] -- the empty program

-- ### Diamonds

def H : Program → List (List Formula × List Program)
| ·a => [ ([], [·a]) ]
| ?'τ => [ ([τ], ε) ]
| α ⋓ β => H α ∪ H β
| α;'β => ((H α).map (fun ⟨F,δ⟩ =>
            if δ = ε
              then ((H β).map (fun ⟨G,δ⟩ => if δ = ε then [] else [⟨F ∪ G, δ⟩])).join
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
    have IHα := localDiamondTruth α ψ W M w
    have IHβ := localDiamondTruth β ψ W M w
    simp [evaluate, H, Yset, disEval] at *
    -- "This case is straightforward"
    sorry
  case sequence α β =>
    have IHα := localDiamondTruth α ψ W M w
    have IHβ := localDiamondTruth β ψ W M w
    simp [evaluate, H, Yset, disEval] at *
    -- "This case follows from the following computation"
    sorry
  case star β =>
    have IHβ := localDiamondTruth β ψ W M w
    simp [evaluate, H, Yset, disEval] at *
    let ρ := dis ((H (∗β)).map (fun Fδ => Con Fδ.1 ⋀ (~ Formula.boxes Fδ.2 ψ)))
    -- use guardToStarDiamond somewhere below!
    -- "then our goal will be ..."
    sorry

-- TODO move to Semantics when sure that this is a good way to define it
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

-- ### Test Profiles

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

-- ### F, P, X and the Φ_□ set

-- NOTE: In P and Xset
-- We use lists here because we eventually want to make formulas.

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
def PhiSet α ψ := { Xset α l ψ | l ∈ TP α }

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
