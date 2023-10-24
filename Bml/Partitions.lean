-- PARTITIONS
import Syntax
import Tableau
import Semantics
import Soundness
import Vocabulary

#align_import partitions

open HasVocabulary HasSat

def Partition :=
  Finset Formula × Finset Formula
#align partition Partition

-- Definition 24
def PartInterpolant (X1 X2 : Finset Formula) (θ : Formula) :=
  voc θ ⊆ voc X1 ∩ voc X2 ∧ ¬Satisfiable (X1 ∪ {~θ}) ∧ ¬Satisfiable (X2 ∪ {θ})
#align partInterpolant PartInterpolant

-- Lemma 14
theorem botInter {X1 X2} : ⊥ ∈ X1 ∪ X2 → ∃ θ, PartInterpolant X1 X2 θ :=
  by
  intro bot_in_X
  refine' if side : ⊥ ∈ X1 then _ else _
  · -- case ⊥ ∈ X1
    use⊥
    constructor
    · unfold voc; unfold vocabOfFormula; simp
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩; specialize sat ⊥; simp at *; tauto
  · -- case ⊥ ∈ X2
    have : ⊥ ∈ X2 := by simp at *; tauto
    use~⊥
    constructor
    · unfold voc; unfold vocabOfFormula; simp
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · specialize sat (~~⊥); simp at *; unfold Evaluate at sat ; tauto
    · specialize sat ⊥; simp at *; tauto
#align botInter botInter

theorem notInter {X1 X2 ϕ} : ϕ ∈ X1 ∪ X2 ∧ ~ϕ ∈ X1 ∪ X2 → ∃ θ, PartInterpolant X1 X2 θ :=
  by
  intro in_both; cases' in_both with pIn nIn
  by_cases pSide : ϕ ∈ X1; all_goals by_cases nSide : ~ϕ ∈ X1
  -- four cases
  · use⊥
    -- both in X1
    constructor
    · unfold voc; unfold vocabOfFormula; simp
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · have h1 := sat ϕ; have h2 := sat (~ϕ); simp at *; tauto
    · specialize sat ⊥; simp at *; tauto
  · use ϕ
    -- ϕ ∈ X1 and ~ϕ ∈ X2
    constructor
    · unfold voc; intro a aIn; simp; constructor
      exact vocElem_subs_vocSet pSide aIn
      have h : ~ϕ ∈ X2 := by rw [Finset.mem_union] at nIn ; tauto
      have := vocElem_subs_vocSet h
      simp at *
      tauto
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · simp at *; tauto
    · have h1 := sat (~ϕ); simp at *; tauto
  · use~ϕ
    -- ~ϕ ∈ X1 and ϕ ∈ X2
    constructor
    · unfold voc; intro a aIn; simp; constructor
      exact vocElem_subs_vocSet nSide aIn
      have h : ϕ ∈ X2 := by rw [Finset.mem_union] at pIn ; tauto
      have := vocElem_subs_vocSet h
      simp at *
      tauto
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · have h1 := sat (~ϕ); simp at *; tauto
    · simp at *; tauto
  · use~⊥
    -- both in X2
    constructor
    · unfold voc; unfold vocabOfFormula; simp
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · specialize sat (~~⊥); simp at *; unfold Evaluate at sat ; tauto
    · have h1 := sat ϕ; have h2 := sat (~ϕ); simp at *; tauto
#align notInter notInter

theorem notnotInterpolantX1 {X1 X2 ϕ θ} :
    ~~ϕ ∈ X1 → PartInterpolant (X1 \ {~~ϕ} ∪ {ϕ}) (X2 \ {~~ϕ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro notnotphi_in_X1 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreserved X1 (~~ϕ) ϕ notnotphi_in_X1 (by unfold voc; simp)]
    change voc θ ⊆ voc (X1 \ {~~ϕ} ∪ {ϕ}) ∩ voc X2
    have : voc (X2 \ {~~ϕ}) ⊆ voc X2 := vocErase
    intro a aInVocTheta
    simp at *
    rw [Finset.subset_inter_iff] at vocSub 
    tauto
  constructor
  all_goals by_contra hyp; unfold satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · have : satisfiable (X1 \ {~~ϕ} ∪ {ϕ} ∪ {~θ}) :=
      by
      unfold satisfiable
      use W, M, w
      intro ψ psi_in_newX_u_notTheta
      simp at psi_in_newX_u_notTheta 
      cases psi_in_newX_u_notTheta
      · apply sat; rw [psi_in_newX_u_notTheta]; simp at *
      cases psi_in_newX_u_notTheta
      · rw [psi_in_newX_u_notTheta]; apply of_not_not
        change Evaluate (M, w) (~~ϕ)
        apply sat (~~ϕ); simp; right; assumption
      · apply sat; simp at *; tauto
    tauto
  · have : satisfiable (X2 \ {~~ϕ} ∪ {θ}) :=
      by
      unfold satisfiable at *
      use W, M, w
      intro ψ psi_in_newX2cupTheta
      apply sat; simp at *; tauto
    tauto
#align notnotInterpolantX1 notnotInterpolantX1

theorem notnotInterpolantX2 {X1 X2 ϕ θ} :
    ~~ϕ ∈ X2 → PartInterpolant (X1 \ {~~ϕ}) (X2 \ {~~ϕ} ∪ {ϕ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro notnotphi_in_X2 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreserved X2 (~~ϕ) ϕ notnotphi_in_X2 (by unfold voc; simp)]
    change voc θ ⊆ voc X1 ∩ voc (X2 \ {~~ϕ} ∪ {ϕ})
    have : voc (X1 \ {~~ϕ}) ⊆ voc X1 := vocErase
    intro a aInVocTheta
    simp at *
    rw [Finset.subset_inter_iff] at vocSub 
    tauto
  constructor
  all_goals by_contra hyp; unfold satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply noSatX1
    unfold satisfiable
    use W, M, w
    intro ψ psi_in_newX_u_notTheta
    simp at psi_in_newX_u_notTheta 
    cases psi_in_newX_u_notTheta
    · apply sat; rw [psi_in_newX_u_notTheta]; simp at *
    cases psi_in_newX_u_notTheta
    · apply sat; simp at *; tauto
  · apply noSatX2
    unfold satisfiable at *
    use W, M, w
    intro ψ psi_in_newX2cupTheta
    simp at psi_in_newX2cupTheta 
    cases psi_in_newX2cupTheta
    -- ! changed from here onwards
    · apply sat; simp at *; tauto
    cases psi_in_newX2cupTheta
    · rw [psi_in_newX2cupTheta]; apply of_not_not
      change Evaluate (M, w) (~~ϕ)
      apply sat (~~ϕ); simp; right; assumption
    · apply sat; simp at *; tauto
#align notnotInterpolantX2 notnotInterpolantX2

theorem conInterpolantX1 {X1 X2 ϕ ψ θ} :
    ϕ⋏ψ ∈ X1 → PartInterpolant (X1 \ {ϕ⋏ψ} ∪ {ϕ, ψ}) (X2 \ {ϕ⋏ψ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro con_in_X1 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreservedTwo (ϕ⋏ψ) ϕ ψ con_in_X1 (by unfold voc vocabOfFormula vocabOfSetFormula; simp)]
    have : voc (X2 \ {ϕ⋏ψ}) ⊆ voc X2 := vocErase
    intro a aInVocTheta
    rw [Finset.subset_inter_iff] at vocSub 
    simp at *
    tauto
  constructor
  all_goals by_contra hyp; unfold satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply noSatX1
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]; apply sat (~θ); simp
    cases pi_in
    · rw [pi_in]; specialize sat (ϕ⋏ψ) (by simp; exact con_in_X1); unfold Evaluate at sat ; tauto
    cases pi_in
    · rw [pi_in]; specialize sat (ϕ⋏ψ) (by simp; exact con_in_X1); unfold Evaluate at sat ; tauto
    · exact sat π (by simp; tauto)
  · apply noSatX2
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]; apply sat θ; simp
    · apply sat; simp at *; tauto
#align conInterpolantX1 conInterpolantX1

theorem conInterpolantX2 {X1 X2 ϕ ψ θ} :
    ϕ⋏ψ ∈ X2 → PartInterpolant (X1 \ {ϕ⋏ψ}) (X2 \ {ϕ⋏ψ} ∪ {ϕ, ψ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro con_in_X2 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreservedTwo (ϕ⋏ψ) ϕ ψ con_in_X2 (by unfold voc vocabOfFormula vocabOfSetFormula; simp)]
    have : voc (X1 \ {ϕ⋏ψ}) ⊆ voc X1 := vocErase
    intro a aInVocTheta
    rw [Finset.subset_inter_iff] at vocSub 
    simp at *
    tauto
  constructor
  all_goals by_contra hyp; unfold satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply noSatX1
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]; apply sat (~θ); simp
    · apply sat; simp at *; tauto
  · apply noSatX2
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]; apply sat θ; simp
    cases pi_in
    · rw [pi_in]; specialize sat (ϕ⋏ψ) (by simp; right; exact con_in_X2); unfold Evaluate at sat ;
      tauto
    cases pi_in
    · rw [pi_in]; specialize sat (ϕ⋏ψ) (by simp; right; exact con_in_X2); unfold Evaluate at sat ;
      tauto
    · exact sat π (by simp; tauto)
#align conInterpolantX2 conInterpolantX2

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:570:6: unsupported: specialize @hyp -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:570:6: unsupported: specialize @hyp -/
theorem nCoInterpolantX1 {X1 X2 ϕ ψ θa θb} :
    ~(ϕ⋏ψ) ∈ X1 →
      PartInterpolant (X1 \ {~(ϕ⋏ψ)} ∪ {~ϕ}) (X2 \ {~(ϕ⋏ψ)}) θa →
        PartInterpolant (X1 \ {~(ϕ⋏ψ)} ∪ {~ψ}) (X2 \ {~(ϕ⋏ψ)}) θb →
          PartInterpolant X1 X2 (~(~θa⋏~θb)) :=
  by
  intro nCo_in_X1 tA_is_chInt tB_is_chInt
  rcases tA_is_chInt with ⟨a_vocSub, a_noSatX1, a_noSatX2⟩
  rcases tB_is_chInt with ⟨b_vocSub, b_noSatX1, b_noSatX2⟩
  unfold PartInterpolant
  constructor
  · unfold voc vocabOfFormula
    rw [Finset.subset_inter_iff]
    constructor; all_goals rw [Finset.union_subset_iff] <;> constructor <;> intro a aIn
    · have sub : voc (~ϕ) ⊆ voc (~(ϕ⋏ψ)) := by unfold voc vocabOfFormula;
        apply Finset.subset_union_left
      have claim := vocPreservedSub (~(ϕ⋏ψ)) (~ϕ) nCo_in_X1 sub
      rw [Finset.subset_iff] at claim 
      specialize claim a
      rw [Finset.subset_iff] at a_vocSub 
      specialize a_vocSub aIn
      finish
    · have sub : voc (~ψ) ⊆ voc (~(ϕ⋏ψ)) := by unfold voc vocabOfFormula;
        apply Finset.subset_union_right
      have claim := vocPreservedSub (~(ϕ⋏ψ)) (~ψ) nCo_in_X1 sub
      rw [Finset.subset_iff] at claim 
      specialize claim a
      rw [Finset.subset_iff] at b_vocSub 
      specialize b_vocSub aIn
      finish
    · rw [Finset.subset_iff] at a_vocSub 
      specialize a_vocSub aIn
      have : voc (X2 \ {~(ϕ⋏ψ)}) ⊆ voc X2 := vocErase
      unfold voc at *
      simp at *
      tauto
    · rw [Finset.subset_iff] at b_vocSub 
      specialize b_vocSub aIn
      have : voc (X2 \ {~(ϕ⋏ψ)}) ⊆ voc X2 := vocErase
      unfold voc at *
      simp at *
      tauto
  constructor
  all_goals by_contra hyp; unfold satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply a_noSatX1
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]; specialize sat (~~(~θa⋏~θb)); simp at sat ; unfold Evaluate at *; simp at sat ;
      tauto
    cases pi_in
    · rw [pi_in]
      by_contra; apply b_noSatX1
      unfold satisfiable
      use W, M, w
      intro χ chi_in
      simp at chi_in 
      cases chi_in
      · rw [chi_in]; specialize sat (~~(~θa⋏~θb)); simp at sat ; unfold Evaluate at *; simp at sat ;
        tauto
      cases chi_in
      · rw [chi_in]; specialize sat (~(ϕ⋏ψ)) (by simp; exact nCo_in_X1); unfold Evaluate at *;
        simp at *; tauto
      · apply sat; simp; tauto
    · apply sat; simp; tauto
  · apply a_noSatX2
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]
      by_contra; apply b_noSatX2
      unfold satisfiable
      use W, M, w
      intro χ chi_in
      simp at chi_in 
      cases chi_in
      · rw [chi_in]; specialize sat (~(~θa⋏~θb)); simp at sat ; unfold Evaluate at *; simp at sat ;
        tauto
      · apply sat; simp; tauto
    · apply sat; simp; tauto
#align nCoInterpolantX1 nCoInterpolantX1

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:570:6: unsupported: specialize @hyp -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:570:6: unsupported: specialize @hyp -/
theorem nCoInterpolantX2 {X1 X2 ϕ ψ θa θb} :
    ~(ϕ⋏ψ) ∈ X2 →
      PartInterpolant (X1 \ {~(ϕ⋏ψ)}) (X2 \ {~(ϕ⋏ψ)} ∪ {~ϕ}) θa →
        PartInterpolant (X1 \ {~(ϕ⋏ψ)}) (X2 \ {~(ϕ⋏ψ)} ∪ {~ψ}) θb → PartInterpolant X1 X2 (θa⋏θb) :=
  by
  intro nCo_in_X2 tA_is_chInt tB_is_chInt
  rcases tA_is_chInt with ⟨a_vocSub, a_noSatX1, a_noSatX2⟩
  rcases tB_is_chInt with ⟨b_vocSub, b_noSatX1, b_noSatX2⟩
  unfold PartInterpolant
  constructor
  · unfold voc vocabOfFormula
    rw [Finset.subset_inter_iff]
    constructor; all_goals rw [Finset.union_subset_iff] <;> constructor <;> intro a aIn
    · rw [Finset.subset_iff] at a_vocSub 
      specialize a_vocSub aIn
      have claim : voc (X1 \ {~(ϕ⋏ψ)}) ⊆ voc X1 := vocErase
      unfold voc at claim 
      simp at *
      tauto
    · rw [Finset.subset_iff] at b_vocSub 
      specialize b_vocSub aIn
      have claim : voc (X1 \ {~(ϕ⋏ψ)}) ⊆ voc X1 := vocErase
      unfold voc at claim 
      simp at *
      tauto
    · have sub : voc (~ϕ) ⊆ voc (~(ϕ⋏ψ)) := by unfold voc vocabOfFormula;
        apply Finset.subset_union_left
      have claim := vocPreservedSub (~(ϕ⋏ψ)) (~ϕ) nCo_in_X2 sub
      rw [Finset.subset_iff] at claim 
      specialize claim a
      rw [Finset.subset_iff] at a_vocSub 
      specialize a_vocSub aIn
      finish
    · have sub : voc (~ψ) ⊆ voc (~(ϕ⋏ψ)) := by unfold voc vocabOfFormula;
        apply Finset.subset_union_right
      have claim := vocPreservedSub (~(ϕ⋏ψ)) (~ψ) nCo_in_X2 sub
      rw [Finset.subset_iff] at claim 
      specialize claim a
      rw [Finset.subset_iff] at b_vocSub 
      specialize b_vocSub aIn
      finish
  constructor
  all_goals by_contra hyp; unfold satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply a_noSatX1
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]
      by_contra; apply b_noSatX1
      unfold satisfiable
      use W, M, w
      intro χ chi_in
      simp at chi_in 
      cases chi_in
      · rw [chi_in]; specialize sat (~(θa⋏θb)); simp at sat ; unfold Evaluate at *; simp at sat ;
        simp at h ; tauto
      · apply sat; simp; tauto
    · apply sat; simp; tauto
  · apply a_noSatX2
    unfold satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in 
    cases pi_in
    · rw [pi_in]; specialize sat (θa⋏θb); simp at sat ; unfold Evaluate at *; tauto
    cases pi_in
    · rw [pi_in]
      by_contra; apply b_noSatX2
      unfold satisfiable
      use W, M, w
      intro χ chi_in
      simp at chi_in 
      cases chi_in
      · rw [chi_in]; specialize sat (θa⋏θb); simp at sat ; unfold Evaluate at *; tauto
      cases chi_in
      · rw [chi_in]; specialize sat (~(ϕ⋏ψ)); simp at sat ; unfold Evaluate at *; simp at sat ;
        simp at h ; tauto
      · apply sat; simp; tauto
    · apply sat; simp; tauto
#align nCoInterpolantX2 nCoInterpolantX2

theorem localTabToInt :
    ∀ n X,
      n = lengthOfSet X →
        ∀ {X1 X2},
          X = X1 ∪ X2 →
            (∃ ltX : LocalTableau X,
                ∀ Y1 Y2, Y1 ∪ Y2 ∈ endNodesOf ⟨X, ltX⟩ → ∃ θ, PartInterpolant Y1 Y2 θ) →
              ∃ θ, PartInterpolant X1 X2 θ :=
  by
  intro N
  apply Nat.strong_induction_on N
  intro n IH
  intro X lenX_is_n X1 X2 defX pt
  rcases pt with ⟨pt, nextInter⟩
  cases pt
  case byLocalRule X B lr next =>
    cases lr
    -- The bot and not cases use Lemma 14
    case bot X bot_in_X => rw [defX] at bot_in_X ; exact botInter bot_in_X
    case not X ϕ in_both => rw [defX] at in_both ; exact notInter in_both
    case neg X ϕ
      notnotphi_in =>
      have notnotphi_in_union : ~~ϕ ∈ X1 ∪ X2 := by rw [defX] at notnotphi_in ; assumption
      simp at *
      cases notnotphi_in_union
      · -- case ~~ϕ ∈ X1
        subst defX
        let newX1 := X1 \ {~~ϕ} ∪ {ϕ}
        let newX2 := X2 \ {~~ϕ}
        -- to deal with possible overlap
        have yclaim : newX1 ∪ newX2 ∈ {(X1 ∪ X2) \ {~~ϕ} ∪ {ϕ}} :=
          by
          rw [Finset.mem_singleton]
          change X1 \ {~~ϕ} ∪ {ϕ} ∪ X2 \ {~~ϕ} = (X1 ∪ X2) \ {~~ϕ} ∪ {ϕ}
          ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set m := lengthOfSet (newX1 ∪ newX2)
        have m_lt_n : m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.neg notnotphi_in) (newX1 ∪ newX2) yclaim
        have nextNextInter :
          ∀ Y1 Y2 : Finset Formula,
            Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, next (newX1 ∪ newX2) yclaim⟩ →
              Exists (PartInterpolant Y1 Y2) :=
          by intro Y1 Y2; apply nextInter Y1 Y2 (newX1 ∪ newX2); finish
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _) (next (newX1 ∪ newX2) yclaim) nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact notnotInterpolantX1 notnotphi_in_union theta_is_chInt
      · -- case ~~ϕ ∈ X2
        ---- based on copy-paste from previous case, changes marked with "!" ---
        subst defX
        let newX1 := X1 \ {~~ϕ}
        -- to deal with possible overlap -- !
        let newX2 := X2 \ {~~ϕ} ∪ {ϕ}
        -- !
        have yclaim : newX1 ∪ newX2 ∈ {(X1 ∪ X2) \ {~~ϕ} ∪ {ϕ}} :=
          by
          rw [Finset.mem_singleton]
          change X1 \ {~~ϕ} ∪ (X2 \ {~~ϕ} ∪ {ϕ}) = (X1 ∪ X2) \ {~~ϕ} ∪ {ϕ}
          -- !
          ext1 a;
          constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set m := lengthOfSet (newX1 ∪ newX2)
        have m_lt_n : m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.neg notnotphi_in) (newX1 ∪ newX2) yclaim
        have nextNextInter :
          ∀ Y1 Y2 : Finset Formula,
            Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, next (newX1 ∪ newX2) yclaim⟩ →
              Exists (PartInterpolant Y1 Y2) :=
          by intro Y1 Y2; apply nextInter Y1 Y2 (newX1 ∪ newX2); finish
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _) (next (newX1 ∪ newX2) yclaim) nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact notnotInterpolantX2 notnotphi_in_union theta_is_chInt
    case con X ϕ ψ
      con_in_X =>
      have con_in_union : ϕ⋏ψ ∈ X1 ∨ ϕ⋏ψ ∈ X2 := by rw [defX] at con_in_X ; simp at con_in_X ;
        assumption
      cases con_in_union
      · -- case ϕ⋏ψ ∈ X1
        subst defX
        let newX1 := X1 \ {ϕ⋏ψ} ∪ {ϕ, ψ}
        let newX2 := X2 \ {ϕ⋏ψ}
        have yclaim : newX1 ∪ newX2 ∈ {(X1 ∪ X2) \ {ϕ⋏ψ} ∪ {ϕ, ψ}} :=
          by
          rw [Finset.mem_singleton]
          change X1 \ {ϕ⋏ψ} ∪ {ϕ, ψ} ∪ X2 \ {ϕ⋏ψ} = (X1 ∪ X2) \ {ϕ⋏ψ} ∪ {ϕ, ψ}
          ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set m := lengthOfSet (newX1 ∪ newX2)
        have m_lt_n : m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.con con_in_X) (newX1 ∪ newX2) yclaim
        have nextNextInter :
          ∀ Y1 Y2 : Finset Formula,
            Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, next (newX1 ∪ newX2) yclaim⟩ →
              Exists (PartInterpolant Y1 Y2) :=
          by
          intro Y1 Y2 Y_in; apply nextInter; unfold endNodesOf
          simp only [endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨newX1 ∪ newX2, yclaim, Y_in⟩
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          by
          apply IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _)
          fconstructor
          apply next (newX1 ∪ newX2) yclaim; exact nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact conInterpolantX1 con_in_union theta_is_chInt
      · -- case ϕ⋏ψ ∈ X2
        subst defX
        let newX1 := X1 \ {ϕ⋏ψ}
        let newX2 := X2 \ {ϕ⋏ψ} ∪ {ϕ, ψ}
        have yclaim : newX1 ∪ newX2 ∈ {(X1 ∪ X2) \ {ϕ⋏ψ} ∪ {ϕ, ψ}} :=
          by
          rw [Finset.mem_singleton]
          change X1 \ {ϕ⋏ψ} ∪ (X2 \ {ϕ⋏ψ} ∪ {ϕ, ψ}) = (X1 ∪ X2) \ {ϕ⋏ψ} ∪ {ϕ, ψ}
          ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set m := lengthOfSet (newX1 ∪ newX2)
        have m_lt_n : m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.con con_in_X) (newX1 ∪ newX2) yclaim
        have nextNextInter :
          ∀ Y1 Y2 : Finset Formula,
            Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, next (newX1 ∪ newX2) yclaim⟩ →
              Exists (PartInterpolant Y1 Y2) :=
          by
          intro Y1 Y2 Y_in; apply nextInter; unfold endNodesOf
          simp only [endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨newX1 ∪ newX2, yclaim, Y_in⟩
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          by
          apply IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _)
          fconstructor
          apply next (newX1 ∪ newX2) yclaim; exact nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact conInterpolantX2 con_in_union theta_is_chInt
    case nCo X ϕ ψ
      nCo_in_X =>
      have nCo_in_union : ~(ϕ⋏ψ) ∈ X1 ∨ ~(ϕ⋏ψ) ∈ X2 := by rw [defX] at nCo_in_X ; simp at nCo_in_X ;
        assumption
      cases nCo_in_union
      · -- case ~(ϕ⋏ψ) ∈ X1
        subst defX
        -- splitting rule!
        -- first get an interpolant for the ~ϕ branch:
        let a_newX1 := X1 \ {~(ϕ⋏ψ)} ∪ {~ϕ}
        let a_newX2 := X2 \ {~(ϕ⋏ψ)}
        have a_yclaim :
          a_newX1 ∪ a_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ψ}} :
              Finset (Finset Formula)) :=
          by simp; left; ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set a_m := lengthOfSet (a_newX1 ∪ a_newX2)
        have a_m_lt_n : a_m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.nCo nCo_in_X) (a_newX1 ∪ a_newX2) a_yclaim
        have a_childInt : Exists (PartInterpolant a_newX1 a_newX2) :=
          by
          apply IH a_m a_m_lt_n (a_newX1 ∪ a_newX2) (refl _) (refl _)
          fconstructor
          apply next (a_newX1 ∪ a_newX2) a_yclaim
          -- remains to show nextNextInter
          intro Y1 Y2 Y_in;
          apply nextInter; unfold endNodesOf
          simp only [endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨a_newX1 ∪ a_newX2, a_yclaim, Y_in⟩
        cases' a_childInt with θa a_theta_is_chInt
        -- now get an interpolant for the ~ψ branch:
        let b_newX1 := X1 \ {~(ϕ⋏ψ)} ∪ {~ψ}
        let b_newX2 := X2 \ {~(ϕ⋏ψ)}
        have b_yclaim :
          b_newX1 ∪ b_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ψ}} :
              Finset (Finset Formula)) :=
          by simp; right; ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set b_m := lengthOfSet (b_newX1 ∪ b_newX2)
        have b_m_lt_n : b_m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.nCo nCo_in_X) (b_newX1 ∪ b_newX2) b_yclaim
        have b_childInt : Exists (PartInterpolant b_newX1 b_newX2) :=
          by
          apply IH b_m b_m_lt_n (b_newX1 ∪ b_newX2) (refl _) (refl _)
          fconstructor
          apply next (b_newX1 ∪ b_newX2) b_yclaim
          -- remains to show nextNextInter
          intro Y1 Y2 Y_in;
          apply nextInter; unfold endNodesOf
          simp only [endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨b_newX1 ∪ b_newX2, b_yclaim, Y_in⟩
        cases' b_childInt with θb b_theta_is_chInt
        -- finally, combine the two interpolants using disjunction:
        use~(~θa⋏~θb)
        exact nCoInterpolantX1 nCo_in_union a_theta_is_chInt b_theta_is_chInt
      · -- case ~(ϕ⋏ψ) ∈ X2
        subst defX
        -- splitting rule!
        -- first get an interpolant for the ~ϕ branch:
        let a_newX1 := X1 \ {~(ϕ⋏ψ)}
        let a_newX2 := X2 \ {~(ϕ⋏ψ)} ∪ {~ϕ}
        have a_yclaim :
          a_newX1 ∪ a_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ψ}} :
              Finset (Finset Formula)) :=
          by simp; left; ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set a_m := lengthOfSet (a_newX1 ∪ a_newX2)
        have a_m_lt_n : a_m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.nCo nCo_in_X) (a_newX1 ∪ a_newX2) a_yclaim
        have a_childInt : Exists (PartInterpolant a_newX1 a_newX2) :=
          by
          apply IH a_m a_m_lt_n (a_newX1 ∪ a_newX2) (refl _) (refl _)
          fconstructor
          apply next (a_newX1 ∪ a_newX2) a_yclaim
          -- remains to show nextNextInter
          intro Y1 Y2 Y_in;
          apply nextInter; unfold endNodesOf
          simp only [endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨a_newX1 ∪ a_newX2, a_yclaim, Y_in⟩
        cases' a_childInt with θa a_theta_is_chInt
        -- now get an interpolant for the ~ψ branch:
        let b_newX1 := X1 \ {~(ϕ⋏ψ)}
        let b_newX2 := X2 \ {~(ϕ⋏ψ)} ∪ {~ψ}
        have b_yclaim :
          b_newX1 ∪ b_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋏ψ)} ∪ {~ψ}} :
              Finset (Finset Formula)) :=
          by simp; right; ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set b_m := lengthOfSet (b_newX1 ∪ b_newX2)
        have b_m_lt_n : b_m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.nCo nCo_in_X) (b_newX1 ∪ b_newX2) b_yclaim
        have b_childInt : Exists (PartInterpolant b_newX1 b_newX2) :=
          by
          apply IH b_m b_m_lt_n (b_newX1 ∪ b_newX2) (refl _) (refl _)
          fconstructor
          apply next (b_newX1 ∪ b_newX2) b_yclaim
          -- remains to show nextNextInter
          intro Y1 Y2 Y_in;
          apply nextInter; unfold endNodesOf
          simp only [endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨b_newX1 ∪ b_newX2, b_yclaim, Y_in⟩
        cases' b_childInt with θb b_theta_is_chInt
        -- finally, combine the two interpolants using conjunction:
        use θa⋏θb
        exact nCoInterpolantX2 nCo_in_union a_theta_is_chInt b_theta_is_chInt
  case sim X X_is_simple =>
    apply nextInter
    unfold endNodesOf
    rw [defX]; simp
#align localTabToInt localTabToInt

theorem vocProj (X) : voc (projection X) ⊆ voc X :=
  by
  unfold voc vocabOfFormula vocabOfSetFormula
  simp
  intro ϕ phi_in_proj
  rw [proj] at phi_in_proj 
  intro a aInVocPhi
  simp
  tauto
#align vocProj vocProj

theorem projUnion {X Y} : projection (X ∪ Y) = projection X ∪ projection Y :=
  by
  unfold projection Finset.biUnion
  ext1
  constructor <;> finish
#align projUnion projUnion

open HasLength

-- tableau interpolation -- IDEA: similar to almostCompleteness
-- part of this is part of Lemma 15
theorem almostTabToInt {X} (ctX : ClosedTableau X) :
    ∀ X1 X2, X = X1 ∪ X2 → ∃ θ, PartInterpolant X1 X2 θ :=
  by
  induction ctX
  case loc X ltX next IH =>
    intro X1 X2 defX
    have nextLtAndInter :
      ∃ ltX : LocalTableau X,
        ∀ Y1 Y2, Y1 ∪ Y2 ∈ endNodesOf ⟨X, ltX⟩ → ∃ θ, PartInterpolant Y1 Y2 θ :=
      by
      use ltX
      intro Y1 Y2 y_is_endOfX
      specialize next (Y1 ∪ Y2) y_is_endOfX
      exact IH (Y1 ∪ Y2) y_is_endOfX Y1 Y2 (refl _)
    exact localTabToInt _ X (refl _) defX nextLtAndInter
  case atm X ϕ notBoxPhi_in_X simpleX ctProjNotPhi
    IH =>
    intro X1 X2 defX
    subst defX
    simp at *
    cases notBoxPhi_in_X
    · -- case ~□ϕ ∈ X1
      let newX1 := projection X1 ∪ {~ϕ}
      let newX2 := projection X2
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ} := by rw [projUnion]; ext1; simp;
        tauto
      rw [← yclaim] at ctProjNotPhi 
      have nextInt : ∃ θ, PartInterpolant newX1 newX2 θ := IH newX1 newX2 (by rw [yclaim]; simp)
      rcases nextInt with ⟨θ, vocSub, unsat1, unsat2⟩
      use~(□~θ)
      repeat' constructor
      -- it remains to show the three properties of the interpolant
      · change voc θ ⊆ voc X1 ∩ voc X2
        have inc1 : voc newX1 ⊆ voc X1 := by
          intro a aIn; unfold voc vocabOfSetFormula Finset.biUnion at *; simp at *
          rcases aIn with ⟨ψ, psi_in_projX1 | psi_is_notPhi⟩
          · use□ψ; change □ψ ∈ X1 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
          · use~(□ϕ); subst psi_is_notPhi; tauto
        have inc2 : voc newX2 ⊆ voc X2 := by
          intro a aIn; unfold voc vocabOfSetFormula Finset.biUnion at *; simp at *
          rcases aIn with ⟨ψ, psi_in_projX2⟩
          · use□ψ; change □ψ ∈ X2 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        intro a aIn; norm_num
        specialize vocSub aIn; simp at vocSub 
        constructor
        apply inc1; tauto
        apply inc2; tauto
      all_goals unfold satisfiable at *
      · by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat1
        use W, M
        --- we use ~□ϕ to get a different world:
        let othersat := sat (~(□ϕ)) (by simp; apply notBoxPhi_in_X)
        unfold Evaluate at othersat 
        simp at othersat 
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX1
        simp at psi_in_newX1 
        cases psi_in_newX1
        · subst psi_in_newX1; specialize sat (~~(□~θ)); unfold Evaluate at *; simp at sat ;
          exact sat v rel_w_v
        cases psi_in_newX1
        · rw [proj] at psi_in_newX1 ; specialize sat (□ψ); unfold Evaluate at sat ; apply sat; simp;
          assumption; assumption
        · subst psi_in_newX1; unfold Evaluate; assumption
      · by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat2
        use W, M
        --- we use ~□~θ to get a different world:
        let othersat := sat (~(□~θ)) (by simp)
        unfold Evaluate at othersat 
        simp at othersat 
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX2
        simp at psi_in_newX2 
        cases psi_in_newX2
        · subst psi_in_newX2; assumption
        · rw [proj] at psi_in_newX2 ; specialize sat (□ψ); unfold Evaluate at sat ; apply sat; simp;
          assumption; assumption
    · -- case ~□ϕ ∈ X2
      let newX1 := projection X1
      let newX2 := projection X2 ∪ {~ϕ}
      ---- what follows is *based* on copying the previous case ----
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ} := by rw [projUnion]; ext1; simp;
        tauto
      rw [← yclaim] at ctProjNotPhi 
      have nextInt : ∃ θ, PartInterpolant newX1 newX2 θ := IH newX1 newX2 (by rw [yclaim]; simp)
      rcases nextInt with ⟨θ, vocSub, unsat1, unsat2⟩
      use□θ
      -- !!
      repeat' constructor
      -- it remains to show the three properties of the interpolant
      · change voc θ ⊆ voc X1 ∩ voc X2
        have inc1 : voc newX1 ⊆ voc X1 := by
          intro a aIn; unfold voc vocabOfSetFormula Finset.biUnion at *; simp at *
          rcases aIn with ⟨ψ, psi_in_projX1⟩
          · use□ψ; change □ψ ∈ X1 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        have inc2 : voc newX2 ⊆ voc X2 := by
          intro a aIn; unfold voc vocabOfSetFormula Finset.biUnion at *; simp at *
          rcases aIn with ⟨ψ, psi_in_projX1 | psi_is_notPhi⟩
          · use□ψ; change □ψ ∈ X2 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
          · use~(□ϕ); subst psi_is_notPhi; tauto
        intro a aIn; norm_num
        specialize vocSub aIn; simp at vocSub 
        constructor
        apply inc1; tauto
        apply inc2; tauto
      all_goals unfold satisfiable at *
      · by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat1
        use W, M
        --- we use ~□θ to get a different world:
        let othersat := sat (~(□θ)) (by simp)
        unfold Evaluate at othersat 
        simp at othersat 
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX1
        simp at psi_in_newX1 
        cases psi_in_newX1
        · subst psi_in_newX1; specialize sat (~(□θ)); unfold Evaluate at *; simp at sat ; tauto
        · rw [proj] at psi_in_newX1 ; specialize sat (□ψ); unfold Evaluate at sat ; apply sat; simp;
          assumption; assumption
      · by_contra hyp
        rcases hyp with ⟨W, M, w, sat⟩
        apply unsat2
        use W, M
        --- we use ~□ϕ to get a different world:
        let othersat := sat (~(□ϕ)) (by simp; assumption)
        unfold Evaluate at othersat 
        simp at othersat 
        rcases othersat with ⟨v, rel_w_v, v_not_phi⟩
        use v
        intro ψ psi_in_newX2
        simp at psi_in_newX2 
        cases psi_in_newX2
        · rw [psi_in_newX2]; specialize sat (□θ); simp at sat ; unfold Evaluate at sat ; apply sat;
          assumption
        cases psi_in_newX2
        · rw [proj] at psi_in_newX2 ; specialize sat (□ψ); simp at sat ; unfold Evaluate at sat ;
          apply sat; right; assumption; assumption
        · rw [psi_in_newX2]; unfold Evaluate; assumption
#align almostTabToInt almostTabToInt

theorem tabToInt {X1 X2} : ClosedTableau (X1 ∪ X2) → ∃ θ, PartInterpolant X1 X2 θ
  | ctX => almostTabToInt ctX X1 X2 (refl _)
#align tabToInt tabToInt

