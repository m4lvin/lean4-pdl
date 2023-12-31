-- PARTITIONS

import Bml.Syntax
import Bml.Tableau
import Bml.Semantics
import Bml.Soundness
import Bml.Vocabulary

open HasVocabulary HasSat

def Partition :=
  Finset Formula × Finset Formula

-- Definition 24
def PartInterpolant (X1 X2 : Finset Formula) (θ : Formula) :=
  voc θ ⊆ voc X1 ∩ voc X2 ∧ ¬Satisfiable (X1 ∪ {~θ}) ∧ ¬Satisfiable (X2 ∪ {θ})

-- Lemma 14
theorem botInter {X1 X2} : ⊥ ∈ X1 ∪ X2 → ∃ θ, PartInterpolant X1 X2 θ :=
  by
  intro bot_in_X
  refine' if side : ⊥ ∈ X1 then _ else _
  · -- case ⊥ ∈ X1
    use ⊥
    constructor
    · unfold voc; simp; tauto
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩; specialize sat ⊥; simp at *
    apply sat
    exact side
  · -- case ⊥ ∈ X2
    have : ⊥ ∈ X2 := by simp at *; tauto
    use ~⊥
    constructor
    · unfold voc; simp; tauto
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · specialize sat (~~⊥); simp at *
    · specialize sat ⊥; simp at *; tauto

theorem notInter {X1 X2 ϕ} : ϕ ∈ X1 ∪ X2 ∧ ~ϕ ∈ X1 ∪ X2 → ∃ θ, PartInterpolant X1 X2 θ :=
  by
  intro in_both; cases' in_both with pIn nIn
  by_cases pSide : ϕ ∈ X1; all_goals by_cases nSide : ~ϕ ∈ X1
  -- four cases
  · use⊥
    -- both in X1
    constructor
    · unfold voc; simp; tauto
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · have h1 := sat ϕ; have h2 := sat (~ϕ); simp at *; tauto
    · specialize sat ⊥; aesop
  · use ϕ
    -- ϕ ∈ X1 and ~ϕ ∈ X2
    constructor
    · unfold voc; intro a aIn; simp
      constructor
      · use ϕ
        tauto
      · have h : ~ϕ ∈ X2 := by rw [Finset.mem_union] at nIn; tauto
        have := vocElem_subs_vocSet h
        simp at *
        tauto
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · simp at *; tauto
    · have h1 := sat (~ϕ); simp at *; tauto
  · use ~ϕ
    -- ~ϕ ∈ X1 and ϕ ∈ X2
    constructor
    · unfold voc; intro a aIn; simp
      constructor
      · use (~ϕ)
        tauto
      · have h : ϕ ∈ X2 := by rw [Finset.mem_union] at pIn; tauto
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
    · unfold voc; simp; tauto
    constructor
    all_goals by_contra h; rcases h with ⟨W, M, w1, sat⟩
    · specialize sat (~~⊥); simp at *
    · have h1 := sat ϕ; have h2 := sat (~ϕ); simp at *; tauto

theorem notnotInterpolantX1 {X1 X2 ϕ θ} :
    ~~ϕ ∈ X1 → PartInterpolant (X1 \ {~~ϕ} ∪ {ϕ}) (X2 \ {~~ϕ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro notnotphi_in_X1 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreserved X1 (~~ϕ) ϕ notnotphi_in_X1 (by unfold voc; simp)]
    have : voc (X2 \ {~~ϕ}) ⊆ voc X2 := vocErase
    rw [Finset.subset_inter_iff] at vocSub
    rw [Finset.subset_inter_iff]
    tauto
  constructor
  all_goals by_contra hyp; unfold Satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · have : Satisfiable (X1 \ {~~ϕ} ∪ {ϕ} ∪ {~θ}) :=
      by
      unfold Satisfiable
      use W, M, w
      intro ψ psi_in_newX_u_notTheta
      simp at psi_in_newX_u_notTheta
      cases psi_in_newX_u_notTheta
      case inl psi_is_phi =>
        specialize sat (~~ϕ)
        subst psi_is_phi
        simp at sat
        apply sat
        right
        exact notnotphi_in_X1
      case inr c =>
      cases c
      case inl psi_in_newX_u_notTheta =>
        rw [psi_in_newX_u_notTheta]; apply of_not_not
        rw [← psi_in_newX_u_notTheta]
        have := sat (~~ϕ); simp at *; aesop
      · apply sat; simp at *; tauto
    tauto
  · have : Satisfiable (X2 \ {~~ϕ} ∪ {θ}) :=
      by
      unfold Satisfiable at *
      use W, M, w
      intro ψ psi_in_newX2cupTheta
      apply sat; simp at *; tauto
    tauto

theorem notnotInterpolantX2 {X1 X2 ϕ θ} :
    ~~ϕ ∈ X2 → PartInterpolant (X1 \ {~~ϕ}) (X2 \ {~~ϕ} ∪ {ϕ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro notnotphi_in_X2 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreserved X2 (~~ϕ) ϕ notnotphi_in_X2 (by simp)]
    have : voc (X1 \ {~~ϕ}) ⊆ voc X1 := vocErase
    rw [Finset.subset_inter_iff]
    rw [Finset.subset_inter_iff] at vocSub
    tauto
  constructor
  all_goals by_contra hyp; unfold Satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply noSatX1
    unfold Satisfiable
    use W, M, w
    intro ψ psi_in_newX_u_notTheta
    simp at psi_in_newX_u_notTheta
    cases' psi_in_newX_u_notTheta with psi_in_newX_u_notTheta psi_in_newX_u_notTheta
    · apply sat; rw [psi_in_newX_u_notTheta]; simp at *
    cases psi_in_newX_u_notTheta
    · apply sat; simp at *; tauto
  · apply noSatX2
    unfold Satisfiable at *
    use W, M, w
    intro ψ psi_in_newX2cupTheta
    simp at psi_in_newX2cupTheta
    cases psi_in_newX2cupTheta
    case inl psi_is_phi =>
      specialize sat (~~ϕ)
      subst psi_is_phi
      simp at sat
      apply sat
      right
      exact notnotphi_in_X2
    case inr psi_in_newX2cupTheta =>
      apply sat; simp; tauto

theorem conInterpolantX1 {X1 X2 ϕ ψ θ} :
    ϕ⋀ψ ∈ X1 → PartInterpolant (X1 \ {ϕ⋀ψ} ∪ {ϕ, ψ}) (X2 \ {ϕ⋀ψ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro con_in_X1 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreservedTwo (ϕ⋀ψ) ϕ ψ con_in_X1 (by simp)]
    have : voc (X2 \ {ϕ⋀ψ}) ⊆ voc X2 := vocErase
    rw [Finset.subset_inter_iff]
    rw [Finset.subset_inter_iff] at vocSub
    tauto
  constructor
  all_goals by_contra hyp; unfold Satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply noSatX1
    unfold Satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; specialize sat (ϕ⋀ψ) (by simp; exact con_in_X1); unfold Evaluate at sat ; tauto
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; specialize sat (ϕ⋀ψ) (by simp; exact con_in_X1); unfold Evaluate at sat ; tauto
    cases' pi_in with pi_in pi_in
    · subst pi_in
      exact sat (~θ) (by simp)
    · exact sat π (by simp; tauto)
  · apply noSatX2
    unfold Satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; apply sat θ; simp
    · apply sat; simp at *; tauto

theorem conInterpolantX2 {X1 X2 ϕ ψ θ} :
    ϕ⋀ψ ∈ X2 → PartInterpolant (X1 \ {ϕ⋀ψ}) (X2 \ {ϕ⋀ψ} ∪ {ϕ, ψ}) θ → PartInterpolant X1 X2 θ :=
  by
  intro con_in_X2 theta_is_chInt
  rcases theta_is_chInt with ⟨vocSub, noSatX1, noSatX2⟩
  unfold PartInterpolant
  constructor
  · rw [vocPreservedTwo (ϕ⋀ψ) ϕ ψ con_in_X2 (by simp)]
    have : voc (X1 \ {ϕ⋀ψ}) ⊆ voc X1 := vocErase
    rw [Finset.subset_inter_iff]
    rw [Finset.subset_inter_iff] at vocSub
    tauto
  constructor
  all_goals by_contra hyp; unfold Satisfiable at hyp ; rcases hyp with ⟨W, M, w, sat⟩
  · apply noSatX1
    unfold Satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; apply sat (~θ); simp
    · apply sat; simp at *; tauto
  · apply noSatX2
    unfold Satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; specialize sat (ϕ⋀ψ) (by simp; right; exact con_in_X2); unfold Evaluate at sat ; tauto
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; specialize sat (ϕ⋀ψ) (by simp; right; exact con_in_X2); unfold Evaluate at sat ;
      tauto
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; apply sat θ; simp
    · exact sat π (by simp; tauto)

theorem nCoInterpolantX1 {X1 X2 ϕ ψ θa θb} :
    ~(ϕ⋀ψ) ∈ X1 →
      PartInterpolant (X1 \ {~(ϕ⋀ψ)} ∪ {~ϕ}) (X2 \ {~(ϕ⋀ψ)}) θa →
        PartInterpolant (X1 \ {~(ϕ⋀ψ)} ∪ {~ψ}) (X2 \ {~(ϕ⋀ψ)}) θb →
          PartInterpolant X1 X2 (~(~θa⋀~θb)) :=
  by
  intro nCo_in_X1 tA_is_chInt tB_is_chInt
  rcases tA_is_chInt with ⟨a_vocSub, a_noSatX1, a_noSatX2⟩
  rcases tB_is_chInt with ⟨b_vocSub, b_noSatX1, b_noSatX2⟩
  unfold PartInterpolant
  constructor
  · simp
    rw [Finset.subset_inter_iff]
    constructor; all_goals rw [Finset.union_subset_iff] ; constructor <;> intro a aIn
    · have sub : voc (~ϕ) ⊆ voc (~(ϕ⋀ψ)) := by simp; apply Finset.subset_union_left
      have claim := vocPreservedSub (~(ϕ⋀ψ)) (~ϕ) nCo_in_X1 sub
      rw [Finset.subset_iff] at claim
      specialize @claim a
      rw [Finset.subset_iff] at a_vocSub
      specialize a_vocSub aIn
      aesop
    · have sub : voc (~ψ) ⊆ voc (~(ϕ⋀ψ)) := by simp; apply Finset.subset_union_right
      have claim := vocPreservedSub (~(ϕ⋀ψ)) (~ψ) nCo_in_X1 sub
      rw [Finset.subset_iff] at claim
      specialize @claim a
      rw [Finset.subset_iff] at b_vocSub
      specialize b_vocSub aIn
      aesop
    · rw [Finset.subset_iff] at a_vocSub
      specialize a_vocSub aIn
      have : voc (X2 \ {~(ϕ⋀ψ)}) ⊆ voc X2 := vocErase
      unfold voc at *
      simp at *
      tauto
    · rw [Finset.subset_iff] at b_vocSub
      specialize b_vocSub aIn
      have : voc (X2 \ {~(ϕ⋀ψ)}) ⊆ voc X2 := vocErase
      unfold voc at *
      simp at *
      tauto
  constructor
  all_goals by_contra hyp; unfold Satisfiable at hyp; rcases hyp with ⟨W, M, w, sat⟩
  · have : ¬ Evaluate (M, w) ϕ ∨ ¬ Evaluate (M,w) ψ := by
      specialize sat (~(ϕ⋀ψ)) (by simp; assumption)
      simp at sat
      tauto
    cases this
    · apply a_noSatX1
      unfold Satisfiable
      use W, M, w
      intro π pi_in
      simp at pi_in
      cases' pi_in with pi_is_notPhi pi_in
      · subst pi_is_notPhi; simp; assumption
      · cases' pi_in with pi_is_notThetA pi_in_X1
        · subst pi_is_notThetA;
          specialize sat (~~(~θa⋀~θb)) (by simp)
          aesop
        · apply sat π; simp; right; exact pi_in_X1.right
    · apply b_noSatX1
      unfold Satisfiable
      use W, M, w
      intro π pi_in
      simp at pi_in
      cases' pi_in with pi_is_notPhi pi_in
      · subst pi_is_notPhi; simp; assumption
      · cases' pi_in with pi_is_notThetB pi_in_X1
        · subst pi_is_notThetB;
          specialize sat (~~(~θa⋀~θb)) (by simp)
          aesop
        · simp at pi_in_X1
          apply sat π; simp; right; exact pi_in_X1.right
  · have : Evaluate (M, w) θa ∨ Evaluate (M,w) θb := by
      specialize sat (~(~θa⋀~θb)) (by simp)
      simp at sat
      tauto
    cases this
    · apply a_noSatX2
      unfold Satisfiable
      use W, M, w
      intro π pi_in
      simp at pi_in
      cases' pi_in with pi_is_thetA pi_in_X2
      · subst pi_is_thetA; assumption
      · apply sat π; simp; right; exact pi_in_X2.right
    · apply b_noSatX2
      unfold Satisfiable
      use W, M, w
      intro π pi_in
      simp at pi_in
      cases' pi_in with pi_is_thetB pi_in_X2
      · subst pi_is_thetB; assumption
      · apply sat π; simp; right; exact pi_in_X2.right

theorem nCoInterpolantX2 {X1 X2 ϕ ψ θa θb} :
    ~(ϕ⋀ψ) ∈ X2 →
      PartInterpolant (X1 \ {~(ϕ⋀ψ)}) (X2 \ {~(ϕ⋀ψ)} ∪ {~ϕ}) θa →
        PartInterpolant (X1 \ {~(ϕ⋀ψ)}) (X2 \ {~(ϕ⋀ψ)} ∪ {~ψ}) θb → PartInterpolant X1 X2 (θa⋀θb) :=
  by
  intro nCo_in_X2 tA_is_chInt tB_is_chInt
  rcases tA_is_chInt with ⟨a_vocSub, a_noSatX1, a_noSatX2⟩
  rcases tB_is_chInt with ⟨b_vocSub, b_noSatX1, b_noSatX2⟩
  unfold PartInterpolant
  constructor
  · simp
    rw [Finset.subset_inter_iff]
    constructor; all_goals rw [Finset.union_subset_iff] ; constructor <;> intro a aIn
    · rw [Finset.subset_iff] at a_vocSub
      specialize a_vocSub aIn
      have claim : voc (X1 \ {~(ϕ⋀ψ)}) ⊆ voc X1 := vocErase
      unfold voc at claim
      simp at *
      tauto
    · rw [Finset.subset_iff] at b_vocSub
      specialize b_vocSub aIn
      have claim : voc (X1 \ {~(ϕ⋀ψ)}) ⊆ voc X1 := vocErase
      unfold voc at claim
      simp at *
      tauto
    · have sub : voc (~ϕ) ⊆ voc (~(ϕ⋀ψ)) := by simp; apply Finset.subset_union_left
      have claim := vocPreservedSub (~(ϕ⋀ψ)) (~ϕ) nCo_in_X2 sub
      rw [Finset.subset_iff] at claim
      rw [Finset.subset_iff] at a_vocSub
      specialize a_vocSub aIn
      aesop
    · have sub : voc (~ψ) ⊆ voc (~(ϕ⋀ψ)) := by simp; apply Finset.subset_union_right
      have claim := vocPreservedSub (~(ϕ⋀ψ)) (~ψ) nCo_in_X2 sub
      rw [Finset.subset_iff] at claim
      rw [Finset.subset_iff] at b_vocSub
      specialize b_vocSub aIn
      aesop
  constructor
  all_goals by_contra hyp; unfold Satisfiable at hyp; rcases hyp with ⟨W, M, w, sat⟩
  · apply a_noSatX1
    unfold Satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in
    cases' pi_in with pi_in pi_in
    · rw [pi_in]
      by_contra; apply b_noSatX1
      unfold Satisfiable
      use W, M, w
      intro χ chi_in
      simp at chi_in
      cases chi_in
      case inl chi_is_not_thetab =>
        subst chi_is_not_thetab; specialize sat (~(θa⋀θb)); simp at *; tauto
      · apply sat; simp; tauto
    · apply sat; simp; tauto
  · apply a_noSatX2
    unfold Satisfiable
    use W, M, w
    intro π pi_in
    simp at pi_in
    cases' pi_in with pi_in pi_in
    · subst pi_in
      by_contra; apply b_noSatX2
      unfold Satisfiable
      use W, M, w
      intro χ chi_in
      simp at chi_in
      cases' chi_in with chi_in chi_in
      case inl notnot_phi => simp at notnot_phi; specialize sat (~(ϕ⋀ψ)); aesop
      cases' chi_in with chi_in chi_in
      · specialize sat (θa⋀θb); simp at sat ; rw [chi_in]; exact sat.right
      · apply sat; simp; tauto
    cases' pi_in with pi_in pi_in
    · rw [pi_in]; specialize sat (θa⋀θb); simp at sat ; unfold Evaluate at *; tauto
    · apply sat; simp; tauto

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
  induction N using Nat.strong_induction_on
  case h n IH =>
   intro X lenX_is_n X1 X2 defX pt
   rcases pt with ⟨pt, nextInter⟩
   cases pt
   case sim foo =>
     apply nextInter
     subst defX
     simp
   case byLocalRule B next lr =>
    cases lr
    -- The bot and not cases use Lemma 14
    case bot bot_in_X => rw [defX] at bot_in_X ; exact botInter bot_in_X
    case Not ϕ in_both => rw [defX] at in_both ; exact notInter in_both
    case neg ϕ
      notnotphi_in =>
      have notnotphi_in_union : ~~ϕ ∈ X1 ∪ X2 := by rw [defX] at notnotphi_in ; assumption
      simp at *
      cases' notnotphi_in_union with notnotphi_in_X1 notnotphi_in_X2
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
          by intro Y1 Y2; apply nextInter Y1 Y2 (newX1 ∪ newX2); aesop
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _) (next (newX1 ∪ newX2) yclaim) nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact notnotInterpolantX1 notnotphi_in_X1 theta_is_chInt
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
          by intro Y1 Y2; apply nextInter Y1 Y2 (newX1 ∪ newX2); aesop
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _) (next (newX1 ∪ newX2) yclaim) nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact notnotInterpolantX2 notnotphi_in_X2 theta_is_chInt
    case Con ϕ ψ
      con_in_X =>
      have con_in_union : ϕ⋀ψ ∈ X1 ∨ ϕ⋀ψ ∈ X2 := by subst defX; simp at con_in_X; assumption
      cases con_in_union
      case inl con_in_X1 => -- case ϕ⋀ψ ∈ X1
        subst defX
        let newX1 := X1 \ {ϕ⋀ψ} ∪ {ϕ, ψ}
        let newX2 := X2 \ {ϕ⋀ψ}
        have yclaim : newX1 ∪ newX2 ∈ {(X1 ∪ X2) \ {ϕ⋀ψ} ∪ {ϕ, ψ}} :=
          by
          rw [Finset.mem_singleton]
          change X1 \ {ϕ⋀ψ} ∪ {ϕ, ψ} ∪ X2 \ {ϕ⋀ψ} = (X1 ∪ X2) \ {ϕ⋀ψ} ∪ {ϕ, ψ}
          ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set m := lengthOfSet (newX1 ∪ newX2)
        have m_lt_n : m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.Con con_in_X) (newX1 ∪ newX2) yclaim
        have nextNextInter :
          ∀ Y1 Y2 : Finset Formula,
            Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, next (newX1 ∪ newX2) yclaim⟩ →
              Exists (PartInterpolant Y1 Y2) :=
          by
          intro Y1 Y2 Y_in; apply nextInter; unfold endNodesOf
          simp only [true_and, endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left, Subtype.exists]
          exact ⟨newX1 ∪ newX2, yclaim, Y_in⟩
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          by
          apply IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _)
          fconstructor
          apply next (newX1 ∪ newX2) yclaim; exact nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact conInterpolantX1 con_in_X1 theta_is_chInt
      case inr con_in_X2 => -- case ϕ⋀ψ ∈ X2
        subst defX
        let newX1 := X1 \ {ϕ⋀ψ}
        let newX2 := X2 \ {ϕ⋀ψ} ∪ {ϕ, ψ}
        have yclaim : newX1 ∪ newX2 ∈ {(X1 ∪ X2) \ {ϕ⋀ψ} ∪ {ϕ, ψ}} :=
          by
          rw [Finset.mem_singleton]
          change X1 \ {ϕ⋀ψ} ∪ (X2 \ {ϕ⋀ψ} ∪ {ϕ, ψ}) = (X1 ∪ X2) \ {ϕ⋀ψ} ∪ {ϕ, ψ}
          ext1 a; constructor <;> · intro hyp; simp at hyp ; simp; tauto
        set m := lengthOfSet (newX1 ∪ newX2)
        have m_lt_n : m < n := by
          rw [lenX_is_n]
          exact localRulesDecreaseLength (LocalRule.Con con_in_X) (newX1 ∪ newX2) yclaim
        have nextNextInter :
          ∀ Y1 Y2 : Finset Formula,
            Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, next (newX1 ∪ newX2) yclaim⟩ →
              Exists (PartInterpolant Y1 Y2) :=
          by
          intro Y1 Y2 Y_in; apply nextInter; unfold endNodesOf
          simp only [true_and, endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left, Subtype.exists]
          exact ⟨newX1 ∪ newX2, yclaim, Y_in⟩
        have childInt : Exists (PartInterpolant newX1 newX2) :=
          by
          apply IH m m_lt_n (newX1 ∪ newX2) (refl _) (refl _)
          fconstructor
          apply next (newX1 ∪ newX2) yclaim; exact nextNextInter
        cases' childInt with θ theta_is_chInt
        use θ
        exact conInterpolantX2 con_in_X2 theta_is_chInt
    case nCo ϕ ψ
      nCo_in_X =>
      have nCo_in_union : ~(ϕ⋀ψ) ∈ X1 ∨ ~(ϕ⋀ψ) ∈ X2 := by subst defX; simp at nCo_in_X; assumption
      cases nCo_in_union
      case inl nCo_in_X1 => -- case ~(ϕ⋀ψ) ∈ X1
        subst defX
        -- splitting rule!
        -- first get an interpolant for the ~ϕ branch:
        let a_newX1 := X1 \ {~(ϕ⋀ψ)} ∪ {~ϕ}
        let a_newX2 := X2 \ {~(ϕ⋀ψ)}
        have a_yclaim :
          a_newX1 ∪ a_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ψ}} :
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
          simp only [true_and, endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨a_newX1 ∪ a_newX2, a_yclaim, Y_in⟩
        cases' a_childInt with θa a_theta_is_chInt
        -- now get an interpolant for the ~ψ branch:
        let b_newX1 := X1 \ {~(ϕ⋀ψ)} ∪ {~ψ}
        let b_newX2 := X2 \ {~(ϕ⋀ψ)}
        have b_yclaim :
          b_newX1 ∪ b_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ψ}} :
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
          simp only [true_and, endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
            Subtype.exists]
          exact ⟨b_newX1 ∪ b_newX2, b_yclaim, Y_in⟩
        cases' b_childInt with θb b_theta_is_chInt
        -- finally, combine the two interpolants using disjunction:
        use~(~θa⋀~θb)
        exact nCoInterpolantX1 nCo_in_X1 a_theta_is_chInt b_theta_is_chInt
      case inr nCo_in_X2 => -- case ~(ϕ⋀ψ) ∈ X2
        subst defX
        -- splitting rule!
        -- first get an interpolant for the ~ϕ branch:
        let a_newX1 := X1 \ {~(ϕ⋀ψ)}
        let a_newX2 := X2 \ {~(ϕ⋀ψ)} ∪ {~ϕ}
        have a_yclaim :
          a_newX1 ∪ a_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ψ}} :
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
          simp only [true_and, endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left, Subtype.exists]
          exact ⟨a_newX1 ∪ a_newX2, a_yclaim, Y_in⟩
        cases' a_childInt with θa a_theta_is_chInt
        -- now get an interpolant for the ~ψ branch:
        let b_newX1 := X1 \ {~(ϕ⋀ψ)}
        let b_newX2 := X2 \ {~(ϕ⋀ψ)} ∪ {~ψ}
        have b_yclaim :
          b_newX1 ∪ b_newX2 ∈
            ({(X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ϕ}, (X1 ∪ X2) \ {~(ϕ⋀ψ)} ∪ {~ψ}} :
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
          simp only [true_and, endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left, Subtype.exists]
          exact ⟨b_newX1 ∪ b_newX2, b_yclaim, Y_in⟩
        cases' b_childInt with θb b_theta_is_chInt
        -- finally, combine the two interpolants using conjunction:
        use θa⋀θb
        exact nCoInterpolantX2 nCo_in_X2 a_theta_is_chInt b_theta_is_chInt

theorem vocProj (X) : voc (projection X) ⊆ voc X :=
  by
  simp
  intro ϕ phi_in_proj
  rw [proj] at phi_in_proj
  intro a aInVocPhi
  simp
  tauto

theorem projUnion {X Y} : projection (X ∪ Y) = projection X ∪ projection Y :=
  by
  ext1
  rw [proj]
  simp
  rw [proj]
  rw [proj]

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
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ} := by rw [projUnion]; ext1; simp
      rw [← yclaim] at ctProjNotPhi
      have nextInt : ∃ θ, PartInterpolant newX1 newX2 θ := IH newX1 newX2 (by rw [yclaim]; simp)
      rcases nextInt with ⟨θ, vocSub, unsat1, unsat2⟩
      use~(□~θ)
      repeat' constructor
      -- it remains to show the three properties of the interpolant
      · change voc θ ⊆ voc X1 ∩ voc X2
        have inc1 : voc newX1 ⊆ voc X1 := by
          intro a aIn; simp at *
          cases' aIn with a_in_vocPhi other
          · use~(□ϕ); tauto
          · rcases other with ⟨ψ, psi_in_projX1, _⟩
            use□ψ; change □ψ ∈ X1 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        have inc2 : voc newX2 ⊆ voc X2 := by
          intro a aIn; simp at *
          rcases aIn with ⟨ψ, psi_in_projX2⟩
          · use□ψ; change □ψ ∈ X2 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        rw [Finset.subset_inter_iff] at vocSub
        rcases vocSub with ⟨vocTh_in_X1, vocTh_in_X2⟩
        rw [Finset.subset_inter_iff]
        tauto
      all_goals unfold Satisfiable at *
      case left notBoxPhi_in_X =>
        by_contra hyp
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
        case inl psi_in_newX1 =>
          subst psi_in_newX1; specialize sat (~~(□~θ)); simp at *;
          exact v_not_phi
        case inr psi_in_newX1 =>
          cases' psi_in_newX1 with psi_in_newX1 psi_in
          · rw [psi_in_newX1]
            specialize sat (~(~(□(~θ))))
            simp at sat
            simp
            exact sat v rel_w_v
          · rw [proj] at psi_in
            specialize sat (□ψ) (by simp; exact psi_in)
            simp at sat
            exact sat v rel_w_v
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
        cases' psi_in_newX2 with psi_is_theta psi_in_projX2
        · subst psi_is_theta; assumption
        · rw [proj] at psi_in_projX2 ; specialize sat (□ψ); apply sat; simp; assumption; assumption
    · -- case ~□ϕ ∈ X2
      let newX1 := projection X1
      let newX2 := projection X2 ∪ {~ϕ}
      ---- what follows is *based* on copying the previous case ----
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ} := by rw [projUnion]; ext1; simp
      rw [← yclaim] at ctProjNotPhi
      have nextInt : ∃ θ, PartInterpolant newX1 newX2 θ := IH newX1 newX2 (by rw [yclaim]; simp)
      rcases nextInt with ⟨θ, vocSub, unsat1, unsat2⟩
      use□θ
      -- !!
      repeat' constructor
      -- it remains to show the three properties of the interpolant
      · change voc θ ⊆ voc X1 ∩ voc X2
        have inc1 : voc newX2 ⊆ voc X2 := by
          intro a aIn; simp at *
          cases' aIn with a_in_vocPhi other
          · use~(□ϕ); tauto
          · rcases other with ⟨ψ, psi_in_projX2, _⟩
            use□ψ; change □ψ ∈ X2 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        have inc2 : voc newX1 ⊆ voc X1 := by
          intro a aIn; simp at *
          rcases aIn with ⟨ψ, psi_in_projX1⟩
          · use□ψ; change □ψ ∈ X1 ∧ a ∈ voc (□ψ); rw [← proj]; tauto
        rw [Finset.subset_inter_iff] at vocSub
        rcases vocSub with ⟨vocTh_in_X1, vocTh_in_X2⟩
        rw [Finset.subset_inter_iff]
        tauto
      all_goals unfold Satisfiable at *
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
        cases' psi_in_newX1 with psi_in_newX1 psi_in_newX1
        · subst psi_in_newX1; specialize sat (~(□θ)); simp at sat; tauto
        · rw [proj] at psi_in_newX1 ; specialize sat (□ψ); apply sat; simp; assumption; assumption
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
        cases' psi_in_newX2 with psi_is_notPhi psi_in_newX2
        · subst psi_is_notPhi; simp; assumption
        cases' psi_in_newX2
        case inl psi_is_theta =>
          subst psi_is_theta
          specialize sat (□ψ) (by simp)
          simp at sat
          exact sat v rel_w_v
        case inr psi_in_newX2 =>
          rw [proj] at psi_in_newX2 ; specialize sat (□ψ); simp at sat
          apply sat; right; assumption; assumption

theorem tabToInt {X1 X2} : ClosedTableau (X1 ∪ X2) → ∃ θ, PartInterpolant X1 X2 θ
  | ctX => almostTabToInt ctX X1 X2 (refl _)
