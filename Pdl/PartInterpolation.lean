import Mathlib.Data.Finset.Basic

import Pdl.Completeness
import Pdl.Distance

open HasVocabulary HasSat

@[simp]
def TNode.left : TNode → List Formula
| ⟨L, _, none⟩ => L
| ⟨L, _, some (Sum.inl ⟨f⟩)⟩ => unload f :: L
| ⟨L, _, some (Sum.inr _  )⟩ => L

@[simp]
def TNode.right : TNode → List Formula
| ⟨_, R, none⟩ => R
| ⟨_, R, some (Sum.inl _  )⟩ => R
| ⟨_, R, some (Sum.inr ⟨f⟩)⟩ => unload f :: R

/-- Joint vocabulary of all parts of a TNode. -/
@[simp]
def jvoc (X : TNode) : Vocab := voc (X.left) ∩ voc (X.right)

def isPartInterpolant (X : TNode) (θ : Formula) :=
  voc θ ⊆ jvoc X ∧ (¬ satisfiable ((~θ) :: X.left) ∧ ¬ satisfiable (θ :: X.right))

def PartInterpolant (N : TNode) := Subtype <| isPartInterpolant N

theorem localRuleApp_does_not_increase_jvoc (ruleA : LocalRuleApp X C) :
    ∀ Y ∈ C, jvoc Y ⊆ jvoc X := by
  sorry -- see Bml

/-- Maehara's method for local rule applications. -/
def localInterpolantStep (L R : List Formula) (o) (ruleA : LocalRuleApp (L,R,o) C)
    (subθs : Π c ∈ C, PartInterpolant c)
    : PartInterpolant (L,R,o) := by
  -- UNPACKING TERMS
  rcases def_ruleA : ruleA with @⟨L, R, C, ress, O, Lcond, Rcond, Ocond, rule, hc, precondProof⟩
  -- DISTINCTION ON LOCALRULE USED
  cases def_rule : rule
  case oneSidedL orule =>
    let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
    use dis interList
    constructor
    · intro n n_in_inter
      rw [in_voc_dis] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp [interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · constructor
      · intro L_and_nθ_sat
        sorry -- See Bml?
      . intro R_and_θ_sat
        sorry -- See Bml?
  case oneSidedR orule =>
    let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
    use Con interList
    constructor
    · intro n n_in_inter
      rw [in_voc_con] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp [interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · constructor
      · intro L_and_nθ_sat
        sorry -- See Bml?
      . intro R_and_θ_sat
        sorry -- See Bml?
  case LRnegL φ =>
    use φ
    constructor
    · intro n n_in_φ
      unfold jvoc
      simp
      constructor
      · rcases o with _ | (_|_)
        all_goals
          simp [voc, Vocab.fromList, Vocab.fromListFormula_map_iff] at *
          simp at precondProof
          tauto
      · rcases o with _ | (_|_)
        all_goals
          simp [voc, Vocab.fromList, Vocab.fromListFormula_map_iff] at *
          simp at precondProof
          try right
          use ~φ
          simp [vocabOfFormula]
          tauto
    · sorry -- see Bml?
  case LRnegR φ =>
    use ~φ -- not sure about this one
    constructor
    · intro n n_in_φ
      unfold jvoc
      simp
      constructor
      · rcases o with _ | (_|_)
        all_goals
          simp [voc, Vocab.fromList, Vocab.fromListFormula_map_iff] at *
          simp at precondProof
          tauto
      · rcases o with _ | (_|_)
        all_goals
        · simp [voc, Vocab.fromList, Vocab.fromListFormula_map_iff] at *
          simp at precondProof
          try right
          use φ
          constructor
          · exact precondProof.2
          · simp only [vocabOfFormula] at n_in_φ; exact n_in_φ
    · sorry -- see Bml?
  case loadedL =>
    -- keep interpolant the same
    sorry
  case loadedR =>
    -- keep interpolant the same
    sorry

def partInterpolation :
    ∀ (L R : List Formula), ¬ satisfiable (L ∪ R) → PartInterpolant (L,R,none) := by
  sorry

def tabToInt {X : TNode} (tab : Tableau .nil X) :
    PartInterpolant X := by
  sorry
