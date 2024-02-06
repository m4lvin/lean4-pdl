import Mathlib.Data.Finset.Basic

import Pdl.Vocab
import Pdl.Semantics
import Pdl.LocalTableau

open HasVocabulary HasSat


def IsPartInterpolant (N : TNode) (θ : Formula) :=
  voc θ ⊆ voc N ∧ (¬Satisfiable (N.L ∪ {~θ}) ∧ ¬Satisfiable (N.R ∪ {θ}))

def PartInterpolant (N : TNode) := Subtype <| IsPartInterpolant N

theorem localInterpolantStep
  (C : List TNode)
  (L R : List Formula)
  (O : Option (Sum NegLoadFormula NegLoadFormula))
  (ruleA : LocalRuleApp N C)
  (subθs : Πc ∈ C, PartInterpolant c)
  : PartInterpolant N := by

  -- UNPACKING TERMS
  match def_ruleA : ruleA with
  | @LocalRuleApp.mk _ _ _ _ _ Lcond Rcond Ocond rule hC preProof =>

  -- DISTINCTION ON LOCALRULE USED
  cases def_rule : rule with


  | oneSidedL orule =>
    let interList := C.attach.map $ λ⟨c, cinC⟩ => (subθs c cinC).val
    sorry

  | oneSidedR orule => sorry
  | LRnegL φ => sorry
  | LRnegR φ => sorry
  | loadedL χ lrule => sorry
  | loadedR χ lrule => sorry


theorem partInterpolation :
    ∀ (L R : List Formula), ¬Satisfiable (L ∪ R) → PartInterpolant (L,R,none) := by
  sorry
