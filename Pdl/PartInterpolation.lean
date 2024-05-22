import Mathlib.Data.Finset.Basic

import Pdl.Vocab
import Pdl.Completeness

open HasVocabulary HasSat


def canonProg : sorry := sorry

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

@[simp]
def jvoc : (LR: TNode) → Finset Nat := λ X => voc (X.left) ∩ voc (X.right)

def isPartInterpolant (X : TNode) (θ : Formula) :=
  voc θ ⊆ jvoc X ∧ (¬Satisfiable ((~θ) :: X.left) ∧ ¬Satisfiable (θ :: X.right))

def PartInterpolant (N : TNode) := Subtype <| isPartInterpolant N

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

theorem tabToInt {X : TNode} (tab : ClosedTableau LoadHistory.nil X) :
    PartInterpolant X := by
  sorry
