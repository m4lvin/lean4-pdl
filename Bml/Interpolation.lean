-- INTERPOLATION

import Bml.CompletenessViaPaths
import Bml.Partitions

open HasVocabulary

def Interpolant (φ : Formula) (ψ : Formula) (θ : Formula) :=
  Tautology (φ↣θ) ∧ Tautology (θ↣ψ) ∧ voc θ ⊆ voc φ ∩ voc ψ

theorem tautImp_iff_TNOdenotUnsat {φ ψ} {X : TNode} :
    X = ({φ}, {~ψ}) →
    (Tautology (φ↣ψ) ↔ ¬HasSat.Satisfiable X) :=
  by
  intro defX
  subst defX
  simp only [Tautology, Evaluate, not_and, not_not, HasSat.Satisfiable, union_singleton_is_insert,
    Finset.mem_singleton, Finset.mem_insert, forall_eq_or_imp, forall_eq, not_exists] at *
  constructor
  · intro taut
    intro W M w w_nPsi w_phi
    specialize taut W M w
    tauto
  · intro unsat
    intro W M w
    specialize unsat W M w
    simp only [impl, Evaluate, not_and, not_not]
    tauto

theorem interpolation {ϕ ψ} : Tautology (ϕ↣ψ) → ∃ θ, Interpolant ϕ ψ θ :=
  by
  intro hyp
  let X : TNode := ({ϕ}, {~ψ})
  have ctX : ClosedTableau X :=
    by
    rw [tautImp_iff_TNOdenotUnsat rfl] at hyp
    rw [← completeness] at hyp
    -- using completeness!
    unfold Consistent at hyp
    simp at hyp
    unfold Inconsistent at hyp
    change ClosedTableau ({ϕ}, {~ψ})
    exact Classical.choice hyp
  have partInt := tabToInt ctX
  -- using tableau interpolation!
  rcases partInt with ⟨θ, pI_prop⟩
  unfold isPartInterpolant at pI_prop
  refine ⟨θ, ?_, ?_, ?_⟩
  · rw [tautImp_iff_comboNotUnsat]; tauto
  · rw [tautImp_iff_comboNotUnsat]
    simp_all [Evaluate, X]
  · intro c c_in
    have := pI_prop.1 c_in
    simp_all [X, jvoc]
