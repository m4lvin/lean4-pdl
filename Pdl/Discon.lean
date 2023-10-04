import Mathlib.Init.Data.Nat.Lemmas

import Pdl.Syntax
import Pdl.Semantics

@[simp]
def Con : List Formula → Formula
  | [] => ⊤
  | [f] => f
  | f :: rest => f⋀Con rest

@[simp]
theorem conempty : Con ∅ = (⊤ : Formula) := by rfl
#align conempty conempty

@[simp]
theorem consingle {f : Formula} : Con [f] = f := by rfl
#align consingle consingle

@[simp]
def dis : List Formula → Formula
  | [] => ⊥
  | [f] => f
  | f :: rest => f⋁dis rest
#align dis dis

@[simp]
theorem disempty : dis ∅ = (⊥ : Formula) := by rfl
#align disempty disempty

@[simp]
theorem dissingle {f : Formula} : dis [f] = f := by rfl
#align dissingle dissingle

@[simp]
def discon : List (List Formula) → Formula
  | [] => ⊥
  | [X] => Con X
  | X :: rest => Con X⋁discon rest
#align discon discon

@[simp]
theorem disconempty : discon {∅} = (⊤ : Formula) := by rfl
#align disconempty disconempty

@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl
#align disconsingle disconsingle

theorem conEvalHT {X f W M} {w : W} :
    evaluate M w (Con (f :: X)) ↔ evaluate M w f ∧ evaluate M w (Con X) :=
  by
  induction' X with g X _
  · simp
  · simp

theorem conEval {W M X} {w : W} : evaluate M w (Con X) ↔ ∀ f ∈ X, evaluate M w f :=
  by
  induction' X with f X IH
  · simp
  · rw [conEvalHT]
    simp
    intro _
    assumption

theorem disconEvalHT {X} : ∀ XS, discon (X :: XS)≡Con X⋁discon XS :=
  by
  unfold semEquiv
  intro XS W M w
  cases' XS with Y YS
  · simp
  · simp

theorem disconEval {W M} {w : W} :
    ∀ {N : Nat} XS,
      List.length XS = N → (evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f) :=
  by
  intro N
  refine Nat.strong_induction_on N ?_ -- should be induction N using Nat.strong_induction_on or something similar?
  intro n IH
  intro XS nDef
  subst nDef
  cases' XS with X XS
  · simp
  specialize IH XS.length (by simp) XS (by rfl)
  rw [disconEvalHT]
  rw [evalDis]
  rw [IH]
  constructor
  · -- →
    intro lhs
    cases' lhs with lhs lhs
    · use X
      simp
      rw [conEval] at lhs
      tauto
    · cases' lhs with Y claim
      use Y
      simp
      tauto
  · -- ←
    intro rhs
    cases' rhs with Y rhs
    cases' rhs with Y_in Ysat
    simp at Y_in 
    cases' Y_in with Y_in
    · left
      subst Y_in
      rw [conEval]; tauto
    · right
      use Y
