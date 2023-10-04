import Oneshot.Syntax
import Oneshot.Semantics

#align_import discon

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Con /-
-- N-ary conjunction and disjunction
-- N-ary conjunction and disjunction
@[simp]
def Con : List Formula → Formula
  | [] => ⊤
  | [f] => f
  | f :: rest => f⋀Con rest
#align con Con
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem conempty : Con ∅ = ⊤ := by rfl
#align conempty conempty

@[simp]
theorem consingle {f : Formula} : Con [f] = f := by rfl
#align consingle consingle

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
def dis : List Formula → Formula
  | [] => ⊥
  | [f] => f
  | f :: rest => f⋁dis rest
#align dis dis

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem disempty : dis ∅ = ⊥ := by rfl
#align disempty disempty

@[simp]
theorem dissingle {f : Formula} : dis [f] = f := by rfl
#align dissingle dissingle

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
def discon : List (List Formula) → Formula
  | [] => ⊥
  | [X] => Con X
  | X :: rest => Con X⋁discon rest
#align discon discon

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem disconempty : discon {∅} = ⊤ := by rfl
#align disconempty disconempty

@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl
#align disconsingle disconsingle

theorem conEvalHT {X f W M} {w : W} :
    Evaluate M w (Con (f :: X)) ↔ Evaluate M w f ∧ Evaluate M w (Con X) :=
  by
  induction' X with g X IH
  · simp; unfold Evaluate; tauto
  · simp; unfold Evaluate
#align conEvalHT conEvalHT

theorem conEval {W M X} {w : W} : Evaluate M w (Con X) ↔ ∀ f ∈ X, Evaluate M w f :=
  by
  induction' X with f X IH
  · simp at *; unfold Evaluate; tauto
  · simp at *; rw [conEvalHT]; tauto
#align conEval conEval

theorem disconEvalHT {X} : ∀ XS, discon (X :: XS)≡Con X⋁discon XS :=
  by
  unfold SemEquiv
  intro XS W M w
  cases' XS with Y YS
  · simp; unfold Evaluate; simp
  · simp
#align disconEvalHT disconEvalHT

theorem disconEval {W M} {w : W} :
    ∀ {N : Nat} (XS),
      List.length XS = N → (Evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, Evaluate M w f) :=
  by
  intro N
  apply Nat.strong_induction_on N
  intro n IH
  intro XS nDef
  subst nDef
  cases' XS with X XS
  · simp; unfold Evaluate; simp
  specialize IH XS.length (by simp) XS (by rfl)
  rw [disconEvalHT]
  rw [evalDis]
  rw [IH]
  constructor
  · -- →
    intro lhs
    cases lhs
    · use X; simp; rw [conEval] at lhs ; tauto
    · cases' lhs with Y claim; use Y; simp; tauto
  · -- ←
    intro rhs
    cases' rhs with Y rhs
    cases' rhs with Y_in Ysat
    simp at Y_in 
    cases Y_in
    · left; subst Y_in; rw [conEval]; tauto
    · right; use Y; tauto
#align disconEval disconEval

