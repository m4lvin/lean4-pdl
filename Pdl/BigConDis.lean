import Mathlib.Init.Data.Nat.Lemmas

import Pdl.Syntax
import Pdl.Semantics
import Pdl.Vocab
import Pdl.Semantics

@[simp]
def bigCon : List Formula → Formula
  | [] => ⊤
  | [f] => f
  | f :: rest => f⋀bigCon rest

open HasVocabulary


theorem vocOfBigCon {l : List Formula} : x ∈ voc (bigCon l) → ∃φ ∈ l, x ∈ voc φ :=
  by sorry

@[simp]
theorem conempty : bigCon ∅ = (⊤ : Formula) := by rfl

@[simp]
theorem consingle {f : Formula} : bigCon [f] = f := by rfl

@[simp]
def bigDis : List Formula → Formula
  | [] => ⊥
  | [f] => f
  | f :: rest => f ⋁ bigDis rest

@[simp]
theorem disempty : bigDis [] = (⊥ : Formula) := by rfl

@[simp]
theorem dissingle {f : Formula} : bigDis [f] = f := by rfl

@[simp]
def discon : List (List Formula) → Formula
  | [] => ⊥
  | [X] => bigCon X
  | X :: rest => bigCon X⋁discon rest

@[simp]
theorem disconempty : discon {∅} = (⊤ : Formula) := by rfl

theorem vocOfBigDis {l : List Formula} : x ∈ voc (bigDis l) ↔ ∃φ ∈ l, x ∈ voc φ := by
  constructor
  · intro hyp
    induction l
    case nil  => exfalso; exact (List.mem_nil_iff x).mp hyp
    case cons head tail ih =>
      cases em (x ∈ vocabOfFormula head)
      next h => use head; simp; exact h
      next h =>
        unfold bigDis at hyp
        have in_tail : x ∈ voc (bigDis tail) := by sorry
        aesop
  · sorry


@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl

theorem conEvalHT {X f W M} {w : W} :
    Evaluates M w (bigCon (f :: X)) ↔ Evaluates M w f ∧ Evaluates M w (bigCon X) :=
  by
  induction' X with g X _
  · simp
  · simp

theorem conEval {W M X} {w : W} : Evaluates M w (bigCon X) ↔ ∀ f ∈ X, Evaluates M w f :=
  by
  induction' X with f X IH
  · simp
  · rw [conEvalHT]
    simp
    intro _
    assumption

theorem disconEvalHT {X} : ∀ XS, discon (X :: XS)≡bigCon X⋁discon XS :=
  by
  unfold semEquiv
  intro XS W M w
  cases' XS with Y YS
  · simp
  · simp

theorem disconEval' {W M} {w : W} :
    ∀ {N : Nat} XS,
      List.length XS = N → (Evaluates M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, Evaluates M w f) :=
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

theorem disconEval {W M} {w : W} :
    ∀ XS,
      (Evaluates M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, Evaluates M w f) :=
  by
    intro XS
    apply disconEval' XS rfl

-- UPLUS

@[simp]
def pairunionList : List (List Formula) → List (List Formula) → List (List Formula)
  | xls, yls => List.join (xls.map fun xl => yls.map fun yl => xl ++ yl)

@[simp]
def pairunionFinset : Finset (Finset Formula) → Finset (Finset Formula) → Finset (Finset Formula)
  | X, Y => X.biUnion fun ga => Y.biUnion fun gb => {ga ∪ gb}

class HasUplus (α : Type → Type) where
  pairunion : α (α Formula) → α (α Formula) → α (α Formula)

infixl:77 "⊎" => HasUplus.pairunion

@[simp]
instance listHasUplus : HasUplus List := ⟨pairunionList⟩
@[simp]
instance finsetHasUplus : HasUplus Finset := ⟨pairunionFinset⟩

theorem disconAnd {XS YS} : discon (XS ⊎ YS) ≡ discon XS ⋀ discon YS :=
  by
  unfold semEquiv
  intro W M w
  rw [disconEval (XS ⊎ YS)]
  simp
  rw [disconEval XS]
  rw [disconEval YS]
  aesop

theorem disconOr {XS YS} : discon (XS ∪ YS) ≡ discon XS ⋁ discon YS :=
  by
  unfold semEquiv
  intro W M w
  rw [disconEval (XS ∪ YS)]
  simp
  rw [disconEval XS]
  rw [disconEval YS]
  constructor
  · -- →
    intro lhs
    rcases lhs with ⟨Z, Z_in, w_sat_Z⟩
    intro notL
    simp at notL
    cases Z_in
    case inl Z_in_XS =>
      specialize notL Z Z_in_XS
      rcases notL with ⟨f, f_in_Z, w_not_f⟩
      specialize w_sat_Z f f_in_Z
      absurd w_sat_Z
      exact w_not_f
    use Z
  · -- ←
    intro rhs
    cases (Classical.em (∃ Y, Y ∈ XS ∧ ∀ (f : Formula), f ∈ Y → Evaluates M w f))
    case inl hyp =>
      rcases hyp with ⟨X, X_in, satX⟩
      use X
      exact ⟨Or.inl X_in, satX⟩
    case inr nothyp =>
      specialize rhs nothyp
      rcases rhs with ⟨Y, Y_in, satY⟩
      use Y
      exact ⟨Or.inr Y_in, satY⟩

theorem union_elem_uplus {XS YS : Finset (Finset Formula)} {X Y : Finset Formula} :
  X ∈ XS → Y ∈ YS → ((X ∪ Y) ∈ (XS ⊎ YS)) :=
  by
  intro X_in Y_in
  simp
  exact ⟨X, X_in, Y, Y_in, rfl⟩


open HasSat

-- Probably redundant but leaving these here for now
lemma eval_neg_BigDis_iff_eval_bigConNeg {l : List Formula} {M : KripkeModel W} {w : W} :
    Evaluates M w (~(bigDis l)) ↔ Evaluates M w (~~bigCon (l.map (~·))) := by sorry

lemma eval_negBigCon_iff_eval_bigDisNeg {l : List Formula} {M : KripkeModel W} {w : W} :
    Evaluates M w (~(bigCon l)) ↔ Evaluates M w (bigDis (l.map (~·))) := by sorry

lemma sat_negBigDis_iff_sat_bigConNeg {l : List Formula} :
    Satisfiable (~(bigDis l)) ↔ Satisfiable (~~bigCon (l.map (~·))) := by sorry

lemma sat_negBigCon_iff_sat_bigDisNeg {l : List Formula}:
    Satisfiable (~(bigCon l)) ↔ Satisfiable (bigDis (l.map (~·))) := by sorry
