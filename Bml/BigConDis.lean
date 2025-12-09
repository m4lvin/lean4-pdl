-- All copied from pdl/Discon.lean
-- not all parts might make sense yet

import Bml.Vocabulary
import Bml.Semantics

open HasSat

@[simp]
def bigCon : List Formula → Formula
  | []        => ⊤
  | [f]       => f
  | f :: rest => f ⋀ bigCon rest

@[simp]
def bigDis : List Formula → Formula
  | []        => ⊥
  | [f]       => f
  | f :: rest => f ⋁ bigDis rest

open HasVocabulary

theorem vocOfBigDis {l : List Formula} : x ∈ voc (bigDis l) → ∃φ ∈ l, x ∈ voc φ :=
  by
    intro hyp
    induction l
    case nil  => aesop
    case cons head tail ih =>
      cases em (x ∈ vocabOfFormula head)
      · simp; tauto
      · unfold bigDis at hyp; aesop

theorem vocOfBigCon {l : List Formula} : x ∈ voc (bigCon l) → ∃φ ∈ l, x ∈ voc φ :=
  by
    intro hyp
    induction l
    case nil  => aesop
    case cons head tail ih =>
      cases em (x ∈ vocabOfFormula head)
      · simp; tauto
      · unfold bigCon at hyp; aesop

@[simp]
theorem conempty : bigCon ∅ = (⊤ : Formula) := by rfl

@[simp]
theorem consingle {f : Formula} : bigCon [f] = f := by rfl

@[simp]
def dis : List Formula → Formula
  | [] => ⊥
  | [f] => f
  | f :: rest => f⋁dis rest

@[simp]
theorem disempty : dis ∅ = (⊥ : Formula) := by rfl

@[simp]
theorem dissingle {f : Formula} : dis [f] = f := by rfl

@[simp]
def discon : List (List Formula) → Formula
  | [] => ⊥
  | [X] => bigCon X
  | X :: rest => bigCon X⋁discon rest

@[simp]
theorem disconempty : discon {∅} = (⊤ : Formula) := by rfl

@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl

theorem conEvalHT {X f W M} {w : W} :
    Evaluate (M, w) (bigCon (f :: X)) ↔ Evaluate (M, w) f ∧ Evaluate (M, w) (bigCon X) :=
  by
  cases X
  <;> simp

theorem conEval {W M X} {w : W} : Evaluate (M, w) (bigCon X) ↔ ∀ f ∈ X, Evaluate (M, w) f :=
  by
  induction X
  · simp
  · rw [conEvalHT]
    simp
    intro _
    assumption

theorem disconEvalHT {X} : ∀ XS, discon (X :: XS) ≡ bigCon X ⋁ discon XS :=
  by
  unfold semEquiv
  intro XS W M w
  cases XS
  <;> simp

theorem disconEval {W M} {w : W} :
    ∀ {N : Nat} XS,
      List.length XS = N → (Evaluate (M, w) (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, Evaluate (M, w) f) :=
  by
  intro N
  refine Nat.strong_induction_on N ?_ -- FIXME `induction N using Nat.strong_induction_on`?
  intro n IH XS nDef
  subst nDef
  rcases XS with _ | ⟨X,XS⟩
  · simp
  specialize IH XS.length (by simp) XS (by rfl)
  rw [disconEvalHT, evalDis, IH]
  constructor
  · -- →
    intro lhs
    rcases lhs with lhs | lhs
    · use X
      simp
      rw [conEval] at lhs
      tauto
    · rcases lhs with ⟨Y, claim⟩
      use Y
      simp
      tauto
  · -- ←
    rintro ⟨Y, Y_in, Ysat⟩
    simp at Y_in
    rcases Y_in with Y_in | Y_in
    · left
      subst Y_in
      rw [conEval]; tauto
    · right
      use Y

-- UPLUS

@[simp]
def pairunionList : List (List Formula) → List (List Formula) → List (List Formula)
  | xls, yls => List.flatten (xls.map fun xl => yls.map fun yl => xl ++ yl)

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
  rw [disconEval (XS ⊎ YS) (by rfl)]
  simp
  rw [disconEval XS (by rfl)]
  rw [disconEval YS (by rfl)]
  aesop

theorem disconOr {XS YS} : discon (XS ∪ YS) ≡ discon XS ⋁ discon YS :=
  by
  unfold semEquiv
  intro W M w
  rw [disconEval (XS ∪ YS) (by rfl)]
  simp
  rw [disconEval XS (by rfl)]
  rw [disconEval YS (by rfl)]
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
    cases em (∃ Y, Y ∈ XS ∧ ∀ (f : Formula), f ∈ Y → Evaluate (M, w) f)
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

@[simp]
lemma bigDis_sat {l : List Formula} {M : KripkeModel W} {w : W} :
    Evaluate (M, w) (bigDis l) ↔ ∃φ ∈ l, Evaluate (M, w) φ :=
  by
    constructor
    · intro satDis
      induction l
      case nil => tauto
      case cons head tail ih =>
        cases em (Evaluate (M, w) head)
        · use head; aesop
        · have : ((Evaluate (M, w) head) ∨ Evaluate (M, w) (bigDis tail)) :=
            by unfold bigDis; aesop
          aesop
    · intro satOne
      induction l
      case nil => tauto
      case cons head tail ih =>
        have : Evaluate (M, w) (bigDis (head :: tail)) ↔
          ((Evaluate (M, w) head) ∨ Evaluate (M, w) (bigDis tail)) :=
          by unfold bigDis; aesop
        aesop

@[simp]
lemma bigCon_sat {l : List Formula} {M : KripkeModel W} {w : W} :
    Evaluate (M, w) (bigCon l) ↔ ∀φ ∈ l, Evaluate (M, w) φ :=
  by
    constructor
    · intro satCon
      induction l
      case nil => tauto
      case cons head tail ih =>
        have : ((Evaluate (M, w) head) ∧ Evaluate (M, w) (bigCon tail)) :=
          by unfold bigCon; aesop
        aesop
    · intro satAll
      induction l
      case nil => tauto
      case cons head tail ih =>
        have : Evaluate (M, w) (bigCon (head :: tail)) ↔
          ((Evaluate (M, w) head) ∧ Evaluate (M, w) (bigCon tail)) :=
          by unfold bigCon; aesop
        aesop

lemma bigDis_union_sat_down {X : Finset Formula} {l : List Formula} :
    Satisfiable (X ∪ {bigDis l}) → ∃φ ∈ l, Satisfiable (X ∪ {φ}) :=
  by simp at *; tauto

lemma bigCon_union_sat_down {X : Finset Formula} {l : List Formula} :
    Satisfiable (X ∪ {bigCon l}) → ∀φ ∈ l, Satisfiable (X ∪ {φ}) :=
  by simp at *; tauto

lemma bigConNeg_union_sat_down {X : Finset Formula} {l : List Formula} :
    Satisfiable (X ∪ {bigCon (l.map (~·))}) → ∀φ ∈ l, Satisfiable (X ∪ {~φ}) :=
  by
    intro hyp
    rcases hyp with ⟨W, M, w, sat⟩
    simp at *
    rcases sat with ⟨lNotSat, XSat⟩
    intro φ inl
    use W, M, w
    apply And.intro (lNotSat φ inl) (XSat)


-- Probably redundant but leaving these here for now
lemma eval_neg_BigDis_iff_eval_bigConNeg {l : List Formula} {M : KripkeModel W} {w : W} :
    Evaluate (M, w) (~(bigDis l)) ↔ Evaluate (M, w) (~~bigCon (l.map (~·))) := by aesop

lemma eval_negBigCon_iff_eval_bigDisNeg {l : List Formula} {M : KripkeModel W} {w : W} :
    Evaluate (M, w) (~(bigCon l)) ↔ Evaluate (M, w) (bigDis (l.map (~·))) := by aesop

lemma sat_negBigDis_iff_sat_bigConNeg {l : List Formula} :
    Satisfiable (~(bigDis l)) ↔ Satisfiable (~~bigCon (l.map (~·))) := by aesop

lemma sat_negBigCon_iff_sat_bigDisNeg {l : List Formula} :
    Satisfiable (~(bigCon l)) ↔ Satisfiable (bigDis (l.map (~·))) := by aesop
