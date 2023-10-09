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

@[simp]
theorem consingle {f : Formula} : Con [f] = f := by rfl

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
  | [X] => Con X
  | X :: rest => Con X⋁discon rest

@[simp]
theorem disconempty : discon {∅} = (⊤ : Formula) := by rfl

@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl

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


-- UPLUS

@[simp]
def pairunionList : List (List Formula) → List (List Formula) → List (List Formula)
  | xls, yls => List.join (xls.map fun xl => yls.map fun yl => xl ++ yl)

@[simp]
def pairunionFinset : Finset (Finset Formula) → Finset (Finset Formula) → Finset (Finset Formula)
  | X, Y => {X.biUnion fun ga => Y.biUnion fun gb => ga ∪ gb}

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
  constructor
  · -- →
    intro lhs
    rcases lhs with ⟨XY, ⟨X, ⟨X_in, ⟨Y, Y_in, X_Y_is_XY⟩⟩⟩, satXY⟩
    rw [← X_Y_is_XY] at satXY
    simp at satXY
    constructor
    · use X
      constructor
      use X_in
      intro f f_in
      apply satXY
      tauto
    · use Y
      constructor
      use Y_in
      intro f f_in
      apply satXY
      tauto
  · -- ←
    intro rhs
    rcases rhs with ⟨⟨X, X_in, satX⟩, ⟨Y, Y_in, satY⟩⟩
    use X ++ Y
    constructor
    · use X
      constructor
      · assumption
      · use Y
    intro f
    intro f_in
    simp at f_in
    cases' f_in with f_in_X f_in_Y -- TODO: nicer match syntax?
    · apply satX f f_in_X
    · apply satY f f_in_Y

theorem disconOr {XS YS} : discon (XS ∪ YS) ≡ discon XS ⋁ discon YS :=
  by
  sorry

theorem union_elem_uplus {XS YS : Finset (Finset Formula)} {X Y : Finset Formula} :
  X ∈ XS → Y ∈ YS → ((X ∪ Y) ∈ (XS ⊎ YS)) :=
  by
  intro X_in Y_in
  simp
  ext1 -- this seems to go wrong?
  constructor
  · intro f_in
    simp at f_in
    simp
    use X
    constructor
    · exact X_in
    · use Y
  · intro f_in
    simp
    simp at f_in
    rcases f_in with ⟨X', X'_in, Y', Y'_in, f_in⟩
    -- But now X' Y' are unrelated to X and Y :-(
    sorry
