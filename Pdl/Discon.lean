import Pdl.Semantics
import Pdl.Vocab

/-! # (Big) Disjunction and Conjunction

Here we define ⋀ and ⋁ on formulas and seveal helper lemmas.
-/

/-! ## Conjunction -/

-- FIXME: rename "Con" to "con"
@[simp]
def Con : List Formula → Formula
  | [] => ⊤
  | [f] => f
  | f :: rest => f⋀Con rest

@[simp]
theorem conempty : Con ∅ = (⊤ : Formula) := by rfl

@[simp]
theorem consingle {f : Formula} : Con [f] = f := by rfl

theorem listEq_to_conEq : l1 = l2 → Con l1 = Con l2 := by
  aesop

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

/-- Vocabulary of Conjunction -/
theorem in_voc_con n (L : List Formula) :
    n ∈ (Con L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [Con, Formula.voc]
  case cons h t IH =>
    induction t -- needed to select case in `Con`
    · simp [Con]
    case cons h t IH =>
      simp [Con, Formula.voc] at *
      rw [← IH]

/-! ## Disjunction -/

@[simp]
def dis : List Formula → Formula
  | [] => ⊥
  | [f] => f
  | f :: rest => f ⋁ dis rest

@[simp]
theorem disempty : dis ∅ = (⊥ : Formula) := rfl

@[simp]
theorem dissingle {f : Formula} : dis [f] = f := rfl

theorem listEq_to_disEq : l1 = l2 → dis l1 = dis l2 := by
  aesop

theorem disEvalHT {X f W M} {w : W} :
    evaluate M w (dis (f :: X)) ↔ evaluate M w f ∨ evaluate M w (dis X) :=
  by
  induction' X with g X IH
  · simp
  · simp
    tauto

theorem disEval {W M X} {w : W} : evaluate M w (dis X) ↔ ∃ f ∈ X, evaluate M w f :=
  by
  induction' X with f X IH
  · simp
  · rw [disEvalHT]
    simp [IH]

/-- Vocabulary of Disjunction -/
theorem in_voc_dis n (L : List Formula) :
    n ∈ (dis L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [dis, Formula.voc]
  case cons h t IH =>
    induction t -- needed to select case in `dis`
    · simp [dis]
    case cons h t IH =>
      simp [dis, Formula.voc] at *
      rw [← IH]

/-! ## Disjunction of Conjunctions -/

@[simp]
def discon : List (List Formula) → Formula
  | [] => ⊥
  | [X] => Con X
  | X :: rest => Con X⋁discon rest

@[simp]
theorem disconempty : discon {∅} = (⊤ : Formula) := by rfl

@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl

theorem disconEvalHT {X} : ∀ XS, discon (X :: XS)≡Con X⋁discon XS :=
  by
  unfold semEquiv
  intro XS W M w
  cases' XS with Y YS
  · simp
  · simp

theorem disconEval' {W M} {w : W} :
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

theorem disconEval {W M} {w : W} :
    ∀ XS,
      (evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f) :=
  by
    intro XS
    apply disconEval' XS rfl

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
    cases (Classical.em (∃ Y, Y ∈ XS ∧ ∀ (f : Formula), f ∈ Y → evaluate M w f))
    case inl hyp =>
      rcases hyp with ⟨X, X_in, satX⟩
      use X
      exact ⟨Or.inl X_in, satX⟩
    case inr nothyp =>
      specialize rhs nothyp
      rcases rhs with ⟨Y, Y_in, satY⟩
      use Y
      exact ⟨Or.inr Y_in, satY⟩

/-! ## Pairwise Union -/

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
  rw [disconEval (XS ⊎ YS)]
  simp
  rw [disconEval XS]
  rw [disconEval YS]
  aesop

theorem union_elem_uplus {XS YS : Finset (Finset Formula)} {X Y : Finset Formula} :
  X ∈ XS → Y ∈ YS → ((X ∪ Y) ∈ (XS ⊎ YS)) :=
  by
  intro X_in Y_in
  simp
  exact ⟨X, X_in, Y, Y_in, rfl⟩

/-- Helper for `oneSidedLocalRuleTruth`, used with `g = Yset`. -/
theorem mapCon_mapForall (M : KripkeModel W) w φ
    (g : (List Formula × List Program) → Formula → List Formula) :
    (∃ f ∈ List.map (fun Fδ => Con (g Fδ φ)) X, evaluate M w f) ↔
    ∃ fs ∈ List.map (fun Fδ => g Fδ φ) X, ∀ f ∈ fs, evaluate M w f := by
  simp_all
  constructor
  · rintro ⟨f,⟨a, b, ab_in, def_f⟩, w_f⟩
    subst def_f
    use g (a,b) φ
    constructor
    · use a, b
    · intro f f_in; rw [conEval] at w_f; specialize w_f f; tauto
  · rintro ⟨fs,⟨⟨a, b, ab_in, def_fs⟩, w_fs⟩⟩
    subst def_fs
    use Con (g (a, b) φ)
    constructor
    · use a, b
    · rw [conEval]; intro f; tauto
