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
    evaluate M w (Con (f :: X)) ↔ evaluate M w f ∧ evaluate M w (Con X) := by
  induction X
  · simp
  · simp

theorem conEval {W M X} {w : W} : evaluate M w (Con X) ↔ ∀ f ∈ X, evaluate M w f := by
  induction X
  · simp
  · rw [conEvalHT]
    simp_all

/-- Vocabulary of Conjunction -/
theorem in_voc_con n (L : List Formula) :
    n ∈ (Con L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [Con, Formula.voc]
  case cons h t IH =>
    induction t <;> simp_all

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
  induction X
  · simp
  · simp
    tauto

theorem disEval {W M X} {w : W} : evaluate M w (dis X) ↔ ∃ f ∈ X, evaluate M w f :=
  by
  induction X
  · simp
  · rw [disEvalHT]
    simp_all

/-- Vocabulary of Disjunction -/
theorem in_voc_dis n (L : List Formula) :
    n ∈ (dis L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [dis, Formula.voc]
  case cons h t IH =>
    induction t <;> simp_all

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
  cases XS <;> simp

theorem disconEval' {W M} {w : W} :
    ∀ {N : Nat} XS,
      List.length XS = N → (evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f) :=
  by
  intro N
  refine Nat.strong_induction_on N ?_ -- FIXME use `induction N using Nat.strong_induction_on`???
  intro n IH XS nDef
  subst nDef
  rcases XS with _ | ⟨X,XS⟩
  · simp
  specialize IH XS.length (by simp) XS (by rfl)
  rw [disconEvalHT, evalDis, IH]
  constructor
  · -- →
    intro lhs
    rcases lhs with lhs|lhs
    · use X
      simp
      rw [conEval] at lhs
      tauto
    · rcases lhs with ⟨Y,claim⟩
      use Y
      simp
      tauto
  · -- ←
    intro rhs
    rcases rhs with ⟨Y,Y_in,Ysat⟩
    simp only [List.mem_cons] at Y_in
    rcases Y_in with Y_in|Y_in
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
  simp only [List.mem_union_iff, Formula.or, evaluate.eq_3, evaluate, not_and, not_not]
  rw [disconEval XS, disconEval YS]
  constructor
  · -- →
    intro lhs
    rcases lhs with ⟨Z, Z_in, w_sat_Z⟩
    intro notL
    simp only [not_exists, not_and, not_forall, exists_prop] at notL
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
  simp only [listHasUplus, pairunionList, List.mem_flatten, List.mem_map, exists_exists_and_eq_and,
    exists_exists_and_exists_and_eq_and, List.mem_append, evaluate]
  rw [disconEval XS, disconEval YS]
  aesop

theorem union_elem_uplus {XS YS : Finset (Finset Formula)} {X Y : Finset Formula} :
  X ∈ XS → Y ∈ YS → ((X ∪ Y) ∈ (XS ⊎ YS)) :=
  by
  intro X_in Y_in
  simp only [finsetHasUplus, pairunionFinset, Finset.mem_biUnion, Finset.mem_singleton]
  exact ⟨X, X_in, Y, Y_in, rfl⟩

/-- Helper for `oneSidedLocalRuleTruth`, used with `g = Yset`. -/
theorem mapCon_mapForall (M : KripkeModel W) w φ
    (g : (List Formula × List Program) → Formula → List Formula) :
    (∃ f ∈ List.map (fun Fδ => Con (g Fδ φ)) X, evaluate M w f) ↔
    ∃ fs ∈ List.map (fun Fδ => g Fδ φ) X, ∀ f ∈ fs, evaluate M w f := by
  simp_all only [List.mem_map, Prod.exists, ↓existsAndEq, and_true]
  constructor <;> grind [conEval]
