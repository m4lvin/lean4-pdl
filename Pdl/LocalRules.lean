import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Multiset.DershowitzManna

import Pdl.Sequent
import Pdl.UnfoldBox
import Pdl.UnfoldDia

/-! ## Local rules and local rule applications  -/

open HasLength

/-! ## One-sided local rules -/

/-- Local rules replace a given set of formulas by other sets, one for each branch.
The list of resulting branches can be empty, representing that the given set is closed.
In the Haskell prover this is done in "ruleFor" in the Logic.PDL.Prove.Tree module. -/
inductive OneSidedLocalRule : List Formula → List (List Formula) → Type
  -- PROP LOGIC
  -- closing rules:
  | bot                 : OneSidedLocalRule [⊥]      ∅
  | not (φ   : Formula) : OneSidedLocalRule [φ, ~φ]  ∅
  | neg (φ   : Formula) : OneSidedLocalRule [~~φ]    [[φ]]
  | con (φ ψ : Formula) : OneSidedLocalRule [φ ⋀ ψ]  [[φ,ψ]]
  | nCo (φ ψ : Formula) : OneSidedLocalRule [~(φ⋀ψ)] [[~φ], [~ψ]]
  -- PROGRAMS
  -- the two general local rules:
  | box (α φ) : (notAtom : ¬ α.isAtomic) → OneSidedLocalRule [ ⌈α⌉φ] (unfoldBox     α φ)
  | dia (α φ) : (notAtom : ¬ α.isAtomic) → OneSidedLocalRule [~⌈α⌉φ] (unfoldDiamond α φ)
  deriving DecidableEq, Repr

theorem oneSidedLocalRuleTruth (lr : OneSidedLocalRule X B) : Con X ≡ discon B :=
  by
  intro W M w
  cases lr
  all_goals try (simp; done) -- takes care of all propositional rules
  case box α φ notAtom =>
    rw [conEval]
    simp only [List.mem_singleton, forall_eq]
    rw [localBoxTruth α φ W M w]
    simp only [disEval, List.mem_map, exists_exists_and_eq_and, unfoldBox, disconEval]
    constructor
    · rintro ⟨l,hyp⟩; use l; rw [conEval] at hyp; tauto
    · rintro ⟨l,hyp⟩; use l; rw [conEval]; tauto
  case dia α φ notAtom =>
    rw [conEval]
    simp only [List.mem_singleton, forall_eq, unfoldDiamond]
    rw [localDiamondTruth α φ W M w, disEval, disconEval]
    apply mapCon_mapForall

/-! ## Loaded Rules -/

/-- The loaded diamond rule, given by `unfoldDiamondLoaded`.
In MB page 19 these were multiple rules ¬u, ¬; ¬* and ¬?.
It replaces the loaded formula by up to one loaded formula and a list of normal formulas.
It's a bit annoying to need the rule twice here due to the definition of LoadFormula
and the extra definition of `unfoldDiamondLoaded'`. -/
inductive LoadRule : NegLoadFormula → List (List Formula × Option NegLoadFormula) → Type
  | dia  {α χ} : (notAtom : ¬ α.isAtomic)
                → LoadRule (~'⌊α⌋(χ : LoadFormula)) (unfoldDiamondLoaded  α χ)
  | dia' {α φ} : (notAtom : ¬ α.isAtomic)
                → LoadRule (~'⌊α⌋(φ : Formula    )) (unfoldDiamondLoaded' α φ)
  deriving DecidableEq, Repr

/-- Given a LoadRule application, define the equivalent unloaded rule application.
This allows re-using `oneSidedLocalRuleTruth` to prove `loadRuleTruth`. -/
def LoadRule.unload : LoadRule (~'χ) B → OneSidedLocalRule [~χ.unload] (B.map pairUnload)
| @dia α χ notAtom => unfoldDiamondLoaded_eq α χ ▸ OneSidedLocalRule.dia α χ.unload notAtom
| @dia' α φ notAtom => unfoldDiamondLoaded'_eq α φ ▸ OneSidedLocalRule.dia α φ notAtom

/-- The loaded unfold rule is sound and invertible.
In the notes this is part of localRuleTruth. -/
theorem loadRuleTruth (lr : LoadRule (~'χ) B) :
    (~χ.unload) ≡ dis (B.map (Con ∘ pairUnload)) :=
  by
  intro W M w
  have := oneSidedLocalRuleTruth (lr.unload) W M w
  simp only [Con, evaluate, disconEval, List.mem_map] at this
  simp only [evaluate, disEval, List.mem_map]
  rw [this]
  clear this
  simp only [Prod.exists]
  constructor
  · rintro ⟨Y, ⟨a, ⟨b, ab_in_B, def_Y⟩⟩, w_Y⟩
    use Con Y
    simp_all only [conEval, implies_true, and_true]
    use a, b, ab_in_B
    rw [← def_Y]
    simp
  · rintro ⟨f, ⟨a, b, ab_in_B, def_f⟩, w_f⟩
    subst def_f
    simp at w_f
    rw [conEval] at w_f
    use pairUnload (a,b)
    constructor
    · use a, b
    · exact w_f

/-! ## Local Rules -/

/-- A local rule is a `OneSidedLocalRule`, a left-right contradiction, or a `LoadRule`.
Note that formulas can be in four places: left, right, loaded left, loaded right.

We do *not* have neg/contradiction rules between loaded and unloaded formulas (i.e.
between `({unload χ}, ∅, some (Sum.inl ~χ))` and `(∅, {unload χ}, some (Sum.inr ~χ))`)
because in any such case we could also close the tableau before or without loading.

The `YS_def` arguments in non-terminal rules enables deriving `DecidableEq` for `LocalRule`.
-/
inductive LocalRule : Sequent → List Sequent → Type
  | oneSidedL {precond ress YS} (orule : OneSidedLocalRule precond ress)
      (YS_def : YS = ress.map fun res => (res,∅,none)) : LocalRule (precond,∅,none) YS
  | oneSidedR {precond ress YS} (orule : OneSidedLocalRule precond ress)
      (YS_def : YS = ress.map fun res => (∅,res,none)) : LocalRule (∅,precond,none) YS
  | LRnegL (ϕ : Formula) : LocalRule ([ϕ], [~ϕ], none) ∅ --  ϕ on left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ([~ϕ], [ϕ], none) ∅ -- ~ϕ on left side,  ϕ on the right
  | loadedL {ress YS} (χ : LoadFormula) (lrule : LoadRule (~'χ) ress)
      (YS_def : YS = ress.map fun (X, o) => (X, ∅, o.map Sum.inl))
      : LocalRule (∅, ∅, some (Sum.inl (~'χ))) YS
  | loadedR {ress YS} (χ : LoadFormula) (lrule : LoadRule (~'χ) ress)
      (YS_def : YS = ress.map fun (X, o) => (∅, X, o.map Sum.inr))
      : LocalRule (∅, ∅, some (Sum.inr (~'χ))) YS
  deriving Repr, DecidableEq

@[simp]
def applyLocalRule {Lcond Rcond Ocond ress} :
  LocalRule (Lcond, Rcond, Ocond) ress → Sequent → List Sequent
  | _, ⟨L, R, O⟩ => ress.map <|
      fun (Lnew, Rnew, Onew) => ( L.diff Lcond ++ Lnew
                                , R.diff Rcond ++ Rnew
                                , Olf.change O Ocond Onew )

/-- Helper originally written for Lemma 6.14 but currently unused. -/
def principalFormulaForLocalRule : LocalRule X YS -> AnyFormula
  | .oneSidedL orule _ =>
      match orule with
        | .bot      => Formula.bottom
        | .con φ ψ =>  (φ ⋀ ψ)
        | .not φ => φ
        | .neg φ => ~~φ
        | .nCo φ ψ => ~(Formula.and φ ψ)
        | .dia α φ _ => ~⌈α⌉φ
        | .box α φ _ => ⌈α⌉φ
  | .oneSidedR orule _ =>
      match orule with
        | .bot      => Formula.bottom
        | .con φ ψ => φ ⋀ ψ
        | .not φ => φ
        | .neg φ => ~~φ
        | .nCo φ ψ => ~(Formula.and φ ψ)
        | .dia α φ _  => ~⌈α⌉φ
        | .box α φ _   => ⌈α⌉φ
  | .LRnegL φ => φ
  | .LRnegR φ => φ
  | .loadedL φ _ _ => φ
  | .loadedR φ _ _ => φ

lemma oneSidedL_preserves_right {LRO : Sequent}
    {Lcond : List Formula} (Lpreproof : Lcond ⊆ LRO.L)
    {Lres : List (List Formula)} (orule : OneSidedLocalRule Lcond Lres)
    {YS : List Sequent} (YS_def : YS = List.map (fun res => (res, ∅, none)) Lres)
    : ∀ c ∈ applyLocalRule (LocalRule.oneSidedL orule YS_def) LRO, c.right = LRO.right := by
  rcases LRO with ⟨L,R,O⟩
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp at *
  grind

lemma oneSidedR_preserves_left {LRO : Sequent}
    {Rcond : List Formula} (Rpreproof : Rcond ⊆ LRO.R)
    {Rres : List (List Formula)} (orule : OneSidedLocalRule Rcond Rres)
    {YS : List Sequent} (YS_def : YS = List.map (fun res => (∅, res, none)) Rres)
    : ∀ c ∈ applyLocalRule (LocalRule.oneSidedR orule YS_def) LRO, c.left = LRO.left := by
  rcases LRO with ⟨L,R,O⟩
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp at *
  grind

open HasSat

lemma oneSidedL_sat_down (LRO : Sequent)
    {Lcond : List Formula} (Lpreproof : Lcond ⊆ LRO.L)
    {Lres : List (List Formula)} (orule : OneSidedLocalRule Lcond Lres)
    {YS : List Sequent} (YS_def : YS = List.map (fun res => (res, ∅, none)) Lres)
    {X : List Formula} (LX_sat : satisfiable (Sequent.left LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.oneSidedL orule YS_def) LRO, satisfiable (c.left ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  subst YS_def
  rcases LX_sat with ⟨W, M, w, satM⟩
  have : evaluate M w (Con Lcond) := by simp [conEval]; aesop
  have := (oneSidedLocalRuleTruth orule W M w).1 this
  rw [disconEval] at this
  rcases this with ⟨L', L'_in, w_L'⟩
  simp [applyLocalRule]
  refine ⟨L', L'_in, W, M, w, fun φ φ_in => ?_⟩
  specialize @satM φ
  have := List.diff_subset L Lcond
  rcases φ_in with (φ_in_LnoCond | φ_in_L') | φ_in_O <;> aesop

lemma oneSidedR_sat_down (LRO : Sequent)
    {Rcond : List Formula} (Rpreproof : Rcond ⊆ LRO.R)
    {Rres : List (List Formula)} (orule : OneSidedLocalRule Rcond Rres)
    {YS : List Sequent} (YS_def : YS = List.map (fun res => (∅, res, none)) Rres)
    {X : List Formula} (RX_sat : satisfiable (Sequent.right LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.oneSidedR orule YS_def) LRO, satisfiable (c.right ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  subst YS_def
  rcases RX_sat with ⟨W, M, w, satM⟩
  have : evaluate M w (Con Rcond) := by simp [conEval]; aesop
  have := (oneSidedLocalRuleTruth orule W M w).1 this
  rw [disconEval] at this
  rcases this with ⟨L', L'_in, w_L'⟩
  simp [applyLocalRule]
  refine ⟨L', L'_in, W, M, w, fun φ φ_in => ?_⟩
  specialize @satM φ
  have := List.diff_subset R Rcond
  rcases φ_in with (φ_in_LnoCond | φ_in_L') | φ_in_O <;> aesop

-- Following four lemmas are almost the same, but then for the loaded diamond rules.

/-- Applying a `LoadRule` on the left will leave the right unchanged. -/
lemma loadedL_preserves_right {LRO : Sequent}
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inl (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : List Sequent} (YS_def : YS = ress.map fun (X, o) => (X, ∅, o.map Sum.inl))
    : ∀ c ∈ applyLocalRule (LocalRule.loadedL χ lrule YS_def) LRO, c.right = LRO.right := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp at *
  rintro _ olnlf _in_ress ⟨⟩
  rcases olnlf with _|⟨_⟩ <;> simp

/-- Applying a `LoadRule` on the right will leave the left unchanged. -/
lemma loadedR_preserves_left {LRO : Sequent}
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inr (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : List Sequent} (YS_def : YS = ress.map fun (X, o) => (∅, X, o.map Sum.inr))
    : ∀ c ∈ applyLocalRule (LocalRule.loadedR χ lrule YS_def) LRO, c.left = LRO.left := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  rintro ⟨L',R',O'⟩
  subst YS_def
  simp at *
  rintro _ olnlf _in_ress ⟨⟩
  rcases olnlf with _|⟨_⟩ <;> simp

/-- Applying a `LoadRule` on the left preserves satisfiability of the left,
even together with any other list of formulas as context. -/
lemma loadedL_sat_down (LRO : Sequent)
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inl (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : List Sequent} (YS_def : YS = ress.map fun (X, o) => (X, ∅, o.map Sum.inl))
    {X : List Formula} (LX_sat : satisfiable (Sequent.left LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.loadedL χ lrule YS_def) LRO, satisfiable (c.left ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  subst YS_def
  rcases LX_sat with ⟨W, M, w, satM⟩
  have w_nχ : evaluate M w (~χ.unload) := by apply satM; simp [Olf.L]
  have := (loadRuleTruth lrule W M w).1 w_nχ; clear w_nχ
  simp only [disEval, List.mem_map, Function.comp_apply, Prod.exists] at this
  rcases this with ⟨φ, ⟨ψs, φ0, _in_ress, def_φ⟩ , w_φ⟩
  use (L ++ ψs, R, φ0.map Sum.inl)
  subst def_φ
  simp
  constructor
  · use ψs, φ0, _in_ress
  · use W, M, w
    intro φ φ_in
    specialize @satM φ
    rcases φ_in with (φ_in_L | φ_in_ψs | φ_in_OL) | φ_in_X
    · aesop
    · simp [conEval, pairUnload] at w_φ; aesop
    · simp [Olf.L] at φ_in_OL
      cases φ0 <;> simp [conEval, pairUnload] at *
      subst φ_in_OL
      apply w_φ
      simp
    · aesop

/-- Applying a `LoadRule` on the right preserves satisfiability of the right,
even together with any other list of formulas as context. -/
lemma loadedR_sat_down (LRO : Sequent)
    (χ : LoadFormula) (Opreproof : LRO.O = some (Sum.inr (~'χ)))
    {ress} (lrule : LoadRule (~'χ) ress)
    {YS : List Sequent} (YS_def : YS = ress.map fun (X, o) => (∅, X, o.map Sum.inr))
    {X : List Formula} (RX_sat : satisfiable (Sequent.right LRO ∪ X))
    : ∃ c ∈ applyLocalRule (LocalRule.loadedR χ lrule YS_def) LRO, satisfiable (c.right ∪ X) := by
  rcases LRO with ⟨L,R,O⟩
  cases Opreproof
  subst YS_def
  rcases RX_sat with ⟨W, M, w, satM⟩
  have w_nχ : evaluate M w (~χ.unload) := by apply satM; simp [Olf.R]
  have := (loadRuleTruth lrule W M w).1 w_nχ; clear w_nχ
  simp only [disEval, List.mem_map, Function.comp_apply, Prod.exists, ↓existsAndEq,
    and_true] at this
  rcases this with ⟨ψs, φ0, _in_ress, w_φ⟩
  simp only [applyLocalRule, List.empty_eq, List.diff_nil, Olf.change_some_some_eq, List.map_map,
    List.mem_map, Function.comp_apply, List.append_nil, Prod.exists, listHasSat, List.mem_union_iff,
    ↓existsAndEq, and_true, Sequent.right_eq, List.append_assoc, List.mem_append]
  use ψs, φ0, _in_ress
  use W, M, w
  intro φ φ_in
  specialize @satM φ
  rcases φ_in with (φ_in_L | φ_in_ψs | φ_in_OL) | φ_in_X
  · aesop
  · simp [conEval, pairUnload] at w_φ; aesop
  · simp only [Olf.R] at φ_in_OL
    cases φ0 <;> simp [conEval, pairUnload] at *
    subst φ_in_OL
    apply w_φ
    simp
  · aesop

/-! ## Local Rule Applications -/

/-- A local rule application going from `⟨L,R,O⟩` to `C` consists of a
local rule `lr` replacing `⟨Lcond, Rcond, Ocond⟩` by `ress` and
proofs that `⟨Lcond, Rcond, Ocond⟩` is a subsequent of `⟨L,R,O⟩`
and that `C` are the results of applying `lr` to `⟨L,R,O⟩`. -/
structure LocalRuleApp where
    L : List Formula := by grind
    R : List Formula := by grind
    O : Olf := by grind
    Lcond : List Formula := []
    Rcond : List Formula := []
    Ocond : Olf := none
    ress : List Sequent := by grind
    lr : LocalRule (Lcond, Rcond, Ocond) ress
    C : List Sequent := applyLocalRule lr (L,R,O)
    hC : C = applyLocalRule lr (L,R,O) := by rfl
    preconditionProof : List.Subperm Lcond L ∧ List.Subperm Rcond R ∧ Ocond ⊆ O
  deriving DecidableEq

@[simp]
abbrev LocalRuleApp.X (lra : LocalRuleApp) : Sequent := ⟨lra.L, lra.R, lra.O⟩

/-- Any local rule application is sound and invertible. -/
theorem localRuleTruth
    (lra : LocalRuleApp) {W} (M : KripkeModel W) (w : W)
  : (M,w) ⊨ lra.X ↔ ∃ Ci ∈ lra.C, (M,w) ⊨ Ci
  := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconditionProof⟩
  simp at *
  cases rule
  case oneSidedL ress orule ress_def =>
    subst ress_def
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp [applyLocalRule] at *
    constructor
    · intro w_LRO
      have : evaluate M w (discon ress) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [List.mem_union_iff]
        exact Or.inl <| Or.inl <| List.Subperm.subset preconditionProof f_in
      rw [disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [List.mem_union_iff, List.mem_append] at f_in
        rcases f_in with (((f_in_L | f_in_Y) | f_in_R) | f_in_O)
        · apply w_LRO f; simp only [List.mem_union_iff]
          exact Or.inl <| Or.inl <| List.diff_subset L Lcond f_in_L
        · exact claim f f_in_Y
        · apply w_LRO f; simp only [List.mem_union_iff]
          tauto
        · apply w_LRO f; simp only [List.mem_union_iff]
          exact Or.inr f_in_O
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      simp only [List.mem_union_iff] at f_in
      rcases f_in with ((f_in_L | f_in_R) | f_in_O)
      · rcases em (f ∈ Lcond) with f_in_cond | f_notin_cond
        · have : ∀ f ∈ Lcond, evaluate M w f := by
            rw [← conEval, osTruth, disconEval]
            use Y
            constructor
            · exact Y_in
            · intro f f_in; apply w_LYRO; simp_all
          exact this f f_in_cond
        · apply w_LYRO
          simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl <| Or.inl <| Or.inl <| List.mem_diff_of_mem f_in_L f_notin_cond
      · apply w_LYRO; simp_all
      · apply w_LYRO; simp_all
  case oneSidedR ress orule ress_def =>
    subst ress_def
    -- based on oneSidedL case
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp [applyLocalRule] at *
    constructor
    · intro w_LRO
      have : evaluate M w (discon ress) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [List.mem_union_iff]
        exact Or.inl <| Or.inr <| List.Subperm.subset preconditionProof f_in
      rw [disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [List.mem_union_iff, List.mem_append] at f_in
        rcases f_in with ((f_in_L | (f_in_R | f_in_Y)) | f_in_O)
        · apply w_LRO f; simp only [List.mem_union_iff]
          exact Or.inl <| Or.inl f_in_L
        · apply w_LRO f; simp only [List.mem_union_iff]
          exact Or.inl <| Or.inr <| List.diff_subset R Rcond f_in_R
        · exact claim f f_in_Y
        · apply w_LRO f; simp only [List.mem_union_iff]
          exact Or.inr f_in_O
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      simp only [List.mem_union_iff] at f_in
      rcases f_in with ((f_in_L | f_in_R) | f_in_O)
      · apply w_LYRO; simp_all
      · rcases em (f ∈ Rcond) with f_in_cond | f_notin_cond
        · have : ∀ f ∈ Rcond, evaluate M w f := by
            rw [← conEval, osTruth, disconEval]
            use Y
            constructor
            · exact Y_in
            · intro f f_in; apply w_LYRO; simp_all
          exact this f f_in_cond
        · apply w_LYRO
          simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl <| Or.inr <| Or.inl <| List.mem_diff_of_mem f_in_R f_notin_cond
      · apply w_LYRO; simp_all
  case LRnegL φ =>
    subst hC
    simp [applyLocalRule] at *
    intro hyp
    have := hyp φ
    have := hyp (~φ)
    aesop
  case LRnegR φ =>
    subst hC
    simp [applyLocalRule] at *
    intro hyp
    have := hyp φ
    have := hyp (~φ)
    aesop
  case loadedL ress χ lrule ress_def =>
    subst ress_def
    have := loadRuleTruth lrule W M w
    rw [disEval] at this
    subst hC
    simp at preconditionProof
    subst preconditionProof
    simp at *
    constructor
    · intro hyp
      have hyp' := hyp (~χ.unload)
      simp only [Option.map_some, Sum.elim_inl, negUnload, Option.toList_some, List.mem_union_iff,
        List.mem_cons, List.not_mem_nil, or_false, or_true, evaluate, forall_const] at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨X , O, in_ress, w_f⟩
      cases O
      · use X, none
        simp_all only [Option.map_none, true_and]
        intro g; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use X, some val, in_ress
        intro g g_in
        simp_all [pairUnload, negUnload, conEval]
        have := w_f (~val.1.unload)
        aesop
    · rintro ⟨X, O, ⟨in_ress, w_Ci⟩⟩
      intro f f_in
      cases O <;> simp at *
      · cases f_in
        · aesop
        subst_eqs
        simp only [evaluate]
        rw [this]
        use X, none
        simp_all only [pairUnload, negUnload, conEval, true_and]
        intro f f_in
        apply w_Ci
        simp_all
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use X, some val, in_ress
          simp only [pairUnload, negUnload, conEval, List.mem_union_iff, List.mem_singleton]
          intro g g_in
          rcases g_in with (_|g_def)
          · apply w_Ci; simp_all
          · subst g_def; apply w_Ci; simp_all
  case loadedR ress χ lrule ress_def =>
    subst ress_def
    -- based on loadedL case
    have := loadRuleTruth lrule W M w
    rw [disEval] at this
    subst hC
    simp at preconditionProof
    subst preconditionProof
    simp at *
    constructor
    · intro hyp
      have hyp' := hyp (~χ.unload)
      simp only [Option.map_some, Sum.elim_inr, negUnload, Option.toList_some, List.mem_union_iff,
        List.mem_cons, List.not_mem_nil, or_false, or_true, evaluate, forall_const] at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨X , O, in_ress, w_f⟩
      cases O
      · use X, none
        simp_all only [Option.map_none, true_and]
        intro g; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use X, some val, in_ress
        intro g g_in
        simp_all [pairUnload, negUnload, conEval]
        have := w_f (~val.1.unload)
        aesop
    · rintro ⟨X, O, ⟨in_ress, w_Ci⟩⟩
      intro f f_in
      cases O <;> simp at *
      · cases f_in
        · aesop
        subst_eqs
        simp only [evaluate]
        rw [this]
        use X, none
        simp_all only [pairUnload, negUnload, conEval, true_and]
        intro f f_in
        apply w_Ci
        simp_all
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use X, some val, in_ress
          simp only [pairUnload, negUnload, conEval, List.mem_union_iff, List.mem_singleton]
          intro g g_in
          rcases g_in with (_|g_def)
          · apply w_Ci; simp_all
          · subst g_def; apply w_Ci; simp_all

/-- If we can apply a local rule to a sequent then it cannot be basic. -/
lemma nonbasic_of_localRuleApp (lra : LocalRuleApp) : ¬ lra.X.basic := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconditionProof⟩
  unfold Sequent.basic
  simp only
  rw [and_iff_not_or_not]
  simp only [not_not]
  cases rule
  case oneSidedL ress orule ress_def =>
    subst_eqs
    cases orule
    case bot => right; simp_all [Sequent.closed]
    case not φ =>
      right; simp_all [Sequent.closed]; right
      have := preconditionProof.subset
      refine ⟨φ, Or.inl ?_, Or.inl ?_⟩ <;> tauto
    case neg φ =>
      left; push_neg; simp_all
      refine ⟨~~φ, Or.inl (by simp_all), by simp⟩
    case con φ1 φ2 =>
      left; push_neg; simp_all
      refine ⟨φ1 ⋀ φ2, Or.inl (by simp_all), by simp⟩
    case nCo φ1 φ2 =>
      left; push_neg; simp_all
      refine ⟨~(φ1 ⋀ φ2), Or.inl (by simp_all), by simp⟩
    case box α φ α_nonAtom =>
      left; push_neg; simp_all
      refine ⟨⌈α⌉φ, Or.inl (by simp_all), ?_⟩
      cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
    case dia α φ α_nonAtom =>
      left; push_neg; simp_all
      refine ⟨~⌈α⌉φ, Or.inl ?_, ?_⟩
      · exact preconditionProof
      · cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
  case oneSidedR ress orule ress_def => -- analogous to oneSidedL
    cases orule
    case bot => right; simp_all [Sequent.closed]
    case not φ =>
      right; simp_all [Sequent.closed]; right
      have := preconditionProof.subset
      refine ⟨φ, Or.inr ?_, Or.inr ?_⟩ <;> tauto
    case neg φ =>
      left; push_neg; simp_all
      refine ⟨~~φ, Or.inr (by simp_all), by simp⟩
    case con φ1 φ2 =>
      left; push_neg; simp_all
      refine ⟨φ1 ⋀ φ2, Or.inr (by simp_all), by simp⟩
    case nCo φ1 φ2 =>
      left; push_neg; simp_all
      refine ⟨~(φ1 ⋀ φ2), Or.inr (by simp_all), by simp⟩
    case box α φ α_nonAtom =>
      left; push_neg; simp_all
      refine ⟨⌈α⌉φ, Or.inr (by simp_all), ?_⟩
      cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
    case dia α φ α_nonAtom =>
      left; push_neg; simp_all
      refine ⟨~⌈α⌉φ, Or.inr (Or.inl ?_), ?_⟩
      · exact preconditionProof
      · cases α <;> simp_all; simp [Program.isAtomic] at α_nonAtom
  case LRnegL =>
    right
    simp [Sequent.closed]
    aesop
  case LRnegR =>
    right
    simp [Sequent.closed]
    aesop
  case loadedL ress χ lrule ress_def =>
    left
    push_neg
    cases lrule
    case dia α χ α_nonAtom =>
      rcases O with _|⟨⟨α',χ'⟩|⟨α',χ'⟩⟩
      · simp_all
      · simp_all
        refine ⟨~(~'⌊α'⌋χ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ χ = χ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
          simp [Program.isAtomic] at α_nonAtom
      · refine ⟨~(~'⌊α'⌋χ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ χ = χ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
    case dia' α φ α_nonAtom =>
      rcases O with _|⟨⟨α',φ'⟩|⟨α',φ'⟩⟩
      · simp_all
      · refine ⟨~(~'⌊α'⌋φ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ φ = φ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
          simp [Program.isAtomic] at α_nonAtom
      · refine ⟨~(~'⌊α'⌋φ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ φ = φ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
  case loadedR ress χ lrule ress_def => -- analogous to loadedL
    left
    push_neg
    cases lrule
    case dia α χ α_nonAtom =>
      rcases O with _|⟨⟨α',χ'⟩|⟨α',χ'⟩⟩
      · simp_all
      · refine ⟨~(~'⌊α'⌋χ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ χ = χ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
      · refine ⟨~(~'⌊α'⌋χ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ χ = χ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
          simp [Program.isAtomic] at α_nonAtom
    case dia' α φ α_nonAtom =>
      rcases O with _|⟨⟨α',φ'⟩|⟨α',φ'⟩⟩
      · simp_all
      · refine ⟨~(~'⌊α'⌋φ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ φ = φ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
      · refine ⟨~(~'⌊α'⌋φ').1.unload, by aesop, ?_⟩
        · have ⟨h1,h2⟩ : α = α' ∧ φ = φ' := by simp_all
          subst h1 h2
          cases α <;> simp_all
          simp [Program.isAtomic] at α_nonAtom

/-- For a given non-basic formula in the left list `L`,
construct a `LocalRuleApp` using an appropriate `OneSidedLocalRule`. -/
def localRuleApp_of_nonbasic_in_L (L R : List Formula) (O : Olf) (f : Formula)
    (f_in : f ∈ L) (f_nonBas : f.basic = false)
    : { lra : LocalRuleApp // lra.X = (L, R, O) } :=
match f with
  | .bottom => ⟨{ L, R, O, Lcond := [⊥], ress := []
                  lr := .oneSidedL .bot rfl
                  preconditionProof :=
                    ⟨by rwa [List.singleton_subperm_iff], List.nil_subperm, by simp⟩ }, rfl⟩
  | ·n => by simp [Formula.basic] at f_nonBas
  | .neg f' => match f' with
    | .bottom => by simp [Formula.basic] at f_nonBas
    | .atom_prop n => by simp [Formula.basic] at f_nonBas
    | .neg φ => ⟨{L, R, O, Lcond := [~~φ], ress := [([φ], [], none)]
                  lr := .oneSidedL (.neg φ) rfl
                  preconditionProof :=
                    ⟨by rwa [List.singleton_subperm_iff], List.nil_subperm, by simp⟩ }, rfl⟩
    | .and φ ψ => ⟨{L, R, O, Lcond := [~(φ⋀ψ)]
                    ress := [([~φ], [], none), ([~ψ], [], none)]
                    lr := .oneSidedL (.nCo φ ψ) rfl
                    preconditionProof :=
                      ⟨by rwa [List.singleton_subperm_iff], List.nil_subperm, by simp⟩ }, rfl⟩
    | .box α φ =>
        have hna : ¬ α.isAtomic := by cases α <;> simp_all [Formula.basic, Program.isAtomic]
        ⟨{L, R, O, Lcond := [~⌈α⌉φ]
          ress := (unfoldDiamond α φ).map (fun res => (res, [], none))
          lr := .oneSidedL (.dia α φ hna) rfl
          preconditionProof :=
            ⟨by rwa [List.singleton_subperm_iff], List.nil_subperm, by simp⟩ }, rfl⟩
  | .and φ ψ => ⟨{L, R, O, Lcond := [φ⋀ψ], ress := [([φ,ψ], [], none)]
                  lr := .oneSidedL (.con φ ψ) rfl
                  preconditionProof :=
                    ⟨by rwa [List.singleton_subperm_iff], List.nil_subperm, by simp⟩ }, rfl⟩
  | .box α φ =>
      have hna : ¬ α.isAtomic := by cases α <;> simp_all [Formula.basic, Program.isAtomic]
      ⟨{L, R, O, Lcond := [⌈α⌉φ]
        ress := (unfoldBox α φ).map (fun res => (res, [], none))
        lr := .oneSidedL (.box α φ hna) rfl
        preconditionProof :=
          ⟨by rwa [List.singleton_subperm_iff], List.nil_subperm, by simp⟩ }, rfl⟩

/-- For a given non-basic formula in the right list `R`,
construct a `LocalRuleApp` using an appropriate `OneSidedLocalRule`. -/
def localRuleApp_of_nonbasic_in_R (L R : List Formula) (O : Olf) (f : Formula)
    (f_in : f ∈ R) (f_nonBas : f.basic = false)
    : { lra : LocalRuleApp // lra.X = (L, R, O) } :=
  match f with
  | .bottom => ⟨{ L, R, O, Rcond := [⊥], ress := []
                  lr := .oneSidedR .bot rfl
                  preconditionProof :=
                    ⟨List.nil_subperm, by rwa [List.singleton_subperm_iff], by simp⟩ }, rfl⟩
  | .atom_prop n => by simp [Formula.basic] at f_nonBas
  | .neg f' => match f' with
    | .bottom => by simp [Formula.basic] at f_nonBas
    | .atom_prop n => by simp [Formula.basic] at f_nonBas
    | .neg φ =>
            ⟨{L, R, O, Rcond := [~~φ], ress := [([], [φ], none)]
              lr := .oneSidedR (.neg φ) rfl
              preconditionProof :=
                ⟨List.nil_subperm, by rwa [List.singleton_subperm_iff], by simp⟩ }, rfl⟩
    | .and φ ψ =>
            ⟨{L, R, O, Rcond := [~(φ⋀ψ)]
              ress := [([], [~φ], none), ([], [~ψ], none)]
              lr := .oneSidedR (.nCo φ ψ) rfl
              preconditionProof :=
                ⟨List.nil_subperm, by rwa [List.singleton_subperm_iff], by simp⟩ }, rfl⟩
    | .box α φ =>
          have hna : ¬ α.isAtomic := by
            cases α <;> simp_all [Formula.basic, Program.isAtomic]
          ⟨{L, R, O, Rcond := [~⌈α⌉φ]
            ress := (unfoldDiamond α φ).map (fun res => ([], res, none))
            lr := .oneSidedR (.dia α φ hna) rfl
            preconditionProof :=
              ⟨List.nil_subperm, by rwa [List.singleton_subperm_iff], by simp⟩ }, rfl⟩
  | .and φ ψ => ⟨{L, R, O, Rcond := [φ⋀ψ], ress := [([], [φ,ψ], none)]
                  lr := .oneSidedR (.con φ ψ) rfl
                  preconditionProof :=
                    ⟨List.nil_subperm, by rwa [List.singleton_subperm_iff], by simp⟩ }, rfl⟩
  | .box α φ =>
    have hna : ¬ α.isAtomic := by cases α <;> simp_all [Formula.basic, Program.isAtomic]
    ⟨{L, R, O, Rcond := [⌈α⌉φ]
      ress := (unfoldBox α φ).map (fun res => ([], res, none))
      lr := .oneSidedR (.box α φ hna) rfl
      preconditionProof :=
        ⟨List.nil_subperm, by rwa [List.singleton_subperm_iff], by simp⟩ }, rfl⟩

/-- A sequent is basic iff no local rule can be applied.
Note that in the paper (L+) and (L-) are also local rules and had to be excluded
here, but here in the Lean formalization they are `PdlRule`s anyway. -/
lemma basic_iff_noLocalRuleApp {Y : Sequent} :
    Y.basic ↔ ¬ ∃ (lra : LocalRuleApp),lra.X = Y := by
  constructor
  · have := nonbasic_of_localRuleApp
    grind
  · intro no_lra
    by_contra Y_nonbas
    unfold Sequent.basic at Y_nonbas
    have not_closed : ¬ Sequent.closed Y := by
      clear Y_nonbas
      intro Y_closed
      absurd no_lra
      rcases Y_closed with bot_in_Y | f_not_f_in_Y
      · rcases Y with ⟨L,R,O⟩
        simp at *
        cases bot_in_Y
        · exact ⟨⟨L,R,O, [⊥],[],none, [], .oneSidedL .bot rfl, [], rfl, by simp_all⟩, by simp⟩
        · exact ⟨⟨L,R,O, [],[⊥],none, [], .oneSidedR .bot rfl, [], rfl, by simp_all⟩, by simp⟩
      · rcases f_not_f_in_Y with ⟨φ, φ_in, not_φ_in⟩
        rcases Y with ⟨L,R,O⟩
        simp at *
        cases φ_in <;> cases not_φ_in
        · refine ⟨⟨L,R,O, [φ, ~φ], [], none, [], .oneSidedL (.not _) rfl, [], rfl, ?_⟩, by simp⟩
          exact ⟨ List.cons_subperm_of_not_mem_of_mem
                  (by simp [φ.neq_neg_self]) ‹_›
                  (by rw [List.singleton_subperm_iff]; exact ‹_›),
                  List.nil_subperm, by simp ⟩
        · exact ⟨⟨L,R,O, [φ], [~φ], none, [], LocalRule.LRnegL φ, [], rfl, by simp_all⟩, by simp⟩
        · exact ⟨⟨L,R,O, [~φ], [φ], none, [], LocalRule.LRnegR φ, [], rfl, by simp_all⟩, by simp⟩
        · refine ⟨⟨L,R,O, [], [φ, ~φ], none, [], .oneSidedR (.not _) rfl, [], rfl, ?_⟩, by simp⟩
          exact ⟨ List.nil_subperm,
                  List.cons_subperm_of_not_mem_of_mem
                  (by simp; exact φ.neq_neg_self) ‹_›
                  (by rw [List.singleton_subperm_iff]; exact ‹_›),
                  by simp ⟩
    rcases Y with ⟨L,R,O⟩
    simp_all
    clear not_closed
    absurd no_lra
    push_neg
    -- Y_nonbas: ∃ formula in L ∪ R ∪ O that's not basic
    rcases Y_nonbas with ⟨f, f_where, f_nonBas⟩
    rcases f_where with f_in_L | f_in_R | ⟨a, rfl, rfl⟩ | ⟨b, rfl, rfl⟩
    · exact Subtype.exists_of_subtype <| localRuleApp_of_nonbasic_in_L L R O f f_in_L f_nonBas
    · exact Subtype.exists_of_subtype <| localRuleApp_of_nonbasic_in_R L R O f f_in_R f_nonBas
    · -- O = some (Sum.inl a), formula is ~a.1.unload, not basic
      -- a : NegLoadFormula, a = ~'χ where χ : LoadFormula = ⌊α⌋af
      rcases a with ⟨⟨α, af⟩⟩
      cases af with
      | normal φ =>
        -- formula is ~⌈α⌉φ, not basic means α is not atomic
        have hna : ¬ α.isAtomic := by
          cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inl (~'⌊α⌋(AnyFormula.normal φ)))
                 Ocond := some (Sum.inl (~'⌊α⌋(AnyFormula.normal φ)))
                 ress := (unfoldDiamondLoaded' α φ).map
                   (fun (X, o) => (X, [], o.map Sum.inl))
                 lr := .loadedL _ (.dia' hna) rfl
                 preconditionProof := ⟨List.nil_subperm, List.nil_subperm, by simp⟩ }, rfl⟩
      | loaded χ =>
        have hna : ¬ α.isAtomic := by
          cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inl (~'⌊α⌋(AnyFormula.loaded χ)))
                 Ocond := some (Sum.inl (~'⌊α⌋(AnyFormula.loaded χ)))
                 ress := (unfoldDiamondLoaded α χ).map
                   (fun (X, o) => (X, [], o.map Sum.inl))
                 lr := .loadedL _ (.dia hna) rfl
                 preconditionProof := ⟨List.nil_subperm, List.nil_subperm, by simp⟩ }, rfl⟩
    · -- O = some (Sum.inr b), symmetric to inl case
      rcases b with ⟨⟨α, af⟩⟩
      cases af with
      | normal φ =>
        have hna : ¬ α.isAtomic := by cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inr (~'⌊α⌋(AnyFormula.normal φ)))
                 Ocond := some (Sum.inr (~'⌊α⌋(AnyFormula.normal φ)))
                 ress := (unfoldDiamondLoaded' α φ).map
                   (fun (X, o) => ([], X, o.map Sum.inr))
                 lr := .loadedR _ (.dia' hna) rfl
                 preconditionProof := ⟨List.nil_subperm, List.nil_subperm, by simp⟩ }, rfl⟩
      | loaded χ =>
        have hna : ¬ α.isAtomic := by cases α <;> simp_all [LoadFormula.unload, Program.isAtomic]
        exact ⟨{ L, R, O := some (Sum.inr (~'⌊α⌋(AnyFormula.loaded χ)))
                 Ocond := some (Sum.inr (~'⌊α⌋(AnyFormula.loaded χ)))
                 ress := (unfoldDiamondLoaded α χ).map
                   (fun (X, o) => ([], X, o.map Sum.inr))
                 lr := .loadedR _ (.dia hna) rfl
                 preconditionProof := ⟨List.nil_subperm, List.nil_subperm, by simp⟩ }, rfl⟩

/-! ## Local rule applications preserve atomic formulas -/

lemma LocalRuleApp.preserve_bottom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ⊥ ∈ lra.X.bothSides → ⊥ ∈ Y.bothSides := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all [applyLocalRule, Sequent.bothSides, Sequent.left, Sequent.right]
  case oneSidedL ress orule ress_def => cases orule <;> simp_all <;> grind
  case oneSidedR ress orule ress_def => cases orule <;> simp_all <;> grind
  case loadedL ress chi lrule ress_def => cases lrule <;> simp_all <;>
    intros <;> subst_eqs <;> simp_all <;> grind
  case loadedR ress chi lrule ress_def => cases lrule <;> simp_all <;>
    intros <;> subst_eqs <;> simp_all <;> grind

lemma LocalRuleApp.preserve_atom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ p : Nat,
      Formula.atom_prop p ∈ lra.X.bothSides → Formula.atom_prop p ∈ Y.bothSides := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all [applyLocalRule, Sequent.bothSides, Sequent.left, Sequent.right]
  case oneSidedL ress orule ress_def => cases orule <;> simp_all <;> grind
  case oneSidedR ress orule ress_def => cases orule <;> simp_all <;> grind
  case loadedL ress chi lrule ress_def =>
    cases lrule <;> simp_all <;> intros <;> subst_eqs <;> simp_all <;> grind
  case loadedR ress chi lrule ress_def =>
    cases lrule <;> simp_all <;> intros <;> subst_eqs <;> simp_all <;> grind

lemma LocalRuleApp.preserve_neg_atom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ p : Nat,
      (~(Formula.atom_prop p)) ∈ lra.X.bothSides → (~(Formula.atom_prop p)) ∈ Y.bothSides := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all [applyLocalRule, Sequent.bothSides, Sequent.left, Sequent.right]
  case oneSidedL ress orule ress_def => cases orule <;> simp_all <;> grind
  case oneSidedR ress orule ress_def => cases orule <;> simp_all <;> grind
  case loadedL ress chi lrule ress_def =>
    cases lrule <;> simp_all <;> intros <;> subst_eqs <;> simp_all <;> grind
  case loadedR ress chi lrule ress_def =>
    cases lrule <;> simp_all <;> intros <;> subst_eqs <;> simp_all <;> grind

lemma LocalRuleApp.preserve_local_atom_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ f,
      (f = ⊥ ∨ ∃ p : Nat, f = (Formula.atom_prop p) ∨ f = (~(Formula.atom_prop p))) →
      f ∈ lra.X.bothSides → f ∈ Y.bothSides := by
  rintro Y Y_in f (rfl | ⟨p, rfl | rfl⟩) f_in
  · exact lra.preserve_bottom_down Y Y_in f_in
  · exact lra.preserve_atom_down Y Y_in p f_in
  · exact lra.preserve_neg_atom_down Y Y_in p f_in

lemma mem_child_left_of_pairUnload_mem {w : List Formula} {o : Option NegLoadFormula}
    {f : Formula} (h : f ∈ pairUnload (w, o)) :
    f ∈ w ∨ f ∈ Olf.L (o.map Sum.inl) := by
  cases o <;> simp_all [pairUnload]

lemma mem_child_right_of_pairUnload_mem {w : List Formula} {o : Option NegLoadFormula}
    {f : Formula} (h : f ∈ pairUnload (w, o)) :
    f ∈ w ∨ f ∈ Olf.R (o.map Sum.inr) := by
  cases o <;> simp_all [pairUnload]

lemma loaded_unfold_child_closes_left {α : Program} {χ : LoadFormula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded α χ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ χ.unload,
      f ∈ w ∨ f ∈ Olf.L (o.map Sum.inl) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α χ.unload := by
    rw [← unfoldDiamondLoaded_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_left_of_pairUnload_mem (heq ▸ hf)⟩

lemma loaded_unfold'_child_closes_left {α : Program} {φ : Formula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded' α φ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ φ,
      f ∈ w ∨ f ∈ Olf.L (o.map Sum.inl) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α φ := by
    rw [← unfoldDiamondLoaded'_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_left_of_pairUnload_mem (heq ▸ hf)⟩

lemma loaded_unfold_child_closes_right {α : Program} {χ : LoadFormula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded α χ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ χ.unload,
      f ∈ w ∨ f ∈ Olf.R (o.map Sum.inr) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α χ.unload := by
    rw [← unfoldDiamondLoaded_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_right_of_pairUnload_mem (heq ▸ hf)⟩

lemma loaded_unfold'_child_closes_right {α : Program} {φ : Formula}
    {w : List Formula} {o : Option NegLoadFormula}
    (h : (w, o) ∈ unfoldDiamondLoaded' α φ) :
    ∃ Fδ ∈ Dset α, ∀ f ∈ Yset Fδ φ,
      f ∈ w ∨ f ∈ Olf.R (o.map Sum.inr) := by
  have hm : pairUnload (w, o) ∈ unfoldDiamond α φ := by
    rw [← unfoldDiamondLoaded'_eq]
    exact List.mem_map_of_mem h
  simp only [unfoldDiamond, List.mem_map] at hm
  rcases hm with ⟨Fδ, Fδ_in, heq⟩
  exact ⟨Fδ, Fδ_in, fun f hf => mem_child_right_of_pairUnload_mem (heq ▸ hf)⟩

-- TODO golf/shorten this
set_option maxHeartbeats 4000000 in
-- lots of simp_al and aesop use, made by aristotle.harmonic.fun
/-- Every formula at the source of a local rule is either retained by a chosen child or is the
principal formula and has the closure data required for saturatedness in that child. -/
lemma LocalRuleApp.formula_preserved_or_expanded (lra : LocalRuleApp) {Y : Sequent}
    (hY : Y ∈ lra.C) : ∀ f ∈ lra.X.bothSides,
      f ∈ Y.bothSides ∨
        (∀ (φ ψ : Formula) (α : Program),
          (f = (~~φ) → φ ∈ Y.bothSides) ∧
          (f = (φ⋀ψ) → φ ∈ Y.bothSides ∧ ψ ∈ Y.bothSides) ∧
          (f = (~(φ⋀ψ)) → (~φ) ∈ Y.bothSides ∨ (~ψ) ∈ Y.bothSides) ∧
          (f = (⌈α⌉φ) → ∃ l : TP α, (Bset α l φ).all (· ∈ Y.bothSides)) ∧
          (f = (~⌈α⌉φ) → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (· ∈ Y.bothSides))) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst C
  cases rule
  case oneSidedL orule YS_def =>
    cases orule
    case neg φ =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ~~φ
      · subst f; right; simp
      · left
        rcases hf with hf | hf | hf | hf
        · have := (List.mem_erase_of_ne hp).2 hf; aesop
        all_goals aesop
    case con φ ψ =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = φ⋀ψ
      · subst f; right; simp
      · left
        rcases hf with hf | hf | hf | hf
        · have := (List.mem_erase_of_ne hp).2 hf; aesop
        all_goals aesop
    case nCo φ ψ =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ~(φ⋀ψ)
      · subst f
        right
        intro φ' ψ' _
        rcases hY with hY | hY <;> subst Y <;>
          simp <;> aesop
      · left
        rcases hf with hf | hf | hf | hf
        · have := (List.mem_erase_of_ne hp).2 hf; aesop
        all_goals aesop
    case box α φ notAtom =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ⌈α⌉φ
      · subst f
        right
        intro φ' ψ' α'
        refine ⟨by simp, by simp, by simp, ?_, by simp⟩
        intro heq
        injection heq with hα hφ
        subst α'; subst φ'
        simp only [unfoldBox, List.mem_map] at hY
        rcases hY with ⟨l, l_in, hY⟩
        rcases l_in with ⟨tp, tp_in, rfl⟩
        subst Y
        refine ⟨tp, ?_⟩
        intro x hx
        simp [hx]
      · left
        rcases hf with hf | hf | hf | hf
        · have := (List.mem_erase_of_ne hp).2 hf; aesop
        all_goals aesop
    case dia α φ notAtom =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ~⌈α⌉φ
      · subst f
        right
        intro φ' ψ' α'
        refine ⟨by simp, by simp, by simp, by simp, ?_⟩
        intro heq
        injection heq with hneg
        injection hneg with hα hφ
        subst α'; subst φ'
        simp only [unfoldDiamond, List.mem_map] at hY
        rcases hY with ⟨ys, ys_in, hY⟩
        rcases ys_in with ⟨Fδ, Fδ_in, rfl⟩
        subst Y
        rcases Fδ with ⟨Fs, δ⟩
        refine ⟨Fs, δ, Fδ_in, ?_⟩
        intro x hx
        simp [hx]
      · left
        rcases hf with hf | hf | hf | hf
        · have := (List.mem_erase_of_ne hp).2 hf; aesop
        all_goals aesop
    all_goals simp_all [applyLocalRule]
  case oneSidedR orule YS_def =>
    cases orule <;> simp_all [applyLocalRule, Sequent.bothSides]
    all_goals intro f hf
    case neg φ => by_cases hp : f = ~~φ <;> simp_all [List.mem_erase_of_ne]; aesop
    case con φ ψ => by_cases hp : f = φ⋀ψ <;> simp_all [List.mem_erase_of_ne]; aesop
    case nCo φ ψ => by_cases hp : f = ~(φ⋀ψ) <;> simp_all <;> aesop
    case box α φ notAtom => by_cases hp : f = ⌈α⌉φ <;> simp_all [unfoldBox] <;> aesop
    case dia α φ notAtom => by_cases hp : f = ~⌈α⌉φ <;> simp_all [unfoldDiamond] <;> aesop
  case loadedL χ lrule YS_def =>
    cases lrule
    case dia α χ notAtom =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ~⌈α⌉χ.unload
      · subst f
        right
        intro φ ψ β
        refine ⟨by simp, by simp, by simp, by simp, ?_⟩
        intro heq
        injection heq with hn
        injection hn with hα hφ
        subst β; subst φ
        rcases hY with ⟨w, o, hwo, rfl⟩
        rcases loaded_unfold_child_closes_left hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
        exact ⟨Fs, δ, hD, by aesop⟩
      · left; aesop
    case dia' α φ notAtom =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ~⌈α⌉φ
      · subst f
        right
        intro φ' ψ β
        refine ⟨by simp, by simp, by simp, by simp, ?_⟩
        intro heq
        injection heq with hn
        injection hn with hα hφ
        subst β; subst φ'
        rcases hY with ⟨w, o, hwo, rfl⟩
        rcases loaded_unfold'_child_closes_left hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
        exact ⟨Fs, δ, hD, by aesop⟩
      · left; aesop
  case loadedR χ lrule YS_def =>
    cases lrule
    case dia α χ notAtom =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ~⌈α⌉χ.unload
      · subst f
        right
        intro φ ψ β
        refine ⟨by simp, by simp, by simp, by simp, ?_⟩
        intro heq
        injection heq with hn
        injection hn with hα hφ
        subst β; subst φ
        rcases hY with ⟨w, o, hwo, rfl⟩
        rcases loaded_unfold_child_closes_right hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
        exact ⟨Fs, δ, hD, by aesop⟩
      · left; aesop
    case dia' α φ notAtom =>
      simp_all [applyLocalRule, Sequent.bothSides]
      intro f hf
      by_cases hp : f = ~⌈α⌉φ
      · subst f
        right
        intro φ' ψ β
        refine ⟨by simp, by simp, by simp, by simp, ?_⟩
        intro heq
        injection heq with hn
        injection hn with hα hφ
        subst β; subst φ'
        rcases hY with ⟨w, o, hwo, rfl⟩
        rcases loaded_unfold'_child_closes_right hwo with ⟨⟨Fs,δ⟩, hD, hclose⟩
        exact ⟨Fs, δ, hD, by aesop⟩
      · left; aesop
  all_goals simp_all [applyLocalRule]

/-! # Saturated and Locally Consistent Sets of Formulas -/

/-- A set of formulas is *saturated* if it is closed under:
removing double negations, splitting (negated) conjunctions,
unfolding boxes using any test profile, and unfolding diamonds using `H`.
Part of Def 6.2 -/
def saturated : Finset Formula → Prop
  | X => ∀ (φ ψ : Formula) (α : Program),
    -- propositional closure:
      ((~~φ) ∈ X → φ ∈ X)
    ∧ (φ⋀ψ ∈ X → φ ∈ X ∧ ψ ∈ X)
    ∧ ((~(φ⋀ψ)) ∈ X → (~φ) ∈ X ∨ (~ψ) ∈ X)
    -- programs closure, now only two general cases, no program subcases:
    ∧ ((⌈α⌉φ) ∈ X → ∃ l : TP α, (Bset α l φ).all (fun y => y ∈ X))
    ∧ ((~⌈α⌉φ) ∈ X → ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (fun y => y ∈ X))

/-- Any basic sequent is also saturated. -/
lemma Sequent.basic_then_saturated {X : Sequent} : X.basic → saturated X.toFinset := by
  intro Xbas
  rcases X with ⟨L,R,O⟩
  unfold saturated
  intro Fs φ ψ α
  refine ⟨?_, ?_, ?_, ?box, ?dia⟩
  · simp_all [basic, Fs, toFinset]
    grind
  · simp_all [basic, Fs, toFinset]
    grind
  · simp_all [basic, Fs, toFinset]
    grind
  case box =>
    intro _in_F
    simp_all [basic, Fs, toFinset]
    cases α
    case atom_prog =>
      simp [TP, testsOfProgram,Bset,P,F]
      exact _in_F
    all_goals
      simp [TP, testsOfProgram,Bset,P,F]
      grind
  case dia =>
    intro _in_F
    simp_all [basic, Fs, toFinset]
    cases α
    case atom_prog =>
      simp [Dset,Yset]
      exact _in_F
    all_goals
      simp [Dset,Yset]
      grind

/-- A set of formulas is *lcoally consistent* iff it does not contain `⊥`
and for all atoms `p ∈ X` we do not have `~p ∈ X`. Part of Def 6.2 -/
def locallyConsistent (X : Finset Formula) : Prop :=
  ⊥ ∉ X.val ∧ ∀ pp, (·pp : Formula) ∈ X.val → (~(·pp)) ∉ X.val

lemma Sequent.basic_to_locallyConsistent {X : Sequent} (bas : X.basic) :
    locallyConsistent X.toFinset := by
  rcases X with ⟨L, R, O⟩
  unfold locallyConsistent Sequent.toFinset at *
  constructor
  · intro hbot
    apply bas.2
    unfold Sequent.closed
    left
    simp_all
  · intro p hp hnp
    apply bas.2
    unfold Sequent.closed
    right
    refine ⟨(·p), ?_, ?_⟩
    · simp_all
    · simp_all
      rcases hnp with h | h | ⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩
      · exact Or.inl h
      · exact Or.inr h
      · rcases a with ⟨⟨α, af⟩⟩
        cases af <;> simp [LoadFormula.unload] at ha
      · rcases b with ⟨⟨α, af⟩⟩
        cases af <;> simp [LoadFormula.unload] at hb

-- TODO golf/shorten this
/-- LocalRuleApp preserves saturatedness backwards. -/
lemma LocalRuleApp.preserve_saturated_up (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ (rest : List Sequent) ,
      Y ∈ rest →
      saturated (rest.map Sequent.bothSides).flatten.toFinset
        → saturated (((lra.X :: rest).map Sequent.bothSides).flatten.toFinset) := by
  intro Y hY rest hYr hs
  simp only [saturated] at hs ⊢
  intro φ ψ α
  have old_or_rest (f : Formula) :
      f ∈ ((lra.X :: rest).map Sequent.bothSides).flatten.toFinset →
      f ∈ lra.X.bothSides ∨ f ∈ (rest.map Sequent.bothSides).flatten.toFinset := by
    simp only [List.map_cons, List.flatten_cons, List.mem_toFinset, List.mem_append]
    exact id
  have child_in_rest (f : Formula) (hf : f ∈ Y.bothSides) :
      f ∈ (rest.map Sequent.bothSides).flatten.toFinset := by
    simp only [List.mem_toFinset, List.mem_flatten, List.mem_map]
    exact ⟨Y.bothSides, ⟨Y, hYr, rfl⟩, hf⟩
  have lift_rest (f : Formula) :
      f ∈ (rest.map Sequent.bothSides).flatten.toFinset →
      f ∈ ((lra.X :: rest).map Sequent.bothSides).flatten.toFinset := by simp_all
  have source_closure := lra.formula_preserved_or_expanded hY
  rcases hs φ ψ α with ⟨hneg, hcon, hncon, hbox, hdia⟩
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · exact lift_rest _ (hneg (child_in_rest _ hkeep))
      · exact lift_rest _ (child_in_rest _ ((hexpand φ ψ α).1 rfl))
    · exact lift_rest _ (hneg hrest)
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hcon (child_in_rest _ hkeep) with ⟨hφ, hψ⟩
        exact ⟨lift_rest _ hφ, lift_rest _ hψ⟩
      · rcases (hexpand φ ψ α).2.1 rfl with ⟨hφ, hψ⟩
        exact ⟨lift_rest _ (child_in_rest _ hφ), lift_rest _ (child_in_rest _ hψ)⟩
    · rcases hcon hrest with ⟨hφ, hψ⟩
      exact ⟨lift_rest _ hφ, lift_rest _ hψ⟩
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · exact (hncon (child_in_rest _ hkeep)).imp (lift_rest _) (lift_rest _)
      · rcases (hexpand φ ψ α).2.2.1 rfl with hφ | hψ
        · exact Or.inl (lift_rest _ (child_in_rest _ hφ))
        · exact Or.inr (lift_rest _ (child_in_rest _ hψ))
    · exact (hncon hrest).imp (lift_rest _) (lift_rest _)
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hbox (child_in_rest _ hkeep) with ⟨l, hl⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hl
        exact ⟨l, by simpa using fun f hf => lift_rest _ (by simpa using hl f hf)⟩
      · rcases (hexpand φ ψ α).2.2.2.1 rfl with ⟨l, hl⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hl
        exact ⟨l, by simpa using fun f hf => lift_rest _ (child_in_rest _ (by simpa using hl f hf))⟩
    · rcases hbox hrest with ⟨l, hl⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hl
      exact ⟨l, by simpa using fun f hf => lift_rest _ (by simpa using hl f hf)⟩
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hdia (child_in_rest _ hkeep) with ⟨Fδ, hD, hF⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hF
        exact ⟨Fδ, hD, by simpa using fun f hf => lift_rest _ (by simpa using hF f hf)⟩
      · rcases (hexpand φ ψ α).2.2.2.2 rfl with ⟨Fδ, hD, hF⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hF
        exact ⟨ Fδ, hD
              , by simpa using fun f hf => lift_rest _ (child_in_rest _ (by simpa using hF f hf))⟩
    · rcases hdia hrest with ⟨Fδ, hD, hF⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hF
      exact ⟨Fδ, hD, by simpa using fun f hf => lift_rest _ (by simpa using hF f hf)⟩

/-- A free diamond at the source of a local rule application is either kept in the chosen child,
or it is the principal formula, and then the child contains one of its unfoldings.
Analogous to `LocalRuleApp.formula_preserved_or_expanded`, but for `Sequent.wForms`, i.e. here
we also know that the formulas in the child occur *unloaded*. (This is why we cannot obtain this
lemma from `LocalRuleApp.formula_preserved_or_expanded`: the latter uses `Sequent.bothSides`,
where a formula may also come from *unloading* the loaded formula of a sequent.) -/
lemma LocalRuleApp.wForms_negBox_preserved_or_unfolded (lra : LocalRuleApp) {Y : Sequent}
    (hY : Y ∈ lra.C) {α φ} (h : (~⌈α⌉φ : WhateverFormula) ∈ lra.X.wForms) :
    ((~⌈α⌉φ : WhateverFormula) ∈ Y.wForms)
    ∨ ∃ Fδ ∈ Dset α, (Yset Fδ φ).all (fun f => (f : WhateverFormula) ∈ Y.wForms) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  simp only [LocalRuleApp.X] at h
  rw [Sequent.mem_wForms_normal_iff] at h
  simp only [applyLocalRule, List.mem_map] at hY
  rcases hY with ⟨⟨Lnew, Rnew, Onew⟩, res_in, rfl⟩
  by_cases hcond : (~⌈α⌉φ) ∈ Lcond ∨ (~⌈α⌉φ) ∈ Rcond
  · -- The diamond is the principal formula, so the only possible rule is its unfolding.
    right
    cases rule with
    | oneSidedL orule ress_def =>
      cases orule <;> simp_all
      rcases res_in with ⟨a, a_in, ha⟩
      simp only [unfoldDiamond, List.mem_map] at a_in
      rcases a_in with ⟨⟨F, δ⟩, Fδ_in, rfl⟩
      cases ha
      exact ⟨F, δ, Fδ_in, fun x hx => Sequent.mem_wForms_normal_iff.mpr
        (Or.inl (List.mem_append.mpr (Or.inr hx)))⟩
    | oneSidedR orule ress_def =>
      cases orule <;> simp_all
      rcases res_in with ⟨a, a_in, ha⟩
      simp only [unfoldDiamond, List.mem_map] at a_in
      rcases a_in with ⟨⟨F, δ⟩, Fδ_in, rfl⟩
      cases ha
      exact ⟨F, δ, Fδ_in, fun x hx => Sequent.mem_wForms_normal_iff.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hx)))⟩
    | _ => simp_all
  · -- The diamond is not the principal formula, so it is kept in the chosen child.
    left
    push_neg at hcond
    rw [Sequent.mem_wForms_normal_iff]
    rcases h with hL | hR
    · exact Or.inl (List.mem_append.mpr (Or.inl (List.mem_diff_of_mem hL hcond.1)))
    · exact Or.inr (List.mem_append.mpr (Or.inl (List.mem_diff_of_mem hR hcond.2)))

/-- A loaded diamond at the source of a local rule application is either kept in the chosen child,
or it is the principal formula, and then the child contains one of the results of the `LoadRule`
that was applied to it.
This is the loaded analogue of `LocalRuleApp.wForms_negBox_preserved_or_unfolded`. -/
lemma LocalRuleApp.wForms_negLoad_preserved_or_unfolded (lra : LocalRuleApp) {Y : Sequent}
    (hY : Y ∈ lra.C) {nlf : NegLoadFormula}
    (h : (WhateverFormula.negLoad nlf) ∈ lra.X.wForms) :
    ((WhateverFormula.negLoad nlf) ∈ Y.wForms)
    ∨ ∃ ress, Nonempty (LoadRule nlf ress) ∧ ∃ Fo ∈ ress,
        Fo.1.all (fun f => (f : WhateverFormula) ∈ Y.wForms)
        ∧ Fo.2.toList.all (fun nl => (WhateverFormula.negLoad nl) ∈ Y.wForms) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  simp only [LocalRuleApp.X] at h
  rw [Sequent.mem_wForms_negLoad_iff] at h
  cases rule
  case oneSidedL ress' orule ress_def | oneSidedR ress' orule ress_def =>
    -- One-sided rules do not change the loaded formula, so it is kept.
    subst ress_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hY
    rcases hY with ⟨res, res_in, rfl⟩
    left
    rw [Sequent.mem_wForms_negLoad_iff]
    simpa using h
  case LRnegL ψ => simp at hY
  case LRnegR ψ => simp at hY
  case loadedL ress' χ lrule ress_def =>
    subst ress_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hY
    rcases hY with ⟨⟨Xnew, onew⟩, res_in, rfl⟩
    right
    have nlf_def : nlf = ~'χ := by
      rcases pre with ⟨_, _, hO⟩
      rcases h with hO' | hO' <;> rw [hO'] at hO <;> simp_all
    subst nlf_def
    refine ⟨ress', ⟨lrule⟩, ⟨Xnew, onew⟩, res_in, ?_, ?_⟩
    · simp only [List.all_eq_true, decide_eq_true_eq]
      intro f f_in
      rw [Sequent.mem_wForms_normal_iff]
      exact Or.inl (List.mem_append.mpr (Or.inr f_in))
    · cases onew with
      | none => simp
      | some nl =>
        simp only [Option.toList_some, List.all_cons, List.all_nil, Bool.and_true,
          decide_eq_true_eq]
        rw [Sequent.mem_wForms_negLoad_iff]
        simp
  case loadedR ress' χ lrule ress_def =>
    subst ress_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hY
    rcases hY with ⟨⟨Xnew, onew⟩, res_in, rfl⟩
    right
    have nlf_def : nlf = ~'χ := by
      rcases pre with ⟨_, _, hO⟩
      rcases h with hO' | hO' <;> rw [hO'] at hO <;> simp_all
    subst nlf_def
    refine ⟨ress', ⟨lrule⟩, ⟨Xnew, onew⟩, res_in, ?_, ?_⟩
    · simp only [List.all_eq_true, decide_eq_true_eq]
      intro f f_in
      rw [Sequent.mem_wForms_normal_iff]
      exact Or.inr (List.mem_append.mpr (Or.inr f_in))
    · cases onew with
      | none => simp
      | some nl =>
        simp only [Option.toList_some, List.all_cons, List.all_nil, Bool.and_true,
          decide_eq_true_eq]
        rw [Sequent.mem_wForms_negLoad_iff]
        simp

/-- The only `LoadRule` applicable to `~'⌊α⌋χ` for a loaded `χ` is `LoadRule.dia`. -/
lemma LoadRule.eq_unfoldDiamondLoaded {α} {χ : LoadFormula} {ress}
    (lr : LoadRule (~'⌊α⌋(AnyFormula.loaded χ)) ress) : ress = unfoldDiamondLoaded α χ := by
  cases lr; rfl

/-- The only `LoadRule` applicable to `~'⌊α⌋φ` for a normal `φ` is `LoadRule.dia'`. -/
lemma LoadRule.eq_unfoldDiamondLoaded' {α} {φ : Formula} {ress}
    (lr : LoadRule (~'⌊α⌋(AnyFormula.normal φ)) ress) : ress = unfoldDiamondLoaded' α φ := by
  cases lr; rfl

/-- Local rule applications preserve *basic* formulas: no local rule with children can have
a basic formula as its principal formula.
Note that `⊥` is not basic, for that case see `LocalRuleApp.preserve_bottom_down`. -/
lemma LocalRuleApp.preserve_basic_down (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ f, f.basic → f ∈ lra.X.bothSides → f ∈ Y.bothSides := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  subst hC
  cases rule <;> simp_all [applyLocalRule, Sequent.bothSides, Sequent.left, Sequent.right]
  case oneSidedL ress orule ress_def => cases orule <;> simp_all <;> grind [Program.isAtomic]
  case oneSidedR ress orule ress_def => cases orule <;> simp_all <;> grind [Program.isAtomic]
  case loadedL ress chi lrule ress_def =>
    cases lrule <;> simp_all <;> intros <;> subst_eqs <;> simp_all <;> grind [Program.isAtomic]
  case loadedR ress chi lrule ress_def =>
    cases lrule <;> simp_all <;> intros <;> subst_eqs <;> simp_all <;> grind [Program.isAtomic]

/-- Local rules never *load* a formula: if the sequent we apply a local rule to is free,
then so are all children. (The rules `loadedL` and `loadedR` are not applicable to a free
sequent, and all other local rules leave the `Olf` component unchanged.) -/
lemma LocalRuleApp.preserve_free (lra : LocalRuleApp) (hfree : lra.O = none) :
    ∀ Y ∈ lra.C, Y.O = none := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, pre⟩
  simp only at hfree
  subst hfree
  subst hC
  cases rule
  case oneSidedL ress orule ress_def => subst ress_def; rintro Y hY; simp at hY; grind [Sequent.O]
  case oneSidedR ress orule ress_def => subst ress_def; rintro Y hY; simp at hY; grind [Sequent.O]
  case LRnegL => simp_all
  case LRnegR => simp_all
  case loadedL => exact absurd pre.2.2 (by simp)
  case loadedR => exact absurd pre.2.2 (by simp)
