import Mathlib.Data.Finset.Basic

import Pdl.Syntax
import Pdl.Vocab
import Pdl.Semantics
import Pdl.LocalTableau
import Pdl.BigConDis
import Pdl.Soundness

open HasVocabulary HasSat


def IsPartInterpolant (N : TNode) (θ : Formula) :=
  voc θ ⊆ voc N ∧ (¬Satisfiable (N.LO ∪ {~θ}) ∧ ¬Satisfiable (N.RO ∪ {θ}))

def PartInterpolant (N : TNode) := Subtype <| IsPartInterpolant N

-- choice_property_in_image: slightly problematic
-- use let x : t := mapImageProp X
-- complains unless you specify all implicit arguments
-- for now: use x := mapImageProp, provide t in a comment
theorem choice_property_in_image {f : α → β }{l : List α} {p : β → Prop} (p_in_image: ∃y ∈ (List.map f l), p y) : ∃x ∈ l, p (f x) :=
  by simp at p_in_image; assumption

theorem localRuleApp_does_not_increase_vocab (ruleA : LocalRuleApp N C)
  : ∀c ∈ C, voc c ⊆ voc N := by sorry

def getFromSingleton : φ ∈ ({ψ} : Finset Formula) → φ = ψ := by sorry

theorem ruleImpliesChildSat
    {C : List TNode}
    {LR : TNode}
    {ruleApp : LocalRuleApp LR C} :
    Satisfiable LR → ∃c ∈ C, Satisfiable c :=
  by sorry

theorem localRuleSoundness
    (M : KripkeModel W)
    (w : W)
    (rule : LocalRule N ress)
    (X : List Formula) :
    (M, w) ⊨ X ∪ N.L ∪ N.R ∪ N.Olist → ∃res ∈ ress, (M, w) ⊨ (X ∪ res.L ∪ res.R ∪ res.Olist) :=
  by sorry

/-
theorem oneSidedRule_implies_child_sat_R
  {ruleApp : LocalRuleApp (L, R, O) C}
  (def_ruleA : ruleApp = (@LocalRuleApp.mk L R O C _ _ _ _ rule hC preproof))
  (rule_is_right : rule = LocalRule.oneSidedR orule)
  : Satisfiable (R ∪ X) → ∃c ∈ C, Satisfiable (c.R ∪ X) :=
  by sorry-/


theorem oneSidedRule_implies_child_sat_L
  {X : List Formula}
  (ruleApp : LocalRuleApp N C)
  (def_ruleA : ruleApp = (@LocalRuleApp.mk N C _ (List.map (fun res => (res, ∅, none)) _) rule hC preproof))
  (rule_is_left : rule = LocalRule.oneSidedL orule)
  : Satisfiable (N.LO ∪ X) → ∃c ∈ C, Satisfiable (c.LO ∪ X) := by
    sorry

-- this was a pain to type, but feel free to try and change it
-- all we really care about it going from any LocalRuleApp using loadedL to the Sat property
theorem oneSidedLoadRule_implies_child_sat_L
  {X : List Formula}
  (ruleApp : LocalRuleApp N C)
  (loadrule : LoadRule _ lress)
  (preproof :
    TNode.L (∅, ∅, some (Sum.inl (~'χ))) ⊆ TNode.L N ∧
      TNode.R (∅, ∅, some (Sum.inl (~'χ))) ⊆ TNode.R N ∧ TNode.O (∅, ∅, some (Sum.inl (~'χ))) ⊆ TNode.O N)
  (hC : C = applyLocalRule (LocalRule.loadedL χ loadrule) N)
  (def_ruleA : ruleApp = (@LocalRuleApp.mk N C _ (List.map (fun (X,o) => (X, ∅, Option.map Sum.inl o)) _) (LocalRule.loadedL χ loadrule) hC preproof))
  --(rule_is_loadleft : rule = LocalRule.loadedL χ loadrule)
  : Satisfiable (N.LO ∪ X) → ∃c ∈ C, Satisfiable (c.LO ∪ X) := by
    sorry

theorem sat_double_neq_invariant
    {X : List Formula}
    (φ : Formula)
    : Satisfiable (X ∪ {~~φ}) ↔ Satisfiable (X ∪ {φ}) :=
  by sorry

lemma bigConNeg_union_sat_down {X : List Formula} {l : List Formula} :
    Satisfiable (X ∪ {bigCon (l.map (~·))}) → ∀φ ∈ l, Satisfiable (X ∪ {~φ}) :=
  by sorry

lemma bigDis_union_sat_down {X : List Formula} {l : List Formula} :
    Satisfiable (X ∪ {bigDis l}) → ∃φ ∈ l, Satisfiable (X ∪ {φ}) :=
  by sorry

lemma oneSidedRuleL_preserves_rest
  {ruleApp : LocalRuleApp N C}
  (hmyrule : ruleApp = (@LocalRuleApp.mk N C _ (List.map (fun res => (res, [], none)) _) rule hC preproof))
  (rule_is_left : rule = LocalRule.oneSidedL orule )
  : ∀c ∈ C, c.RO = N.RO := by sorry

lemma oneSidedLoadRuleL_preserves_rest
  {ruleApp : LocalRuleApp N C}
  (hmyrule : ruleApp = (@LocalRuleApp.mk N C (∅, ∅, some (Sum.inl (~'χ))) (List.map (fun (X, o) => (X, ∅, Option.map Sum.inl o)) ress) rule hC preproof))
  (rule_is_left : rule = LocalRule.loadedL χ lrule )
  : ∀c ∈ C, c.RO = N.RO := by sorry

lemma oneSidedRuleR_preserves_rest
  {ruleApp : LocalRuleApp N C}
  (hmyrule : ruleApp = (@LocalRuleApp.mk N C _ (List.map (fun res => ([], res, none)) _) rule hC preproof))
  (rule_is_left : rule = LocalRule.oneSidedR orule )
  : ∀c ∈ C, c.RO = N.RO := by sorry

theorem negation_not_cosatisfiable
    {X : List Formula}
    (φ : Formula)
    (phi_in : φ ∈ X)
    (notPhi_in : (~φ) ∈ X)
    : ¬Satisfiable X :=
  by sorry


theorem localInterpolantStep
  (O : Option (Sum NegLoadFormula NegLoadFormula))
  (subθs : Πc ∈ C, PartInterpolant c)
  : LocalRuleApp N C → PartInterpolant N
  | @LocalRuleApp.mk _ _ conds ress rule hC ⟨h_Lcond, h_Rcond, h_Ocond⟩ => by
    rename List TNode => ress
    let ruleA := @LocalRuleApp.mk N C conds ress rule hC ⟨h_Lcond, h_Rcond, h_Ocond⟩
    let def_ruleA : ruleA = @LocalRuleApp.mk N C conds ress rule hC ⟨h_Lcond, h_Rcond, h_Ocond⟩ := by simp

    -- DISTINCTION ON LOCALRULE USED
    cases def_rule : rule with


    | oneSidedL orule =>
      let interList := C.attach.map $ λ⟨c, cinC⟩ => (subθs c cinC).val
      use bigDis interList
      constructor
      · intro ℓ ℓ_in_inter
        let ⟨⟨c,c_in_C⟩, _, ℓ_in_c'θ⟩ := choice_property_in_image <| vocOfBigDis.mp ℓ_in_inter
        have ℓ_in_c : ℓ ∈ voc c := (subθs c c_in_C).2 |> And.left <| ℓ_in_c'θ
        exact localRuleApp_does_not_increase_vocab ruleA c c_in_C <| ℓ_in_c

      · constructor
        · intro L_and_nθ_sat
          have L_and_bigC_sat : Satisfiable (N.LO ∪ {(~~bigCon (List.map (fun x => ~x) interList))}) := by
            rcases L_and_nθ_sat with ⟨W, M, w, MWsat⟩
            have evalDis : Evaluates M w <| ~(bigDis interList) := MWsat (~ (bigDis interList)) (by
              simp; apply Or.inr; sorry -- no clue, but should be minor
            )
            rw [eval_neg_BigDis_iff_eval_bigConNeg] at evalDis
            use W, M, w
            simp
            intro φ φ_in_L_bigC
            apply Or.elim φ_in_L_bigC
            · intro φ_in_L
              apply MWsat φ (by simp; exact Or.inl φ_in_L)
            · intro φ_in_bigC; rw [getFromSingleton φ_in_bigC]; simp at evalDis ⊢; exact evalDis
          let ⟨c, c_in_C, sat_c_nnθ⟩ := oneSidedRule_implies_child_sat_L ruleA def_ruleA def_rule L_and_bigC_sat
          have sat_c_θ : Satisfiable (c.LO ∪ {(bigCon <| interList.map (~·))}) :=
              sat_double_neq_invariant (bigCon <| interList.map (~·)) |> Iff.mp <| sat_c_nnθ
          have sat_c_c'sθ : Satisfiable <| c.LO ∪ {~ (subθs c c_in_C).1} :=
            bigConNeg_union_sat_down sat_c_θ (subθs c c_in_C).1 (by simp; use c, c_in_C)
          exact (subθs c c_in_C).2 |> And.right |> And.left <| sat_c_c'sθ

        . intro R_and_θ_sat
          have ⟨⟨c,c_in_C⟩, _, sat_cθ⟩ := choice_property_in_image <| bigDis_union_sat_down R_and_θ_sat
          have cR_eq_R : c.RO = N.RO := (oneSidedRuleL_preserves_rest def_ruleA def_rule) c c_in_C
          rw[←cR_eq_R] at sat_cθ
          exact (subθs c c_in_C).2 |> And.right |> And.right <| sat_cθ

    | oneSidedR orule => sorry

    | LRnegL φ =>
      use φ
      constructor
      · intro ℓ ℓ_in_φ
        simp [voc] at ℓ_in_φ ⊢
        constructor
        · use φ; constructor
          · exact h_Lcond <| Finset.mem_singleton.mpr rfl
          . exact ℓ_in_φ
        · use ~φ; constructor
          · exact h_Rcond <| Finset.mem_singleton.mpr rfl
          . simp; exact ℓ_in_φ

      · constructor <;> apply negation_not_cosatisfiable φ <;> simp
        · apply Or.intro_left; simp [TNode.LO]
          apply Or.intro_left
          apply h_Lcond; simp [TNode.L]; exact Finset.mem_singleton.mpr rfl
        · apply Or.intro_right; exact Finset.mem_singleton.mpr rfl
        · apply Or.intro_right; exact Finset.mem_singleton.mpr rfl
        · apply Or.intro_left; simp [TNode.RO]
          apply Or.intro_left
          apply h_Rcond; simp [TNode.R]; exact Finset.mem_singleton.mpr rfl

    | LRnegR φ => sorry

    | loadedL χ lrule =>
      let interList := C.attach.map $ λ⟨c, cinC⟩ => (subθs c cinC).val
      use bigDis interList
      constructor
      · intro ℓ ℓ_in_inter
        let ⟨⟨c,c_in_C⟩, _, ℓ_in_c'θ⟩ := choice_property_in_image <| vocOfBigDis.mp ℓ_in_inter
        have ℓ_in_c : ℓ ∈ voc c := (subθs c c_in_C).2 |> And.left <| ℓ_in_c'θ
        exact localRuleApp_does_not_increase_vocab ruleA c c_in_C <| ℓ_in_c

      · constructor
        · intro L_and_nθ_sat
          have L_and_bigC_sat : Satisfiable (N.LO ∪ {(~~bigCon (List.map (fun x => ~x) interList))}) := by
            rcases L_and_nθ_sat with ⟨W, M, w, MWsat⟩
            have evalDis : Evaluates M w <| ~(bigDis interList) := MWsat (~ (bigDis interList)) (by
              simp; apply Or.inr; sorry -- no clue, but should be minor
            )
            rw [eval_neg_BigDis_iff_eval_bigConNeg] at evalDis
            use W, M, w
            simp
            intro φ φ_in_L_bigC
            apply Or.elim φ_in_L_bigC
            · intro φ_in_L
              apply MWsat φ (by simp; exact Or.inl φ_in_L)
            · intro φ_in_bigC; rw [getFromSingleton φ_in_bigC]; simp at evalDis ⊢; exact evalDis
          let ⟨c, c_in_C, sat_c_nnθ⟩ := (oneSidedLoadRule_implies_child_sat_L ruleA lrule
            (by  simp [TNode.L, TNode.R, TNode.O];  apply h_Ocond)
            (by rw [hC]; rw [def_rule])
            (by rw [def_ruleA]; simp; rw [def_rule])
            L_and_bigC_sat)
          have sat_c_θ : Satisfiable (c.LO ∪ {(bigCon <| interList.map (~·))}) :=
              sat_double_neq_invariant (bigCon <| interList.map (~·)) |> Iff.mp <| sat_c_nnθ
          have sat_c_c'sθ : Satisfiable <| c.LO ∪ {~ (subθs c c_in_C).1} :=
            bigConNeg_union_sat_down sat_c_θ (subθs c c_in_C).1 (by simp; use c, c_in_C)
          exact (subθs c c_in_C).2 |> And.right |> And.left <| sat_c_c'sθ

        . intro R_and_θ_sat
          have ⟨⟨c,c_in_C⟩, _, sat_cθ⟩ := choice_property_in_image <| bigDis_union_sat_down R_and_θ_sat
          have cR_eq_R : c.RO = N.RO := (oneSidedLoadRuleL_preserves_rest def_ruleA def_rule) c c_in_C
          rw[←cR_eq_R] at sat_cθ
          exact (subθs c c_in_C).2 |> And.right |> And.right <| sat_cθ

    | loadedR χ lrule => sorry


theorem partInterpolation :
    ∀ (L R : List Formula), ¬Satisfiable (L ∪ R) → PartInterpolant (L,R,none) := by
  sorry
