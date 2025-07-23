import Mathlib.Data.Finset.Basic

import Pdl.Completeness

/-! # Interpolants for Partitions (big part of Section 7) -/

open HasSat

def Olf.L : Olf → List Formula
| none => []
| some (Sum.inl ⟨lf⟩) => [~ lf.unload]
| some (Sum.inr _) => []

@[simp]
lemma Olf.L_none : Olf.L none = [] := by rfl
@[simp]
lemma Olf.L_inr : Olf.L (some (Sum.inr lf)) = [] := by rfl

def Olf.R : Olf → List Formula
| none => []
| some (Sum.inl _) => []
| some (Sum.inr ⟨lf⟩) => [~ lf.unload]

@[simp]
lemma Olf.R_none : Olf.R none = [] := by rfl
@[simp]
lemma Olf.R_inl : Olf.R (some (Sum.inl lf)) = [] := by rfl

@[simp]
def Sequent.left (X : Sequent) : List Formula := X.L ++ X.O.L
@[simp]
def Sequent.right (X : Sequent) : List Formula := X.R ++ X.O.R

/-- Joint vocabulary of all parts of a `Sequent`. -/
@[simp]
def jvoc (X : Sequent) : Vocab := (X.left).fvoc ∩ (X.right).fvoc

def isPartInterpolant (X : Sequent) (θ : Formula) :=
  θ.voc ⊆ jvoc X ∧ (¬ satisfiable ((~θ) :: X.left) ∧ ¬ satisfiable (θ :: X.right))

def PartInterpolant (N : Sequent) := Subtype <| isPartInterpolant N

def lfovoc (L : List (List Formula × Option NegLoadFormula)) : Vocab :=
  Vocab.fromList $ L.map (fun ⟨fs,o⟩ => fs.fvoc ∪ (o.map NegLoadFormula.voc).getD ∅)

lemma LoadRule_voc (lr : LoadRule (~'χ) ress) : lfovoc ress ⊆ χ.voc := by
  intro x x_in
  unfold lfovoc at *
  cases lr <;> simp_all
  -- TODO is there a more ergonomic way to define `lfovoc`?
  · sorry
  · sorry

theorem localRule_does_not_increase_vocab_L {Lcond Rcond Ocond B}
    (rule : LocalRule (Lcond, Rcond, Ocond) B) :
    ∀ res ∈ B, res.L.fvoc ∪ res.O.L.fvoc ⊆ Lcond.fvoc ∪ Ocond.L.fvoc := by
  intro res res_in_B x x_in_res
  cases rule
  case oneSidedL ress orule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, L_in, def_res⟩
    subst def_res
    simp at *
    rw [Vocab.fromListFormula_map_iff] at x_in_res
    rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
    cases orule
    case nCo => aesop
    case box α φ α_notAt => have := unfoldBox_voc L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedL ress χ lrule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    simp at *
    simp only [Vocab.fromListFormula_map_iff] at x_in_res
    rcases x_in_res with ⟨φ, φ_in_L, x_in_φvoc⟩|⟨φ, φ_in_OlfL, x_in_φvoc⟩
    all_goals
      rw [Vocab.fromListFormula_map_iff]
      simp only [Olf.L, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, Formula.voc]
      have := LoadRule_voc lrule
      unfold lfovoc at *
      simp only [List.fvoc, LoadFormula.voc] at *
      apply this; clear this
      rw [Vocab.fromList_map_iff]
      refine ⟨(L, lnf), in_ress, ?_⟩
      simp
    · left; rw [Vocab.fromListFormula_map_iff]; use φ
    · right
      cases lnf <;> simp [Olf.L] at *
      subst φ_in_OlfL
      exact x_in_φvoc
  case loadedR B_def =>
    simp only [List.fvoc, Finset.mem_union] at x_in_res
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    rcases x_in_res with _|x_in
    · aesop
    · simp [Olf.L] at *; absurd x_in; aesop
  -- other cases are all trivial (as in Bml)
  all_goals
    simp at *
  · aesop

theorem localRule_does_not_increase_vocab_R (rule : LocalRule (Lcond, Rcond, Ocond) ress) :
    ∀ res ∈ ress, res.R.fvoc ∪ res.O.R.fvoc ⊆ Rcond.fvoc ∪ Ocond.R.fvoc := by
  -- should be analogous to _L version
  intro res res_in_B x x_in_res
  cases rule
  case oneSidedR ress orule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, L_in, def_res⟩
    subst def_res
    simp at *
    rw [Vocab.fromListFormula_map_iff] at x_in_res
    rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
    cases orule
    case nCo => aesop
    case box α φ α_notAt => have := unfoldBox_voc L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedR ress χ lrule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    simp at *
    simp only [Vocab.fromListFormula_map_iff] at x_in_res
    rcases x_in_res with ⟨φ, φ_in_L, x_in_φvoc⟩|⟨φ, φ_in_OlfR, x_in_φvoc⟩
    all_goals
      rw [Vocab.fromListFormula_map_iff]
      simp only [Olf.R, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, Formula.voc]
      have := LoadRule_voc lrule
      unfold lfovoc at *
      simp only [List.fvoc, LoadFormula.voc] at *
      apply this; clear this
      rw [Vocab.fromList_map_iff]
      refine ⟨(L, lnf), in_ress, ?_⟩
      simp
    · left; rw [Vocab.fromListFormula_map_iff]; use φ
    · right
      cases lnf <;> simp [Olf.R] at *
      subst φ_in_OlfR
      exact x_in_φvoc
  case loadedL B_def =>
    simp only [List.fvoc, Finset.mem_union] at x_in_res
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    rcases x_in_res with _|x_in
    · aesop
    · simp [Olf.R] at *; absurd x_in; aesop
  -- other cases are all trivial (as in Bml)
  all_goals
    simp at *
  · aesop

theorem localRuleApp_does_not_increase_jvoc (ruleA : LocalRuleApp X C) :
    ∀ Y ∈ C, jvoc Y ⊆ jvoc X := by
  match ruleA with
  | @LocalRuleApp.mk L R C ress O Lcond Rcond Ocond lrule hC preconditionProof =>
    rintro ⟨cL, cR, cO⟩ C_in x x_in_voc_C
    simp [jvoc] at x_in_voc_C
    have := localRule_does_not_increase_vocab_L lrule
    have := localRule_does_not_increase_vocab_R lrule
    subst hC
    -- See Bml?
    sorry

/-- Maehara's method for local rule applications.
This is `itpLeaves` for singleton clusters in the notes, but not only. -/
def localInterpolantStep (L R : List Formula) (o) (ruleA : LocalRuleApp (L,R,o) C)
    (subθs : Π c ∈ C, PartInterpolant c)
    : PartInterpolant (L,R,o) := by
  -- UNPACKING TERMS
  rcases def_ruleA : ruleA with @⟨L, R, C, ress, O, Lcond, Rcond, Ocond, rule, hc, precondProof⟩
  -- DISTINCTION ON LOCALRULE USED
  cases def_rule : rule
  case oneSidedL orule =>
    let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
    use dis interList
    constructor
    · intro n n_in_inter
      rw [in_voc_dis] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp [interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · have locSound := @localRuleTruth _ _ ruleA
      constructor
      all_goals
        rintro ⟨W,M,w,w_⟩
        specialize locSound M w
      ·
        sorry -- See Bml?
      ·
        sorry -- See Bml?
  case oneSidedR orule =>
    let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
    use Con interList
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_inter
      rw [in_voc_con] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp [interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · intro L_and_nθ_sat
      sorry -- See Bml?
    · intro R_and_θ_sat
      sorry -- See Bml?

  case LRnegL φ =>
    use φ
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      simp [Vocab.fromListFormula_map_iff] at *
      aesop
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp, evaluate] at *
      subst_eqs
      absurd w_.1
      have := w_.2 φ
      simp_all
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp] at *
      subst_eqs
      absurd w_.1
      have := w_.2 (~φ)
      simp_all [evaluate]

  case LRnegR φ =>
    use ~φ
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      simp [Vocab.fromListFormula_map_iff] at *
      aesop
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp, evaluate] at *
      subst_eqs
      absurd w_.1
      have := w_.2 (~φ)
      simp_all [evaluate]
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp, evaluate] at *
      subst_eqs
      absurd w_.1
      have := w_.2 φ
      simp_all

  case loadedL =>
    -- keep interpolant the same
    sorry
  case loadedR =>
    -- keep interpolant the same
    sorry


/-- The exits of a cluster: (C \ C+). -/
-- IDEA: similar to endNodesOf?
def exitsOf : (tab : Tableau Hist (L, R, some nlf)) → List (PathIn tab)
| .lrep lpr => [] -- a repeat is never an exit
| .loc _ _ lt next => sorry -- TODO: can the exit be "inside" lt? Or can we filter `endNodesOf lt`?
| .pdl _ _ _ next => sorry -- TODO: if (L-) then root of next is exit, also if (M) removes loading etc?

-- TODO move to Soundness.lean ?
def PathIn.children : (p : PathIn tab) → List (PathIn tab) := sorry

/-- C+ -/
def plus_exits {X} {tab : Tableau .nil X} (C : List (PathIn tab)) : List (PathIn tab) :=
  C ++ (C.map (fun p => p.children)).flatten

/-- W.l.o.g version of `clusterInterpolation`. -/
def clusterInterpolation_right {Hist L R nlf}
    (tab : Tableau Hist (L, R, some (Sum.inr nlf)))
    (exitIPs : ∀ e ∈ exitsOf tab, PartInterpolant (nodeAt e))
    : PartInterpolant (L, R, some (Sum.inr nlf)) := by
  sorry

/-- Given a tableau where the root is loaded, and exit interpolants, interpolate the root. -/
def clusterInterpolation {Hist L R snlf}
    (tab : Tableau Hist (L, R, some snlf))
    (exitIPs : ∀ e ∈ exitsOf tab, PartInterpolant (nodeAt e))
    : PartInterpolant (L, R, some snlf) := by
  cases snlf
  case inl nlf =>
    -- TODO: "flip" the left/right sides of `tab` so we can apply the wlog version.
    sorry
  case inr nlf =>
    exact @clusterInterpolation_right _ _ _ nlf tab exitIPs

def tabToInt {X : Sequent} (tab : Tableau .nil X) :
    PartInterpolant X := by
  sorry
