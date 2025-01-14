import Mathlib.Data.Finset.Basic

import Pdl.Completeness
import Pdl.Distance

/-! # Interpolants for Partitions (big part of Section 7) -/

open HasSat

def Olf.toForms : Olf → List Formula
| none => []
| some (Sum.inl ⟨lf⟩) => [~ lf.unload]
| some (Sum.inr ⟨lf⟩) => [~ lf.unload]

-- BUG: Using `.toForms` below is wrong, because it ignores which side the Olf is on!

@[simp]
def Sequent.left (X : Sequent) : List Formula := X.L ++ X.O.toForms
@[simp]
def Sequent.right (X : Sequent) : List Formula := X.R ++ X.O.toForms

/-- Joint vocabulary of all parts of a `Sequent`. -/
@[simp]
def jvoc (X : Sequent) : Vocab := (X.left).fvoc ∩ (X.right).fvoc

def isPartInterpolant (X : Sequent) (θ : Formula) :=
  θ.voc ⊆ jvoc X ∧ (¬ satisfiable ((~θ) :: X.left) ∧ ¬ satisfiable (θ :: X.right))

def PartInterpolant (N : Sequent) := Subtype <| isPartInterpolant N

-- move to UnfoldBox.lean ?
theorem unfoldBox_voc {x α φ} {L} (L_in : L ∈ unfoldBox α φ) {ψ} (ψ_in : ψ ∈ L)
    (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  rcases unfoldBoxContent _ _ _ L_in _ ψ_in with ψ_def | ⟨τ, τ_in, ψ_def⟩ | ⟨a, δ, ψ_def, _⟩
  all_goals subst ψ_def
  · right; exact x_in_voc_ψ
  · simp only [Formula.voc] at x_in_voc_ψ
    left
    -- PROBLEM: here and in next case we need the stronger version of `unfoldBoxContent`.
    sorry
  · simp at *
    rw [Formula.voc_boxes] at x_in_voc_ψ
    sorry

-- move to UnfoldDia.lean ?
theorem unfoldDiamond_voc {x α φ} {L} (L_in : L ∈ unfoldDiamond α φ) {ψ} (ψ_in : ψ ∈ L)
    (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  simp [unfoldDiamond, Yset] at L_in
  -- TODO use unfoldDiamondContent here instead?
  rcases L_in with ⟨Fs, δ, in_H, def_L⟩
  subst def_L
  simp at ψ_in
  cases ψ_in
  case inl hyp =>
    left
    have := H_mem_test α ψ in_H hyp
    rcases this with ⟨τ, τ_in, ψ_def⟩
    subst ψ_def
    exact testsOfProgram.voc α τ_in x_in_voc_ψ
  case inr ψ_def =>
    have := H_mem_sequence
    subst ψ_def
    simp only [Formula.voc, Formula.voc_boxes, Finset.mem_union] at x_in_voc_ψ
    cases x_in_voc_ψ
    case inl hyp =>
      left
      rw [Vocab.fromListProgram_map_iff] at *
      rcases hyp with ⟨α', α'_in, x_in⟩
      -- need lemma that vocabOf in (H α) is subset of vocabOf α
      sorry
    · right
      assumption

theorem localRule_does_not_increase_vocab_L (rule : LocalRule (Lcond, Rcond, Ocond) ress) :
    ∀ res ∈ ress, res.1.fvoc ⊆ Lcond.fvoc := by
  intro res ress_in_ress x x_in_res
  cases rule
  case oneSidedL ress orule =>
    cases orule <;> simp_all
    case nCo =>
      aesop
    case box α φ =>
      rw [Vocab.fromListFormula_map_iff] at x_in_res
      rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
      rcases ress_in_ress with ⟨L, L_in, def_res⟩
      subst def_res
      simp at *
      exact unfoldBox_voc L_in ψ_in x_in_voc_ψ
    case dia =>
      rw [Vocab.fromListFormula_map_iff] at x_in_res
      rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
      rcases ress_in_ress with ⟨L, L_in, def_res⟩
      subst def_res
      simp at *
      exact unfoldDiamond_voc L_in ψ_in x_in_voc_ψ
  -- other cases *should be* trivial (as in Bml)
  all_goals
    simp at *
  · aesop
  case loadedL ress χ lrule =>
    rcases ress_in_ress with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    simp [Vocab.fromListProgram_map_iff, Vocab.fromListFormula_map_iff] at *
    rcases x_in_res with ⟨φ, φ_in_L, bla⟩
    -- wait, where should a contradiction come from now?
    -- PROBLEM: theorem is not true. The loadedL case here *does* add voc in "L" part, coming "O".
    -- SOLUTION: Do not have separate theorems for vocab_L, vocab_R and vocab_O.
    sorry
  · aesop

theorem localRule_does_not_increase_vocab_R (rule : LocalRule (Lcond, Rcond, Ocond) ress) :
    ∀ res ∈ ress, res.2.1.fvoc ⊆ Rcond.fvoc := by
  -- should be dual to _L version
  sorry

theorem localRule_does_not_increase_vocab_O (rule : LocalRule (Lcond, Rcond, Ocond) ress) :
    ∀ res ∈ ress, res.2.2.voc ⊆ Ocond.voc := by
  sorry

theorem localRuleApp_does_not_increase_jvoc (ruleA : LocalRuleApp X C) :
    ∀ Y ∈ C, jvoc Y ⊆ jvoc X := by
  match ruleA with
  | @LocalRuleApp.mk L R C ress O Lcond Rcond Ocond lrule hC preconditionProof =>
    rintro ⟨cL, cR, cO⟩ C_in x x_in_voc_C
    simp [jvoc] at x_in_voc_C
    have := localRule_does_not_increase_vocab_L lrule
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
    · constructor
      · intro L_and_nθ_sat
        sorry -- See Bml?
      · intro R_and_θ_sat
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
      simp_all [evaluate]
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp, evaluate] at *
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
      simp_all [evaluate]

  case loadedL =>
    -- keep interpolant the same
    sorry
  case loadedR =>
    -- keep interpolant the same
    sorry


/-- The exits of a cluster: (C \ C+). -/
-- IDEA: similar to endNodesOf?
def exitsOf : (tab : Tableau Hist (L, R, some nlf)) → List (PathIn tab)
| .rep lpr => [] -- a repeat is never an exit
| .loc lt next => sorry -- TODO: can the exit be "inside" lt? Or can we filter `endNodesOf lt`?
| .pdl r next => sorry -- TODO: if (L-) then root of next is exit, also if (M) removes loading etc?

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
