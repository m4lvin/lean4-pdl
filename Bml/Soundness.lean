-- SOUNDNESS

import Bml.Syntax
import Bml.Tableau

open Classical

-- attribute [local instance 10] prop_decidable -- delete me?

open HasSat

-- Combine a collection of pointed models with one new world using the given valuation.
-- TODO: rewrite to term mode?
def combinedModel {β : Type} (collection : β → Σ W : Type, KripkeModel W × W)
    (newVal : Char → Prop) :
    KripkeModel (Sum Unit (Σ k : β, (collection k).fst)) × Sum Unit (Σ k : β, (collection k).fst) :=
  by
  constructor
  constructor
  · -- making the valuation function:
    intro world
    cases world
    case inl newWorld => -- the one new world
      cases newWorld
      exact newVal -- use new given valuation here!!
    case inr oldWorld => -- world in one of the given models:
      cases' oldWorld with R w
      exact (collection R).snd.fst.val w
  · -- defining relations:
    intro worldOne worldTwo
    cases worldOne <;> cases worldTwo -- four cases about two new or old worlds
    case inl.inl => exact False -- no reflexive loop at the new world.
    case inl.inr newWorld oldWorld =>
      exact HEq oldWorld.snd (collection oldWorld.fst).snd.snd -- conect new world to given points.
    case inr.inl => exact False -- no connection from models to new world
    case inr.inr oldWorldOne oldWorldTwo =>
      -- connect two old worlds iff they are from the same model and were connected there already:
      cases' oldWorldOne with kOne wOne
      cases' oldWorldTwo with kTwo wTwo
      have help : kOne = kTwo → Prop := by
        intro same
        have sameCol : collection kOne = collection kTwo := by rw [← same]
        rw [← sameCol] at wTwo
        exact (collection kOne).snd.fst.Rel wOne wTwo
      exact dite (kOne = kTwo) (fun same => help same) fun _ => False
  · -- point at the new world:
    left
    exact ()

-- The combined model preserves all truths at the old worlds.
theorem combMo_preserves_truth_at_oldWOrld {β : Type}
    (collection : β → Σ W : Type, KripkeModel W × W) (newVal : Char → Prop) :
    ∀ (f : Formula) (R : β) (oldWorld : (collection R).fst),
      Evaluate ((combinedModel collection newVal).fst, Sum.inr ⟨R, oldWorld⟩) f ↔
        Evaluate ((collection R).snd.fst, oldWorld) f :=
  by
  intro f
  induction f <;> intro R oldWorld
  case bottom => aesop
  case atom_prop c =>
    unfold combinedModel
    simp
  case neg f f_IH =>
    unfold Evaluate
    rw [f_IH R oldWorld]
  case And f g f_IH g_IH =>
    unfold Evaluate
    rw [f_IH R oldWorld]
    rw [g_IH R oldWorld]
  case box f f_IH =>
    unfold Evaluate
    constructor
    · intro true_in_combo
      intro otherWorld rel_in_old_model
      specialize f_IH R otherWorld
      rw [← f_IH]
      specialize true_in_combo (Sum.inr ⟨R, otherWorld⟩)
      apply true_in_combo
      unfold combinedModel
      simp
      exact rel_in_old_model
    · intro true_in_old
      simp
      constructor
      · intro newWorld
        unfold combinedModel
        tauto
      -- the new world is never reachable, trivial case
      · intro otherR otherWorld
        intro rel_in_new_model
        specialize f_IH otherR otherWorld
        unfold combinedModel at rel_in_new_model
        have sameR : R = otherR := by
          by_contra
          aesop
        subst sameR
        rw [f_IH]
        apply true_in_old
        -- remains to show that related in old model
        simp at *
        exact rel_in_new_model

-- The combined model for X satisfies X.
theorem combMo_sat_X {X : Finset Formula} {β : Set Formula}
    {beta_def : β = {R : Formula | ~R.box ∈ X}} (simple_X : Simple X) (not_closed_X : ¬Closed X)
    (collection : β → Σ W : Type, KripkeModel W × W)
    (all_pro_sat :
      ∀ R : β,
        ∀ f ∈ projection X ∪ {~R}, Evaluate ((collection R).snd.fst, (collection R).snd.snd) f) :
    ∀ f ∈ X,
      Evaluate
        ((combinedModel collection fun c => Formula.atom_prop c ∈ X).fst,
          (combinedModel collection fun c => Formula.atom_prop c ∈ X).snd)
        f :=
  by
  intro f f_in_X
  cases f
  -- no induction because X is simple
  case bottom =>
    unfold Closed at not_closed_X
    tauto
  case atom_prop =>
    unfold combinedModel
    unfold Evaluate
    simp
    exact f_in_X
  case
    neg f =>
    -- subcases :-/
    cases f
    case atom_prop =>
      unfold combinedModel
      unfold Evaluate
      unfold Closed at not_closed_X
      rw [not_or] at not_closed_X
      simp at *
      tauto
    case box f =>
      -- set coMo := ,
      simp only [Evaluate, not_forall]
      -- need reachable world with ~f, use the β-witness
      let h : f ∈ β := by rw [beta_def]; use f_in_X
      let oldWorld : Sum Unit (Σ k : β, (collection k).fst) :=
        Sum.inr ⟨⟨f, h⟩, (collection ⟨f, h⟩).snd.snd⟩
      use oldWorld
      constructor
      · -- show that f is false at old world
        have coMoLemma :=
          combMo_preserves_truth_at_oldWOrld collection (fun c : Char => (·c) ∈ X) f ⟨f, h⟩
            (collection ⟨f, h⟩).snd.snd
        rw [coMoLemma]
        specialize all_pro_sat ⟨f, h⟩ (~f)
        unfold Evaluate at all_pro_sat
        simp at *
        exact all_pro_sat
      ·-- show that worlds are related in combined model (def above, case 2)
        unfold combinedModel;
        simp
    case bottom => tauto
    case neg f =>
      unfold Simple SimpleForm at simple_X
      simp at simple_X
      specialize simple_X (~~f) f_in_X
      simp at simple_X
    case And f g =>
      unfold Simple SimpleForm at simple_X
      simp at simple_X
      specialize simple_X (~(f⋀g)) f_in_X
      simp at simple_X
  case And fa fb =>
    unfold Simple at simple_X
    simp at simple_X
    specialize simple_X (fa⋀fb) f_in_X
    simp at simple_X
  case box f =>
    unfold Evaluate
    intro otherWorld is_rel
    cases otherWorld
    · cases is_rel
    case inr otherWorld => -- otherWorld cannot be the (unreachable) new world
      have coMoLemma :=
        combMo_preserves_truth_at_oldWOrld collection (fun c => (·c) ∈ X) f otherWorld.fst
          otherWorld.snd
      simp at coMoLemma
      rw [coMoLemma]
      specialize all_pro_sat otherWorld.fst f
      simp at all_pro_sat
      rw [or_imp] at all_pro_sat
      cases' all_pro_sat with _ all_pro_sat_right
      rw [← proj] at f_in_X
      specialize all_pro_sat_right f_in_X
      have sameWorld : otherWorld.snd = (collection otherWorld.fst).snd.snd := by
        rw [heq_iff_eq.mp (HEq.symm is_rel)]
      rw [sameWorld]
      simp
      exact all_pro_sat_right

-- Lemma 1 (page 16)
-- A simple set of formulas X is satisfiable if and only if
-- it is not closed  and  for all ¬[A]R ∈ X also XA; ¬R is satisfiable.
theorem Lemma1_simple_sat_iff_all_projections_sat {X : Finset Formula} :
    Simple X → (Satisfiable X ↔ ¬Closed X ∧ ∀ R, ~(□R) ∈ X → Satisfiable (projection X ∪ {~R})) :=
  by
  intro X_is_simple
  constructor
  · -- left to right
    intro sat_X
    unfold Satisfiable at *
    rcases sat_X with ⟨W, M, w, w_sat_X⟩
    constructor
    · -- show that X is not closed:
      by_contra hyp
      unfold Closed at hyp
      cases' hyp with bot_in_X f_and_notf_in_X
      · exact w_sat_X ⊥ bot_in_X
      · rcases f_and_notf_in_X with ⟨f, f_in_X, notf_in_X⟩
        let w_sat_f := w_sat_X f f_in_X
        let w_sat_notf := w_sat_X (~f) notf_in_X
        exact absurd w_sat_f w_sat_notf
    · -- show that for each ~[]R ∈ X the projection with ~R is satisfiable:
      intro R notboxr_in_X
      let w_sat_notboxr := w_sat_X (~(□R)) notboxr_in_X
      unfold Evaluate at w_sat_notboxr
      simp at w_sat_notboxr
      rcases w_sat_notboxr with ⟨v, w_rel_v, v_sat_notr⟩
      use W, M, v
      intro g
      simp at *
      rw [or_imp]
      constructor
      · intro g_is_notR
        rw [g_is_notR]
        exact v_sat_notr
      · intro boxg_in_X
        rw [proj] at boxg_in_X
        specialize w_sat_X (□g) boxg_in_X
        unfold Evaluate at w_sat_X
        exact w_sat_X v w_rel_v
  · -- right to left
    intro rhs
    cases' rhs with not_closed_X all_pro_sat
    unfold Satisfiable at *
    -- Let's build a new Kripke model!
    let β := {R : Formula | ~(□R) ∈ X}
    -- beware, using Axioms of Choice here!
    choose typeFor this_pro_sat using all_pro_sat
    choose modelFor this_pro_sat using this_pro_sat
    choose worldFor this_pro_sat using this_pro_sat
    -- define the collection:
    let collection : β → Σ W : Type, KripkeModel W × W :=
      by
      intro k
      cases' k with R notboxr_in_X
      simp at notboxr_in_X
      use typeFor R notboxr_in_X, modelFor R notboxr_in_X, worldFor R notboxr_in_X
    let newVal c := Formula.atom_prop c ∈ X
    let BigM := combinedModel collection newVal
    use Sum Unit (Σ k : β, (collection k).fst)
    use BigM.fst, BigM.snd
    -- apply Lemma, missing last argument "all_pro_sat"
    -- we need to use that X_is_simple (to restrict cases what phi can be)
    -- and that X is not closed (to ensure that it is locally consistent)
    apply combMo_sat_X X_is_simple not_closed_X collection
    -- it remains to show that the new big model satisfies X
    intro R f f_inpro_or_notr
    cases' R with R notrbox_in_X
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Subtype.coe_mk] at *
    specialize this_pro_sat R notrbox_in_X
    cases' f_inpro_or_notr with f_inpro f_is_notboxR
    · -- if f is in the projection
      specialize this_pro_sat f
      rw [or_imp] at this_pro_sat
      cases' this_pro_sat with this_pro_sat_l this_pro_sat_r
      exact this_pro_sat_l f_inpro
    · -- case where f is ~[]R
      cases f_is_notboxR
      case refl =>
        specialize this_pro_sat (~R)
        rw [or_imp] at this_pro_sat
        cases' this_pro_sat with this_pro_sat_l this_pro_sat_r
        tauto
    simp


-- to check β
-- Each rule is sound and preserves satisfiability "downwards"
-- theorem localRuleSoundness {α : Finset Formula} {B : Finset (Finset Formula)} :
--  LocalRule α B → Satisfiable α → ∃ β ∈ B, Satisfiable β :=

theorem localRuleSoundness (rule : LocalRule) (L R : Finset Formula) :
  LocalRuleToPrecondition rule L R → Satisfiable (L ∪ R) → ∃LR ∈ LocalRuleToChildren rule L R, Satisfiable (LR.fst ∪ LR.snd) :=
  by
  intro proof sat
  unfold Satisfiable at sat
  rcases sat with ⟨W, M, w, w_sat_LR⟩
  cases rule
  case oneSidedL lr =>                       -- left side
    cases lr
    case not φ =>
      simp at *
    case bot  =>
      simp at *
      have contradiction : Evaluate (M, w) ⊥ :=
        w_sat_LR ⊥ (Or.inl proof)
      exact contradiction
    case neg φ =>
      simp at *
      use W; use M; use w
      intro φ₁ hyp
      cases hyp
      case inl h =>
        cases h
        case inl h₁ =>
          rw [h₁]
          have eval_neg : Evaluate (M, w) (~~φ) :=
            w_sat_LR (~~φ) (Or.inl proof)
          simp [Evaluate] at eval_neg
          exact eval_neg
        case inr h₁ =>
          aesop
      case inr h =>
        aesop
    case con φ ψ =>
      simp at *
      use W; use M; use w
      have eval_con : Evaluate (M, w) (φ⋀ψ) :=
        w_sat_LR (φ⋀ψ) (Or.inl proof)
      intro φ₁ hyp
      cases hyp <;> aesop
    case ncon φ ψ =>
      simp at *
      have eval_ncon : Evaluate (M, w) (~(φ⋀ψ)) :=
        w_sat_LR (~(φ⋀ψ)) (Or.inl proof)
      simp [Evaluate, imp_iff_not_or] at eval_ncon
      cases eval_ncon <;> aesop
  case oneSidedR lr =>                            -- right side (mostly copy paste, will try custom tactic later)
    cases lr
    case not φ =>
      simp at *
    case bot  =>
      simp at *
      have contradiction : Evaluate (M, w) ⊥ :=
        w_sat_LR ⊥ (Or.inr proof)   -- changed Or.inl to Or.inr
      exact contradiction
    case neg φ =>
      simp at *
      use W; use M; use w
      intro φ₁ hyp
      cases hyp
      case inl h =>
        aesop
      case inr h =>
        cases h
        case inl h₁ =>  -- inl switched with inr
          rw [h₁]
          have eval_neg : Evaluate (M, w) (~~φ) :=
            w_sat_LR (~~φ) (Or.inr proof)
          simp [Evaluate] at eval_neg
          exact eval_neg
        case inr h₁ =>
          aesop
    case con φ ψ =>
      simp at *
      use W; use M; use w
      have eval_con : Evaluate (M, w) (φ⋀ψ) :=
        w_sat_LR (φ⋀ψ) (Or.inr proof)   -- changed Or.inl to Or.inr
      intro φ₁ hyp
      cases hyp <;> aesop
    case ncon φ ψ =>
      simp at *
      have eval_ncon : Evaluate (M, w) (~(φ⋀ψ)) :=
        w_sat_LR (~(φ⋀ψ)) (Or.inr proof)     -- changed Or.inl to Or.inr
      simp [Evaluate, imp_iff_not_or] at eval_ncon
      cases eval_ncon <;> aesop
  case LRnegL φ =>       -- LRnegL and LRnegR are almost equal
    simp at *
    have eval_phi : Evaluate (M, w) φ := by
      exact w_sat_LR φ (Or.inl proof.left)
    have eval_negphi : Evaluate (M, w) (~φ) := by
      exact w_sat_LR (~φ) (Or.inr proof.right)
    exact absurd eval_phi eval_negphi
  case LRnegR φ =>
    simp at *
    have eval_phi : Evaluate (M, w) φ := by
      exact w_sat_LR φ (Or.inr proof.right)
    have eval_negphi : Evaluate (M, w) (~φ) := by
      exact w_sat_LR (~φ) (Or.inl proof.left)
    exact absurd eval_phi eval_negphi


/-
-- The critical rule is sound and preserves satisfiability "downwards".
-- NOTE: This is stronger than Lemma 1, but we do not need.
theorem atmSoundness {α : Finset Formula} {f} (not_box_f_in_a : ~(□f) ∈ α) :
    Satisfiable α → Satisfiable (projection α ∪ {~f}) :=
  by
  intro aSat
  unfold Satisfiable at aSat
  rcases aSat with ⟨W, M, w, w_sat_a⟩
  constructor
  simp
  -- get the other reachable world:
  let w_sat_not_box_f := w_sat_a (~f.box) not_box_f_in_a
  unfold Evaluate at w_sat_not_box_f
  simp at w_sat_not_box_f
  rcases w_sat_not_box_f with ⟨v, w_rel_v, v_not_sat_f⟩
  -- show that the projection is satisfiable:
  use M, v
  constructor
  · exact v_not_sat_f
  intro phi phi_in_proj
  rw [proj] at phi_in_proj
  · specialize w_sat_a phi.box _
    exact phi_in_proj
    unfold Evaluate at w_sat_a
    exact w_sat_a v w_rel_v
-/

theorem localTableauAndEndNodesUnsatThenNotSat {L R} (ltLR : LocalTableau L R) :
    (∀ Y, Y ∈ endNodesOf ⟨Z, ltZ⟩ → ¬Satisfiable Y) → ¬Satisfiable Z :=
  by
  intro endsOfXnotSat
  induction ltZ
  case byLocalRule X YS lr next IH =>
    by_contra satX
    rcases localRuleSoundness lr satX with ⟨Y, Y_in_YS, satY⟩
    specialize IH Y Y_in_YS
    set ltY := next Y Y_in_YS
    have endNodesInclusion :
      ∀ W, W ∈ endNodesOf ⟨Y, ltY⟩ → W ∈ endNodesOf ⟨X, LocalTableau.byLocalRule lr next⟩ :=
      by
      rw [endNodesOf]
      intro W W_endOF_Y
      simp only [endNodesOf, Finset.mem_biUnion, Finset.mem_attach, exists_true_left,
        Subtype.exists]
      use Y, Y_in_YS
    have endsOfYnotSat : ∀ Y_1 : Finset Formula, Y_1 ∈ endNodesOf ⟨Y, ltY⟩ → ¬Satisfiable Y_1 :=
      by
      intro W W_is_endOf_Y
      apply endsOfXnotSat W (endNodesInclusion W W_is_endOf_Y)
    aesop
  case sim X X_is_simple =>
    apply endsOfXnotSat
    unfold endNodesOf
    simp

theorem tableauThenNotSat : ∀ X, ClosedTableau X → ¬Satisfiable X :=
  by
  intro X t
  induction t
  case loc Y ltY _ IH =>
    apply localTableauAndEndNodesUnsatThenNotSat ltY
    intro Z ZisEndOfY
    exact IH Z ZisEndOfY
  case atm φ notBoxPhiInY Y_is_simple ltProYnPhi notSatProj =>
    rw [Lemma1_simple_sat_iff_all_projections_sat Y_is_simple]
    simp
    aesop

-- Theorem 2, page 30
theorem correctness : ∀ X, Satisfiable X → Consistent X :=
  by
  intro X
  contrapose
  unfold Consistent
  unfold Inconsistent
  simp only [not_nonempty_iff, not_isEmpty_iff, not_exists, not_forall, exists_prop, Nonempty.forall]
  intro hyp
  apply tableauThenNotSat X hyp

theorem soundTableau : ∀ φ, Provable φ → ¬Satisfiable ({~φ} : Finset Formula) :=
  by
  intro phi
  intro prov
  cases' prov with _ tabl
  apply tableauThenNotSat
  assumption

theorem soundness : ∀ φ, Provable φ → Tautology φ :=
  by
  intro φ prov
  apply notsatisfnotThenTaut
  rw [← singletonSat_iff_sat]
  apply soundTableau
  exact prov
