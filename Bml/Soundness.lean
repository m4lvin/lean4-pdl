-- SOUNDNESS
import Syntax
import Tableau

#align_import soundness

open Classical

attribute [local instance 10] prop_decidable

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
    · -- the one new world:
      cases world
      exact newVal
    -- use new given valuation here!!
    · -- world in one of the given models:
      cases' world with R w
      exact (collection R).snd.fst.val w
  · -- defining relations:
    intro worldOne worldTwo
    cases worldOne <;> cases worldTwo
    -- four cases about two new or old worlds:
    · exact False
    -- no reflexive loop at the new world.
    · exact HEq worldTwo.snd (collection worldTwo.fst).snd.snd
    -- conect new world to given points.
    · exact False
    -- no connection from models to new world
    · -- connect two old worlds iff they are from the same model and were connected there already:
      cases' worldOne with kOne wOne
      cases' worldTwo with kTwo wTwo
      have help : kOne = kTwo → Prop := by
        intro same
        have sameCol : collection kOne = collection kTwo := by rw [← same]
        rw [← sameCol] at wTwo 
        exact (collection kOne).snd.fst.Rel wOne wTwo
      exact dite (kOne = kTwo) (fun same => help same) fun _ => False
  · -- point at the new world:
    left
    exact ()
#align combinedModel combinedModel

-- The combined model preserves all truths at the old worlds.
theorem combMo_preserves_truth_at_oldWOrld {β : Type}
    (collection : β → Σ W : Type, KripkeModel W × W) (newVal : Char → Prop) :
    ∀ (f : Formula) (R : β) (oldWorld : (collection R).fst),
      Evaluate ((combinedModel collection newVal).fst, Sum.inr ⟨R, oldWorld⟩) f ↔
        Evaluate ((collection R).snd.fst, oldWorld) f :=
  by
  intro f
  induction f <;> intro R oldWorld
  case bottom => finish
  case atom_prop c =>
    unfold combinedModel
    unfold Evaluate
  case neg f f_IH =>
    unfold Evaluate
    rw [f_IH R oldWorld]
  case and f g f_IH g_IH =>
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
          classical finish
        subst sameR
        rw [f_IH]
        apply true_in_old
        -- remains to show that related in old model
        simp at *
        exact rel_in_new_model
#align combMo_preserves_truth_at_oldWOrld combMo_preserves_truth_at_oldWOrld

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
    neg =>
    -- subcases :-/
    cases f
    case atom_prop =>
      unfold combinedModel
      unfold Evaluate
      unfold Closed at not_closed_X 
      rw [not_or] at not_closed_X 
      simp at *
      tauto
    case box
      newf =>
      -- set coMo := ,
      --unfold combinedModel,
      change
        Evaluate
          ((combinedModel collection fun c => (·c) ∈ X).fst,
            (combinedModel collection fun c : Char => (·c) ∈ X).snd)
          (~(□newf))
      unfold Evaluate
      rw [Classical.not_forall]
      -- need a reachable world where newf holds, choose the witness
      let h : newf ∈ β := by
        rw [beta_def]
        use f_in_X
      let oldWorld : Sum Unit (Σ k : β, (collection k).fst) :=
        Sum.inr ⟨⟨newf, h⟩, (collection ⟨newf, h⟩).snd.snd⟩
      use oldWorld
      simp
      constructor
      ·-- show that worlds are related in combined model (def above, case 2)
        unfold combinedModel;
        simp
      · -- show that f is false at old world
        have coMoLemma :=
          combMo_preserves_truth_at_oldWOrld collection (fun c : Char => (·c) ∈ X) newf ⟨newf, h⟩
            (collection ⟨newf, h⟩).snd.snd
        rw [coMoLemma]
        specialize all_pro_sat ⟨newf, h⟩ (~newf)
        unfold Evaluate at all_pro_sat 
        simp at *
        exact all_pro_sat
    case bottom => tauto
    all_goals
      unfold Simple at simple_X 
      by_contra
      exact simple_X _ f_in_X
  case and fa fb =>
    unfold Simple at simple_X 
    by_contra
    exact simple_X (fa⋏fb) f_in_X
  case box f =>
    unfold Evaluate
    intro otherWorld is_rel
    cases otherWorld
    · cases is_rel
    -- otherWorld cannot be the (unreachable) new world
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
#align combMo_sat_X combMo_sat_X

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
    unfold satisfiable at *
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
        unfold Evaluate at *
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
    unfold satisfiable at *
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
      specialize this_pro_sat (~R)
      rw [or_imp] at this_pro_sat 
      cases' this_pro_sat with this_pro_sat_l this_pro_sat_r
      exact this_pro_sat_r f_is_notboxR
    simp
#align Lemma1_simple_sat_iff_all_projections_sat Lemma1_simple_sat_iff_all_projections_sat

-- to check β
-- Each rule is sound and preserves satisfiability "downwards"
theorem localRuleSoundness {α : Finset Formula} {B : Finset (Finset Formula)} :
    LocalRule α B → Satisfiable α → ∃ β ∈ B, Satisfiable β :=
  by
  intro r
  intro a_sat
  unfold satisfiable at a_sat 
  rcases a_sat with ⟨W, M, w, w_sat_a⟩
  cases r
  case bot a bot_in_a =>
    by_contra
    let w_sat_bot := w_sat_a ⊥ bot_in_a
    unfold Evaluate at w_sat_bot 
    exact w_sat_bot
  case not a f hyp =>
    by_contra
    have w_sat_f : Evaluate (M, w) f := by
      apply w_sat_a
      exact hyp.left
    have w_sat_not_f : Evaluate (M, w) (~f) :=
      by
      apply w_sat_a (~f)
      exact hyp.right
    unfold Evaluate at *
    exact absurd w_sat_f w_sat_not_f
  case neg a f
    hyp =>
    have w_sat_f : Evaluate (M, w) f :=
      by
      specialize w_sat_a (~~f) hyp
      unfold Evaluate at *
      finish
    use a \ {~~f} ∪ {f}
    simp only [true_and_iff, eq_self_iff_true, sdiff_singleton_is_erase, Multiset.mem_singleton,
      Finset.mem_mk]
    unfold satisfiable
    use W, M, w
    intro g
    simp only [Ne.def, union_singleton_is_insert, Finset.mem_insert, Finset.mem_erase]
    rw [or_imp]
    constructor
    · intro g_is_f; rw [g_is_f]; apply w_sat_f
    · rw [and_imp]
      intro g_neq_notnotf g_in_a
      apply w_sat_a
      exact g_in_a
  case con a f g hyp =>
    use a \ {f⋏g} ∪ {f, g}
    constructor
    simp
    unfold satisfiable
    use W, M, w
    simp only [and_imp, forall_eq_or_imp, sdiff_singleton_is_erase, Ne.def, Finset.union_insert,
      Finset.mem_insert, Finset.mem_erase]
    constructor
    · -- f
      specialize w_sat_a (f⋏g) hyp
      unfold Evaluate at *
      exact w_sat_a.left
    · intro h hhyp
      simp at hhyp 
      cases hhyp
      · -- h = g
        specialize w_sat_a (f⋏g) hyp
        unfold Evaluate at *
        rw [hhyp]
        exact w_sat_a.right
      ·-- h in a
        exact w_sat_a h hhyp.right
  case nCo a f g notfandg_in_a =>
    unfold satisfiable
    simp
    let w_sat_phi := w_sat_a (~(f⋏g)) notfandg_in_a
    unfold Evaluate at w_sat_phi 
    rw [not_and_or] at w_sat_phi 
    cases' w_sat_phi with not_w_f not_w_g
    · use a \ {~(f⋏g)} ∪ {~f}
      constructor
      · simp at *
      · use W, M, w
        intro psi
        simp
        intro psi_def
        cases psi_def
        · rw [psi_def]
          unfold Evaluate
          exact not_w_f
        · cases' psi_def with psi_in_a
          exact w_sat_a psi psi_def_right
    · use a \ {~(f⋏g)} ∪ {~g}
      constructor
      · simp at *
      · use W, M, w
        intro psi
        simp
        intro psi_def
        cases psi_def
        · rw [psi_def]
          unfold Evaluate
          exact not_w_g
        · cases' psi_def with psi_in_a
          exact w_sat_a psi psi_def_right
#align localRuleSoundness localRuleSoundness

-- The critical roule is sound and preserves satisfiability "downwards".
-- TODO: is this the same as (one of the directions of) Lemma 1 ??
theorem atmSoundness {α : Finset Formula} {f} (not_box_f_in_a : ~(□f) ∈ α) :
    Simple α → Satisfiable α → Satisfiable (projection α ∪ {~f}) :=
  by
  intro s
  intro aSat
  unfold satisfiable at aSat 
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
  · unfold Evaluate
    exact v_not_sat_f
  intro phi phi_in_proj
  rw [proj] at phi_in_proj 
  · specialize w_sat_a phi.box _
    exact phi_in_proj
    unfold Evaluate at w_sat_a 
    exact w_sat_a v w_rel_v
#align atmSoundness atmSoundness

theorem localTableauAndEndNodesUnsatThenNotSat {Z} (ltZ : LocalTableau Z) :
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
      assumption
    have endsOfYnotSat : ∀ Y_1 : Finset Formula, Y_1 ∈ endNodesOf ⟨Y, ltY⟩ → ¬satisfiable Y_1 :=
      by
      intro W W_is_endOf_Y
      apply endsOfXnotSat W (endNodesInclusion W W_is_endOf_Y)
    finish
  case sim X X_is_simple =>
    apply endsOfXnotSat
    unfold endNodesOf
    simp
#align localTableauAndEndNodesUnsatThenNotSat localTableauAndEndNodesUnsatThenNotSat

theorem tableauThenNotSat : ∀ X, ClosedTableau X → ¬Satisfiable X :=
  by
  intro X t
  induction t
  case loc Y ltY next IH =>
    apply localTableauAndEndNodesUnsatThenNotSat ltY
    intro Z ZisEndOfY
    exact IH Z ZisEndOfY
  case atm Y ϕ notBoxPhiInY Y_is_simple
    ltProYnPhi =>
    rw [Lemma1_simple_sat_iff_all_projections_sat Y_is_simple]
    simp
    intro Ynotclosed
    use ϕ
    use notBoxPhiInY
    finish
#align tableauThenNotSat tableauThenNotSat

-- Theorem 2, page 30
theorem correctness : ∀ X, Satisfiable X → Consistent X :=
  by
  intro X
  contrapose
  unfold Consistent
  simp
  unfold Inconsistent
  intro hyp
  cases' hyp with t
  exact tableauThenNotSat X t
#align correctness correctness

theorem soundTableau : ∀ φ, Provable φ → ¬Satisfiable ({~φ} : Finset Formula) :=
  by
  intro phi
  intro prov
  cases' prov with _ tabl
  apply tableauThenNotSat
  exact tabl
#align soundTableau soundTableau

theorem soundness : ∀ φ, Provable φ → Tautology φ :=
  by
  intro φ prov
  apply notsatisfnotThenTaut
  rw [← singletonSat_iff_sat]
  apply soundTableau
  exact prov
#align soundness soundness

