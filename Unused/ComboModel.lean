
-- UNUSED FILE !!

import Pdl.Star
import Pdl.Tableau

import Mathlib.Tactic.Ring

open HasSat

-- Combine a collection of pointed models with one new world using the given valuation.
-- TODO: rewrite to term mode?
def combinedModel {β : Type} (collection : β → Σ W : Type, Nat × KripkeModel W × W)
    (newVal : Nat → Prop) :
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
      rcases oldWorld with ⟨R, w⟩
      exact (collection R).snd.snd.fst.val w
  · -- defining relations:
    intro prog worldOne worldTwo
    cases worldOne <;> cases worldTwo -- four cases about two new or old worlds
    case inl.inl =>
      exact False -- no reflexive loop at the new world.
    case inl.inr newWorld oldWorld => -- connect new world to given points.
      exact (HEq oldWorld.snd (collection oldWorld.fst).snd.snd)
          ∧ (HEq prog (collection oldWorld.fst).snd.fst)
    case inr.inl => exact False -- no connection from old worlds to new world
    case inr.inr oldWorldOne oldWorldTwo =>
      -- connect two old worlds iff they are from the same model and were connected there already:
      rcases oldWorldOne with ⟨kOne, wOne⟩
      rcases oldWorldTwo with ⟨kTwo, wTwo⟩
      have help : kOne = kTwo → Prop := by
        intro same
        have sameCol : collection kOne = collection kTwo := by rw [← same]
        rw [← sameCol] at wTwo
        exact (collection kOne).snd.snd.fst.Rel prog wOne wTwo
      classical
      exact dite (kOne = kTwo) (fun same => help same) fun _ => False
  · -- point at the new world:
    left
    exact ()


theorem combMo_preserves_truth_at_oldWOrld {β : Type}
    (collection : β → Σ W : Type, Nat × KripkeModel W × W) (newVal : Nat → Prop) :
    ∀ (f : Formula) (R : β) (oldWorld : (collection R).fst),
      evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) f ↔
        evaluate (collection R).snd.snd.fst oldWorld f :=
    by
    intro mF mR moW
    apply @Formula.rec
      (fun φ => ∀ (R : β) (oldWorld : (collection R).fst),  -- Formula IH
        evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) φ ↔
          evaluate (collection R).snd.snd.fst oldWorld φ)
      -- Program IH 1: relations within models are preserved
      (fun π => (∀ (R : β) (oldWorld₁ oldWorld₂ : (collection R).fst),
          relate (combinedModel collection newVal).fst π
            (Sum.inr ⟨R, oldWorld₁⟩) (Sum.inr ⟨R, oldWorld₂⟩)
        ↔ relate (collection R).snd.snd.fst π oldWorld₁ oldWorld₂)
            -- Program IH 2: if old worlds are from different models they are not related
            ∧ (∀ (R₁ R₂ : β) (oldWorld₁ : (collection R₁).fst) (oldWorld₂ : (collection R₂).fst),
              R₁ ≠ R₂ →
                ¬(relate (combinedModel collection newVal).fst π
                    (Sum.inr ⟨R₁, oldWorld₁⟩) (Sum.inr ⟨R₂, oldWorld₂⟩)))
              -- Program IH 3: no old world can see the new world
              ∧ (∀ (R : β) (oldWorld : (collection R).fst),
                ¬(relate (combinedModel collection newVal).fst π
                    (Sum.inr ⟨R, oldWorld⟩) (Sum.inl Unit.unit))))
      (by simp)       -- case bottom
      (by aesop)      -- case atom_prop
      (by aesop)      -- case neg
      (by aesop)      -- case and
      ( by            -- case box
          intro α f IH_a IH_f R oldWorld
          constructor
          · sorry -- aesop
          · intro true_in_old
            unfold evaluate at true_in_old
            simp
            constructor
            · intro newWorld old_rel_new
              absurd old_rel_new
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
            · rintro ⟨otherR, otherWorld⟩ rel_in_new_model
              specialize IH_f otherR otherWorld
              simp_all
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              specialize sameR R otherR oldWorld otherWorld
              simp_all
              subst sameR
              aesop
      )
      ( by          -- case atom_prog
          intro a
          constructor
          · intro R oldWorld₁ oldWorld₂    -- first half of Program IH
            constructor <;>
            ( intro new_rel
              unfold relate at *
              unfold KripkeModel.Rel at *
              unfold combinedModel at *
              aesop
            )
          · unfold combinedModel at *; aesop   -- second half of Program IH
      )
      ( by          -- case sequence
          intro a b IH_a IH_b
          constructor
          · intro R oldWorld₁ oldWorld₂          -- first half of Program IH
            constructor
            · intro new_rel
              unfold relate at new_rel
              rcases new_rel with ⟨u, a_rel_u, u_rel_b⟩
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              rcases u with u_new|u_old
              · absurd a_rel_u
                apply noNewL
              · rcases u_old with ⟨otherR, otherWorld⟩ -- old world
                specialize sameR R otherR oldWorld₁ otherWorld
                simp_all
                subst sameR
                aesop
            · intro old_rel
              unfold relate at old_rel
              unfold relate
              rcases old_rel with ⟨u, a_rel_u, u_rel_b⟩
              use (Sum.inr ⟨R, u⟩)
              aesop
          constructor
          · intro R₁ R₂ oldWorld₁ oldWorld₂ hneq hrel     -- second half of Program IH
            unfold relate at hrel
            rcases hrel with ⟨u, a_rel_u, _⟩
            rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
            rcases u with u_new|u_old
            · absurd a_rel_u
              apply noNewL
            · rcases u_old with ⟨otherR, otherWorld⟩ -- old world
              specialize sameR R₁ otherR oldWorld₁ otherWorld
              simp_all
          · intro R oldWorld
            unfold relate
            rintro ⟨u, a_rel_to_u, b_rel_u_to⟩
            cases u
            · absurd a_rel_to_u
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
            · absurd b_rel_u_to
              rcases IH_b with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
      )
      (by aesop)       -- case union
      (by              -- case star
        intro a IH_a
        constructor
        · intro R oldWorld₁ oldWorld₂                  -- first half of Program IH
          have star_preserved : ∀ (w v : (collection R).fst),
              Relation.ReflTransGen
                (relate (combinedModel collection newVal).fst a) (Sum.inr ⟨R, w⟩) (Sum.inr ⟨R, v⟩)
            ↔ Relation.ReflTransGen (relate (collection R).snd.snd.fst a) w v :=
            by
            intro w v
            rw [ReflTransGen.iff_finitelyManySteps]
            rw [ReflTransGen.iff_finitelyManySteps]
            -- alternatively, use @Relation.ReflTransGen.head_induction_on here?
            sorry
          constructor <;> aesop
        constructor
        · intro R₁ R₂ oldWorld₁ oldWorld₂ hneq        -- second half of Program IH
          unfold relate
          rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
          specialize sameR R₁ R₂ oldWorld₁ oldWorld₂ hneq
          sorry -- again @Relation.ReflTransGen.head_induction_on
        · intro R oldWorld
          unfold relate
          intro star_rel
          cases ReflTransGen.cases_tail_eq_neq star_rel
          case inl hyp => simp at hyp
          case inr hyp =>
            rcases hyp.2 with ⟨u, _neq_u, a_rel_to_u, b_rel_u_to⟩
            cases u
            · absurd a_rel_to_u
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
            · absurd b_rel_u_to
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              sorry -- apply noNewL -- not working, need induction?
      )
      (by aesop)       -- case test
      (mF)


/-
-- The combined model for X satisfies X.
theorem combMo_sat_LR {L R : Finset Formula} {β : Set Formula}
    {beta_def : β = {F : Formula | f_in_TNode (~F.box) (L, R)}}
    (simple_LR : Simple (L, R)) (not_closed_LR : ¬ closed (L ∪ R))
    (collection : β → Σ W : Type, KripkeModel W × W)
    (all_pro_sat :
      ∀ F : β,
        ∀ f, (f ∈ (projection (L ∪ R) ∪ {~F}))
          → evaluate ((collection F).snd.fst, (collection F).snd.snd) f) :
    ∀ f, f_in_TNode f (L, R)
      → evaluate
        ((combinedModel collection fun c => Formula.atom_prop c ∈ (L ∪ R)).fst,
          (combinedModel collection fun c => Formula.atom_prop c ∈ (L ∪ R)).snd)
        f :=
  by
    intro f f_in_LR
    unfold Simple SimpleSet at simple_LR
    simp at simple_LR
    simp at f_in_LR
    rw [←Finset.mem_union] at f_in_LR
    cases f
    -- no induction because (L, R) is simple
    case bottom =>
      unfold closed at not_closed_LR
      aesop
    case atom_prop =>
      unfold combinedModel
      unfold Evaluate
      aesop
    case
      neg f =>
      -- subcases :
      cases f
      case atom_prop =>
        unfold combinedModel
        unfold Evaluate
        unfold closed at not_closed_LR
        rw [not_or] at not_closed_LR
        aesop
      case box f =>
        -- set coMo := ,
        simp only [Evaluate, not_forall]
        -- need reachable world with ~f, use the β-witness
        let h : f ∈ β := by rw [beta_def]; use f_in_LR
        let oldWorld : Sum Unit (Σ k : β, (collection k).fst) :=
          Sum.inr ⟨⟨f, h⟩, (collection ⟨f, h⟩).snd.snd⟩
        use oldWorld
        constructor
        · -- show that f is false at old world
          have coMoLemma :=
            combMo_preserves_truth_at_oldWOrld collection (fun c : Nat => (·c) ∈ (L ∪ R)) f ⟨f, h⟩
              (collection ⟨f, h⟩).snd.snd
          rw [coMoLemma]
          specialize all_pro_sat ⟨f, h⟩ (~f)
          unfold Evaluate at all_pro_sat
          simp at *
          exact all_pro_sat
        ·-- show that worlds are related in combined model (def above, case 2)
          unfold combinedModel
          simp
      case bottom => tauto
      case neg f =>
        rw [Finset.mem_union] at f_in_LR
        cases f_in_LR
        case inl hyp =>
          have := simple_LR.1 (~~f) hyp
          simp at this
        case inr hyp =>
          have := simple_LR.2 (~~f) hyp
          simp at this
      case And f g =>
        rw [Finset.mem_union] at f_in_LR
        cases f_in_LR
        case inl hyp =>
          have := simple_LR.1 (~(f⋀g)) hyp
          simp at this
        case inr hyp =>
          have := simple_LR.2 (~(f⋀g)) hyp
          simp at this
    case And fa fb =>
      rw [Finset.mem_union] at f_in_LR
      cases f_in_LR
      case inl hyp =>
        have := simple_LR.1 (fa⋀fb) hyp
        simp at this
      case inr hyp =>
        have := simple_LR.2 (fa⋀fb) hyp
        simp at this
    case box f =>
      unfold Evaluate
      intro otherWorld is_rel
      cases otherWorld
      · cases is_rel
      case inr otherWorld => -- otherWorld cannot be the (unreachable) new world
        have coMoLemma :=
          combMo_preserves_truth_at_oldWOrld collection (fun c => (·c) ∈ (L ∪ R)) f otherWorld.fst
            otherWorld.snd
        rw [coMoLemma]
        specialize all_pro_sat otherWorld.fst f
        simp at all_pro_sat
        rw [or_imp] at all_pro_sat
        cases' all_pro_sat with _ all_pro_sat_right
        rw [←proj] at f_in_LR
        simp at *
        specialize all_pro_sat_right f_in_LR
        have sameWorld : otherWorld.snd = (collection otherWorld.fst).snd.snd := by
          rw [heq_iff_eq.mp (HEq.symm is_rel)]
        rw [sameWorld]
        exact all_pro_sat_right


-- Lemma 1 (page 16)
-- A simple set of formulas X is satisfiable if and only if
-- it is not closed  and  for all ¬[A]R ∈ X also XA; ¬R is satisfiable.
theorem Lemma1_simple_sat_iff_all_projections_sat {LR : TNode} :
    Simple LR → (satisfiable LR ↔
      ¬closed (LR.1 ∪ LR.2) ∧ ∀ F, f_in_TNode (~(□F)) LR
        → satisfiable (projection (LR.1 ∪ LR.2) ∪ {~F})) :=
  by
    intro LR_is_simple
    constructor
    · -- left to right
      intro sat_LR
      unfold satisfiable at *
      rcases sat_LR with ⟨W, M, w, w_sat_LR⟩
      constructor
      · -- show that X is not closed:
        by_contra hyp
        unfold closed at hyp
        cases' hyp with bot_in_LR f_and_notf_in_LR
        · exact w_sat_LR ⊥ bot_in_LR
        · rcases f_and_notf_in_LR with ⟨f, f_in_LR, notf_in_LR⟩
          let w_sat_f := w_sat_LR f f_in_LR
          let w_sat_notf := w_sat_LR (~f) notf_in_LR
          exact absurd w_sat_f w_sat_notf
      · -- show that for each ~[]R ∈ X the projection with ~R is satisfiable:
        intro R notboxr_in_LR
        let w_sat_notboxr := w_sat_LR (~(□R)) notboxr_in_LR
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
        · intro boxg_in_LR
          repeat rw [proj] at boxg_in_LR
          rw [←Finset.mem_union]at boxg_in_LR
          specialize w_sat_LR (□g)
          aesop
    · -- right to left
      intro rhs
      cases' rhs with not_closed_LR all_pro_sat
      unfold satisfiable at *
      -- Let's build a new Kripke model!
      let (L, R) := LR
      let β := {F : Formula | f_in_TNode (~(□F)) (L, R)}
      -- beware, using Axioms of Choice here!
      choose typeFor this_pro_sat using all_pro_sat
      choose modelFor this_pro_sat using this_pro_sat
      choose worldFor this_pro_sat using this_pro_sat
      -- define the collection:
      let collection : β → Σ W : Type, KripkeModel W × W :=
        by
        intro k
        cases' k with R notboxr_in_LR
        use typeFor R notboxr_in_LR, modelFor R notboxr_in_LR, worldFor R notboxr_in_LR
      let newVal c := f_in_TNode (Formula.atom_prop c) (L, R)
      let BigM := combinedModel collection newVal
      use Sum Unit (Σ k : β, (collection k).fst)
      use BigM.fst, BigM.snd
      -- apply Lemma, missing last argument "all_pro_sat"
      -- we need to use that X_is_simple (to restrict cases what phi can be)
      -- and that X is not closed (to ensure that it is locally consistent)
      apply combMo_sat_LR LR_is_simple not_closed_LR collection
      -- it remains to show that the new big model satisfies X
      intro R f f_inpro_or_notr
      cases' R with R notrbox_in_LR
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Subtype.coe_mk] at *
      specialize this_pro_sat R notrbox_in_LR
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

-/
