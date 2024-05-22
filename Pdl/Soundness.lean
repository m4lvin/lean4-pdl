-- SOUNDNESS

import Pdl.Tableau

import Mathlib.Tactic.Ring

open Classical

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
      cases' oldWorld with R w
      exact (collection R).snd.snd.fst.val w
  · -- defining relations:
    intro prog worldOne worldTwo
    cases worldOne <;> cases worldTwo -- four cases about two new or old worlds
    case inl.inl =>
      exact False -- no reflexive loop at the new world.
    case inl.inr newWorld oldWorld => -- connect new world to given points.
      exact (HEq oldWorld.snd (collection oldWorld.fst).snd.snd) ∧ (HEq prog (collection oldWorld.fst).snd.fst)
    case inr.inl => exact False -- no connection from old worlds to new world
    case inr.inr oldWorldOne oldWorldTwo =>
      -- connect two old worlds iff they are from the same model and were connected there already:
      cases' oldWorldOne with kOne wOne
      cases' oldWorldTwo with kTwo wTwo
      have help : kOne = kTwo → Prop := by
        intro same
        have sameCol : collection kOne = collection kTwo := by rw [← same]
        rw [← sameCol] at wTwo
        exact (collection kOne).snd.snd.fst.Rel prog wOne wTwo
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
      (λφ => ∀ (R : β) (oldWorld : (collection R).fst),  -- Formula IH
        evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) φ ↔
          evaluate (collection R).snd.snd.fst oldWorld φ)
      -- Program IH 1: relations within models are preserved
      (λπ => (∀ (R : β) (oldWorld₁ oldWorld₂ : (collection R).fst),
        relate (combinedModel collection newVal).fst π (Sum.inr ⟨R, oldWorld₁⟩) (Sum.inr ⟨R, oldWorld₂⟩) ↔
          relate (collection R).snd.snd.fst π oldWorld₁ oldWorld₂)
            -- Program IH 2: if old worlds are from different models they are not related
            ∧ (∀ (R₁ R₂ : β) (oldWorld₁ : (collection R₁).fst) (oldWorld₂ : (collection R₂).fst),
              R₁ ≠ R₂ → ¬(relate (combinedModel collection newVal).fst π (Sum.inr ⟨R₁, oldWorld₁⟩) (Sum.inr ⟨R₂, oldWorld₂⟩)))
              -- Program IH 3: no old world can see the new world
              ∧ (∀ (R : β) (oldWorld : (collection R).fst),
                ¬(relate (combinedModel collection newVal).fst π (Sum.inr ⟨R, oldWorld⟩) (Sum.inl Unit.unit))))
      (by tauto)      -- case bottom
      (by aesop)      -- case atom_prop
      (by aesop)      -- case neg
      (by aesop)      -- case and
      ( by            -- case box
          intro α f IH_a IH_f R oldWorld
          constructor
          · aesop
          · intro true_in_old
            unfold evaluate at true_in_old
            simp
            constructor
            · intro newWorld  -- new world
              intro old_rel_new
              absurd old_rel_new
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
            · intro otherR otherWorld  -- old world
              intro rel_in_new_model
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
              cases' u with u_new u_old
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
            cases' u with u_new u_old
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
            Relation.ReflTransGen (relate (combinedModel collection newVal).fst a)
              (Sum.inr ⟨R, w⟩) (Sum.inr ⟨R, v⟩) ↔ Relation.ReflTransGen (relate (collection R).snd.snd.fst a) w v :=
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
    {beta_def : β = {F : Formula | f_in_TNode (~F.box) (L, R)}} (simple_LR : Simple (L, R)) (not_closed_LR : ¬Closed (L ∪ R))
    (collection : β → Σ W : Type, KripkeModel W × W)
    (all_pro_sat :
      ∀ F : β,
        ∀ f, (f ∈ (projection (L ∪ R) ∪ {~F})) → Evaluate ((collection F).snd.fst, (collection F).snd.snd) f) :
    ∀ f, f_in_TNode f (L, R)
      → Evaluate
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
      unfold Closed at not_closed_LR
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
        unfold Closed at not_closed_LR
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
    Simple LR → (Satisfiable LR ↔ ¬Closed (LR.1 ∪ LR.2) ∧ ∀ F, f_in_TNode (~(□F)) LR → Satisfiable (projection (LR.1 ∪ LR.2) ∪ {~F})) :=
  by
    intro LR_is_simple
    constructor
    · -- left to right
      intro sat_LR
      unfold Satisfiable at *
      rcases sat_LR with ⟨W, M, w, w_sat_LR⟩
      constructor
      · -- show that X is not closed:
        by_contra hyp
        unfold Closed at hyp
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
      unfold Satisfiable at *
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


-- * Tools for saying that different kinds of formulas are in a TNode

@[simp]
instance : Membership Formula TNode :=
  ⟨fun φ X => φ ∈ X.L ∨ φ ∈ X.R⟩

@[simp]
def NegLoadFormula_in_TNode := fun nlf (X : TNode) => X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

@[simp]
instance NegLoadFormula.HasMem_TNode : Membership NegLoadFormula TNode := ⟨NegLoadFormula_in_TNode⟩

def AnyFormula := Sum Formula LoadFormula

inductive AnyNegFormula
| neg : AnyFormula → AnyNegFormula

local notation "~''" φ:arg => AnyNegFormula.neg φ

@[simp]
instance modelCanSemImplyAnyNegFormula {W : Type} : vDash (KripkeModel W × W) AnyNegFormula :=
  vDash.mk (λ ⟨M,w⟩ af => match af with
   | ⟨Sum.inl f⟩ => evaluate M w f
   | ⟨Sum.inr f⟩ => evaluate M w (unload f)
   )

@[simp]
def anyNegLoad : Program → AnyFormula → NegLoadFormula
| α, Sum.inl φ => ~'⌊α⌋φ
| α, Sum.inr χ => ~'⌊α⌋χ

local notation "~'⌊" α "⌋" χ => anyNegLoad α χ

-- set_option trace.Meta.synthInstance true -- turn this on to debug ∈ below.
@[simp]
def AnyNegFormula_in_TNode := fun (anf : AnyNegFormula) (X : TNode) => match anf with
| ⟨Sum.inl φ⟩ => (~φ) ∈ X
| ⟨Sum.inr χ⟩ => NegLoadFormula_in_TNode (~'χ) X -- FIXME: ∈ not working here

@[simp]
instance : Membership AnyNegFormula TNode := ⟨AnyNegFormula_in_TNode⟩

-- * Helper functions, to be moved to (Local)Tableau.lean

-- TODO Computable version possible?
noncomputable def endNode_to_endNodeOfChildNonComp (lrA)
  (E_in: E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  @Subtype TNode (fun x => ∃ h, E ∈ endNodesOf (subTabs x h)) := by
  simp [endNodesOf] at E_in
  choose l h E_in using E_in
  choose c c_in l_eq using h
  subst l_eq
  use c
  use c_in

theorem endNodeIsEndNodeOfChild (lrA)
  (E_in: E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  ∃ Y h, E ∈ endNodesOf (subTabs Y h) := by
  have := endNode_to_endNodeOfChildNonComp lrA E_in
  use this
  aesop

theorem endNodeOfChild_to_endNode
    {X Y: TNode}
    {ltX}
    {C : List TNode}
    (lrA : LocalRuleApp X C)
    subTabs
    (h : ltX = LocalTableau.byLocalRule lrA subTabs)
    (Y_in : Y ∈ C)
    {Z : TNode}
    (Z_in: Z ∈ endNodesOf (subTabs Y Y_in))
    : Z ∈ endNodesOf ltX :=
  by
  cases h' : subTabs Y Y_in -- No induction needed for this!
  case sim Y_isSimp =>
    subst h
    simp
    use endNodesOf (subTabs Y Y_in)
    constructor
    · use Y, Y_in
    · exact Z_in
  case byLocalRule C' subTabs' lrA' =>
    subst h
    rw [h'] at Z_in
    simp
    use endNodesOf (subTabs Y Y_in)
    constructor
    · use Y, Y_in
    · rw [h']
      exact Z_in

-- * Navigating through tableaux

-- Given our representation of condition 6a, now we want to prove MB Lemma 7.
--
-- To represent both the whole Tableau and a specific node in it we use
-- a "List TNode" path to say "go to this child, then to this child, etc."
-- These paths:
-- - can go through/across multiple LocalTableau, like LHistories
--   and unlike the Paths used in the Complteness Proof
-- - are over the relation that includes back-loops.

-- TODO: Replace the "unsafe" list paths with inductive types
--       See the toy examples and experiments in "Repeat.lean".

inductive PathInLocal {X} : LocalTableau X → Type
-- TODO

inductive PathIn {H X} : ClosedTableau H X → Type
-- TODO

-- Definition of ◃' in a tableu, successor + back loops
-- MB: page 26
def edgesBack {H X} {ctX : ClosedTableau H X} : PathIn ctX → PathIn ctX → Prop := sorry -- TODO

notation pa:arg "◃'" pb:arg => edgesBack pa pb

-- TODO: ≤' should be the refl-tran closure of ◃'


-- Given:
-- - a local tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the TNode at the end of the path or a local end node and the remaining path
-- TOOD: rewrite with more match cases in term mode without "by"?
def nodeInLocalAt (ltX : LocalTableau X) : List TNode → Option (TNode ⊕ (Subtype (fun Y => Y ∈ endNodesOf ltX) × List TNode))
| [] => some (Sum.inl X) -- we have reached the destination
| (Y::rest) => by
    cases ltX
    case byLocalRule B lnext lrApp =>
      refine if Y_in : Y ∈ B then ?_ else ?_
      · cases nodeInLocalAt (lnext Y Y_in) rest -- make a recursive call!
        case none => exact none -- not found.
        case some foo =>
          cases foo
          case inl Z =>
            exact some (Sum.inl Z) -- found it!
          case inr Z_ =>
            rcases Z_ with ⟨⟨Z,Z_in⟩, remainder⟩
            apply some
            apply Sum.inr
            refine ⟨⟨Z, ?_⟩, ?_⟩
            · apply endNodeOfChild_to_endNode lrApp lnext rfl Y_in Z_in
            · exact remainder
      · exact none -- cannot follow path
    case sim X_simp =>
      apply some
      apply Sum.inr
      constructor
      · use X
        rw [endNodesOf, List.mem_singleton]
      · exact Y::rest -- Problem: This case means "reminder" may be of same length still.

-- Given:
-- - a tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the TNode at the end of the path
def nodeInAt : (Σ X HistX, ClosedTableau HistX X) → List TNode → Option TNode
| ⟨X, hX, tab⟩, [] => some X -- we have reached the destination
| ⟨X, hX, tab⟩, (Y::rest) => by
      cases tab
      case loc ltX next =>
        cases nodeInLocalAt ltX (Y::rest)
        case none => exact none
        case some lt_res =>
          cases lt_res
          case inl Z => exact some Z -- reached end of path inside the local tableau.
          case inr Y_end_remainder =>
            rcases Y_end_remainder with ⟨⟨Y, Y_in⟩, remainder⟩
            have : remainder.length < (Y::rest).length := sorry -- needed for termination, may need to add this in tabInLocalAt
            exact nodeInAt ⟨Y, hX, next Y Y_in⟩ remainder
      case mrkL =>
        -- apply nodeInAt ?
        sorry
      case rep isRep =>
        exact none -- fail, we cannot go to Y (and should be using Loopy from below!)
      all_goals sorry
termination_by
   Xhtab toWalk => toWalk.length

-- Given:
-- - a local tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the local tableau at the end of the path or a local end node and the remaining path
-- TOOD: rewrite with more match cases in term mode without "by"?
def tabInLocalAt (ltX : LocalTableau X) : List TNode → Option ((Σ Z, LocalTableau Z) ⊕ (Subtype (fun Y => Y ∈ endNodesOf ltX) × List TNode))
| [] => some (Sum.inl ⟨X, ltX⟩) -- we have reached the destination
| (Y::rest) => by
    cases ltX
    case byLocalRule B lnext lrApp =>
      refine if Y_in : Y ∈ B then ?_ else ?_
      · cases tabInLocalAt (lnext Y Y_in) rest -- make a recursive call!
        case none => exact none -- not found.
        case some foo =>
          cases foo
          case inl Z =>
            exact some (Sum.inl Z) -- found it!
          case inr Z_ =>
            rcases Z_ with ⟨⟨Z,Z_in⟩, remainder⟩
            apply some
            apply Sum.inr
            refine ⟨⟨Z, ?_⟩, ?_⟩
            · apply endNodeOfChild_to_endNode lrApp lnext rfl Y_in Z_in
            · exact remainder
      · exact none -- cannot follow path
    case sim X_simp =>
      apply some
      apply Sum.inr
      constructor
      · use X
        rw [endNodesOf, List.mem_singleton]
      · exact Y::rest -- Problem: This case means "reminder" may be of same length still.

-- Given:
-- - a tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the closed tableau at the end of the path
def tabInAt : (Σ X HistX, ClosedTableau HistX X) → List TNode → Option (Σ Y HistY, ClosedTableau HistY Y)
| ⟨X, hX, tab⟩, [] => some ⟨X, hX, tab⟩ -- we have reached the destination
| ⟨X, hX, tab⟩, (Y::rest) => by
      cases tab
      case loc ltX next =>
        cases tabInLocalAt ltX (Y::rest)
        case none => exact none
        case some lt_res =>
          cases lt_res
          case inl Z_ltZ =>
            -- reached end of path inside the local tableau.
            rcases Z_ltZ with ⟨Z, ltZ⟩
            let ctZnext : (W : TNode) → W ∈ endNodesOf ltZ → ClosedTableau hX W :=
              fun W W_in => next _ sorry -- Need: endNnodesOf ltZ ⊆ endNnodesOf ltX
            let ctZ : ClosedTableau _ Z := ClosedTableau.loc ltZ ctZnext
            exact some ⟨Z, _, ctZ⟩
          case inr Y_end_remainder =>
            rcases Y_end_remainder with ⟨⟨Y, Y_in⟩, remainder⟩
            have : remainder.length < (Y::rest).length := sorry -- needed for termination, may need to add this in tabInLocalAt
            exact tabInAt ⟨Y, hX, next Y Y_in⟩ remainder
      case mrkL =>
        -- apply tabInAt ?
        sorry
      case rep isRep =>
        exact none -- fail, we cannot go to Y (and should be using Loopy from below!)
      all_goals sorry
termination_by
   Xhtab toWalk => toWalk.length

-- Go one step, to Y, but possibly via a loop
-- Given:
-- - the root of a tableau
-- - a path already walked - needed to go back up to companion
-- - a path still to be walked
-- return: the tableau at the end of the path, possibly by looping via condition 6 repeats
--
-- IDEA: instead of using "tabInAt", add the Closed (or Local?!) tableau at "done" as another input?
def goTo : (Σ R, ClosedTableau ([],[]) R) → List TNode → TNode → Option (Σ Y HistY, ClosedTableau HistY Y)
| ⟨R, tab⟩, done, Y => by
      cases tab_def : tabInAt ⟨R, ([],[]), tab⟩ done
      case none =>
        exact none -- this should never happen :-(
      case some X_ =>
        rcases X_ with ⟨X, HistX, ctX⟩
        cases ctX
        case loc ltX next =>
          cases ltX
          case byLocalRule B lnext lrApp =>
            refine if Y_in : Y ∈ B then ?_ else ?_
            -- move down a real step:
            · let ltY := lnext Y Y_in
              -- now need to turn ltY into a closed tableau. or change the return type?
              let ctYnext : (Z : TNode) → Z ∈ endNodesOf ltY → ClosedTableau HistX Z :=
                fun Z Z_in => next _ (endNodeOfChild_to_endNode lrApp lnext rfl Y_in Z_in)
              let ctY : ClosedTableau _ Y := ClosedTableau.loc ltY ctYnext
              exact some ⟨Y, _, ctY⟩
            -- not found:
            · exact none
          case sim X_simp =>
            have ctXnew := next X (by simp)
            simp [endNodesOf, List.mem_singleton] at ctXnew
            -- Now check that Y is among the successors given by non-local rules?
            -- Or could we make a recursive call here?
            -- Instead of `tabInAt ⟨R, ([],[]), tab⟩ done` above, now we want to consider ctXnew ?!
            cases ctXnew
            all_goals sorry
        case mrkL =>
          -- apply tabInAt ?
          sorry
        case rep theRep =>
          simp only [condSixRepeat, List.any_eq_true] at theRep
          rcases theRep with ⟨⟨k,Y⟩, getk, X_is_Y⟩ -- is k the index now? start with 0 or 1?
          let (bef, aft) := HistX
          -- now go back to the companion (and thus allow the path to be longer than the actual tableau)
          let pathToCompanion : List TNode := done.drop (k+1) -- undo the steps since companion
          have : pathToCompanion.length + 1 < done.length := by -- no more "rest" here as we only do one step
            zify
            -- ring -- why not working?
            sorry
          exact (tabInAt ⟨R, ([],[]), tab⟩ pathToCompanion)
        all_goals sorry

-- MB: Lemma 7
theorem loadedDiamondPaths
  {Root Δ : TNode}
  (tab : ClosedTableau ([],[]) Root) -- ensure History = [] here to prevent repeats from "above".
  (path_to_Δ : List TNode)
  (h : some tabΔ = tabInAt ⟨Root,_,tab⟩ path_to_Δ)
  {M : KripkeModel W} {v : W}
  (φ : AnyFormula)
  (negLoad_in : NegLoadFormula_in_TNode (~'⌊α⌋φ) Δ) -- FIXME: ∈ not working here?
  (v_X : (M,v) ⊨ Δ)
  (v_α_w : relate M α v w)
  (w_φ : (M,w) ⊨ ~''φ)
  : ∃ path_Δ_to_Γ : List TNode,
    ∃ Γ ∈ tabInAt ⟨Root,_,tab⟩ (path_to_Δ ++ path_Δ_to_Γ),
    (AnyNegFormula_in_TNode (~''φ) Γ.1) -- FIXME: ∈ not working here?
    ∧
    (M,w) ⊨ Γ.1 :=
  by
  let ⟨L,R,O⟩ := Δ
  let ⟨ΔNode, ΔHist, ΔTab⟩ := tabΔ
  -- cases tab -- No, we want to distinguish by cases what is happening at Δ
  cases ΔTab
  case mrkL =>
    -- it should be impossible to apply (M+)
    -- because we already have a loaded formula in Δ
    simp at negLoad_in
    cases negLoad_in
    case inl hyp => subst hyp; sorry
    all_goals sorry

  all_goals sorry

-- MB: Lemma 8
theorem freeSatDown : sorry := sorry
-- have := localRuleTruth
-- have := loadedDiamondPaths


theorem tableauThenNotSat : ∀ X, ClosedTableau LoadHistory.nil X → ¬Satisfiable X :=
  by
  intro X t
  sorry

-- Theorem 2, page 30
theorem correctness : ∀LR : TNode, Satisfiable LR → Consistent LR :=
  by
    intro LR
    contrapose
    unfold Consistent
    unfold Inconsistent
    simp only [not_nonempty_iff, not_isEmpty_iff, not_exists, not_forall, exists_prop, Nonempty.forall]
    intro hyp
    apply tableauThenNotSat LR hyp

theorem soundTableau : ∀φ, Provable φ → ¬Satisfiable ({~φ} : Finset Formula) :=
  by
    intro φ prov
    rcases prov with ⟨tabl⟩|⟨tabl⟩
    exact tableauThenNotSat ([~φ], [], none) tabl
    exact tableauThenNotSat ([], [~φ], none) tabl

theorem soundness : ∀φ, Provable φ → tautology φ :=
  by
    intro φ prov
    apply notsatisfnotThenTaut
    rw [← singletonSat_iff_sat]
    apply soundTableau
    exact prov
