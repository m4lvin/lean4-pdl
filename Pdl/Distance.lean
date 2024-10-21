
import Mathlib.Data.FinEnum

import Pdl.UnfoldDia

-- Alternative to `Paths.lean` for the proof of `correctRightIP`.

-- Currently unsure whether this is easier than doing world-paths.
-- Due to the general W type and M.Rel the distance may not be computable.
-- On the other hand, we *only need this for a proof* of correctness
-- of interpolants, not to define/compute the interpolant themselves.
-- So it may be fine to have noncomputable defs here.
-- Still leaves the map/enum problem though due to generality of W.

-- NOTE: it may be nice in general to have a Decidable evaluate.

-- TODO move parts from here to `Semantics.lean`?

/-- A Kripke model where the relation and valuation are decidable.
Moreover, to get computable composition and transitive closure we
want the type of worlds to be finite and enumerable.
In fact, to avoid choice, we want a list of all worlds.
-/
structure DecidableKripkeModel (W :Type) where
  M : KripkeModel W
  allW : List W
  h : ∀ w : W, w ∈ allW
  deceq : DecidableEq W
  decrel : ∀ n, DecidableRel (M.Rel n)
  decval : ∀ w n, Decidable (M.val w n)

-- Possibly useful reference:
-- Martin Lange (2005): *Model checking propositional dynamic logic with all extras*
-- Journal of Applied Logic
-- https://doi.org/10.1016/j.jal.2005.08.002

mutual
instance evaluate.instDecidable (Mod : DecidableKripkeModel W) w φ
    : Decidable (evaluate Mod.M w φ) := by
  cases φ
  · apply isFalse
    simp only [evaluate, not_false_eq_true]
  · simp only [evaluate]
    apply Mod.decval
  case neg φ =>
    simp only [evaluate]
    have IH := evaluate.instDecidable Mod w φ
    by_cases decide (evaluate Mod.M w φ)
    · apply isFalse
      simp [Decidable.not_not] at *
      assumption
    · apply isTrue
      simp at *
      assumption
  case and φ1 φ2 =>
    have IH1 := evaluate.instDecidable Mod w φ1
    have IH2 := evaluate.instDecidable Mod w φ2
    by_cases @decide (evaluate Mod.M w φ1) IH1 <;> by_cases @decide (evaluate Mod.M w φ2) IH2
    · apply isTrue; simp at *; tauto
    all_goals
      apply isFalse; simp at *; tauto
  case box α φ =>
    simp only [evaluate]
    let reachable := Mod.allW.filter
      (fun v => @decide (relate Mod.M α w v) (relate.instDecidable Mod α w v))
    let hyp := reachable.all
      (fun v => @decide (evaluate Mod.M v φ) (evaluate.instDecidable Mod v φ))
    by_cases decide hyp
    case pos yes =>
      apply isTrue
      intro v w_v
      have : v ∈ Mod.allW := Mod.h v
      have : v ∈ reachable := by
        unfold_let reachable
        simp only [List.mem_filter, decide_eq_true_eq]
        tauto
      unfold_let hyp at yes
      simp_all
    case neg no =>
      apply isFalse
      push_neg
      unfold_let hyp at no
      simp at no
      rcases no with ⟨v, v_in_r, not_v_φ⟩
      aesop
  termination_by
    sizeOf φ

instance relate.instDecidable (Mod : DecidableKripkeModel W) α v w
    : Decidable (relate Mod.M α v w) := by
  cases α
  case atom_prog a =>
    simp only [relate]
    apply Mod.decrel
  case sequence α β =>
    have IHα := relate.instDecidable Mod α
    have IHβ := relate.instDecidable Mod β
    let α_img := Mod.allW.filter (fun x => @decide (relate Mod.M α v x) (IHα v x))
    let α_β_fun := fun x => Mod.allW.filter (fun y => @decide (relate Mod.M β x y) (IHβ x y))
    let α_β_img := (α_img.map α_β_fun).join
    simp only [relate]
    -- FIXME: inferred `List.instDecidableMemOfLawfulBEq w α_β_img` leads to non-computable code?
    by_cases @decide (w ∈ α_β_img) sorry
    case pos yes =>
      apply isTrue
      unfold_let α_β_img at yes
      simp only [List.mem_join, List.mem_map, exists_exists_and_eq_and, decide_eq_true_eq] at yes
      rcases yes with ⟨y, y_in, w_in⟩
      use y
      unfold_let α_img at y_in
      unfold_let α_β_fun at w_in
      simp only [List.mem_filter, decide_eq_true_eq] at *
      tauto
    case neg no =>
      apply isFalse
      simp only [not_exists, not_and]
      intro y v_y
      unfold_let α_β_img at no
      unfold_let α_β_fun at no
      unfold_let α_img at no
      simp [List.mem_join, List.mem_map, List.mem_filter, FinEnum.mem_toList,
        decide_eq_true_eq, true_and, exists_exists_and_eq_and, not_exists, not_and] at no
      exact no y (Mod.h _) v_y (Mod.h _)
  case union α β =>
    have IHα := relate.instDecidable Mod α v w
    have IHβ := relate.instDecidable Mod β v w
    simp
    by_cases relate Mod.M α v w <;> by_cases relate Mod.M β v w
    · apply isTrue; tauto
    · apply isTrue; tauto
    · apply isTrue; tauto
    · apply isFalse; tauto
  case star α =>
    simp
    have IHα := relate.instDecidable Mod α
    -- PROBLEM: decidable relation does not imply that
    --          its transitive closure is decidable!
    -- QUESTION: would it be enough to have decidable
    --           transitive closures of atomic programs
    --           to then compute all other PDL stars?
    -- FOR NOW: we have `FinEnum`, that should be enough.
    sorry
  case test τ =>
    simp only [relate]
    have IHτ := evaluate.instDecidable Mod v τ
    by_cases @decide (v = w) (Mod.deceq v w) <;> by_cases decide (evaluate Mod.M v τ)
    · apply isTrue; simp at *; tauto
    all_goals
      apply isFalse; simp at *; tauto
  termination_by
    sizeOf α
end

def distance {W} (Mod : DecidableKripkeModel W) (v w : W)
    : (α : Program) → Option Nat
| ·c => if @decide (Mod.M.Rel c w v) (Mod.decrel c w v) then some 1 else none
| ?'τ => by
  have := evaluate.instDecidable Mod v τ
  have := Mod.deceq v w
  exact (if v = w ∧ evaluate Mod.M v τ then some 0 else none)
| α⋓β => min (distance Mod v w α) (distance Mod v w β)
| α;'β =>

    let α_β_distOf := fun x => Nat.add <$> distance Mod v x α <*> distance Mod x w β
    (Mod.allW.map α_β_distOf).reduceOption.minimum?
| ∗α =>
    -- This will be ugly, but essentially we need something like the matrix method?
    let maxN := Mod.allW.length
    sorry -- min { ... | u ∈ W } -- need map or enum over W here :-/
termination_by
  α => sizeOf α

def distance_list {W} (Mod : DecidableKripkeModel W) (v w : W) : (δ : List Program) → Option Nat
| [] => have := Mod.deceq v w
        if v = w then some 0 else none
| (α::δ) => -- similar to α;'β case in `distance`
    let α_δ_distOf := fun x => Nat.add <$> distance Mod v x α <*> distance_list Mod x w δ
    (Mod.allW.map α_δ_distOf).reduceOption.minimum?

theorem distance_iff_relate (Mod : DecidableKripkeModel W) :
    (distance Mod v w α).isSome ↔ relate Mod.M α v w := by
  sorry

theorem relate_existsH_distance (Mod : DecidableKripkeModel W) (α : Program) :
    relate Mod.M α v w → ∃ Fδ ∈ H α,
        evaluate Mod.M v (Con Fδ.1)
      ∧ distance_list Mod v w Fδ.2 = distance Mod v w α  := by
  sorry
