
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
want the type of worlds to be finite and enumerable. -/
structure DecidableKripkeModel (W :Type) where
  M : KripkeModel W
  enum : FinEnum W -- alternatively, should we just restrict W to be a list?
  deceq : DecidableEq W
  decrel : ∀ n, DecidableRel (M.Rel n)
  decval : ∀ w n, Decidable (M.val w n)

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
    by_cases evaluate Mod.M w φ
    · apply isFalse
      simp only [Decidable.not_not]
      assumption
    · apply isTrue
      assumption
  case and φ1 φ2 =>
    have IH1 := evaluate.instDecidable Mod w φ1
    have IH1 := evaluate.instDecidable Mod w φ2
    by_cases evaluate Mod.M w φ1 <;> by_cases evaluate Mod.M w φ2
    · apply isTrue; simp; tauto
    all_goals
      apply isFalse; simp; tauto
  case box α φ =>
    simp
    sorry

instance relate.instDecidable (Mod : DecidableKripkeModel W) α v w
    : Decidable (relate Mod.M α v w) := by
  cases α
  case atom_prog a =>
    simp only [relate]
    apply Mod.decrel
  case sequence α β =>
    have IH1 := relate.instDecidable Mod α v
    have IH1 := relate.instDecidable Mod β
    -- do we need more here? iterate over all `W` or so?
    sorry
  case union α β =>
    have IH1 := relate.instDecidable Mod α v w
    have IH1 := relate.instDecidable Mod β v w
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
    sorry
  case test τ =>
    simp only [relate]
    have := Mod.deceq v w
    have IHτ := evaluate.instDecidable Mod v τ
    by_cases v = w <;> by_cases evaluate Mod.M v τ
    · apply isTrue; tauto
    all_goals
      apply isFalse; tauto
end

def distance {W} (Mod : DecidableKripkeModel W) (v w : W)
    : (α : Program) → Option Nat
| ·c => if @decide (Mod.M.Rel c w v) (Mod.decrel c w v) then some 1 else none
| ?'τ => by
  have := evaluate.instDecidable Mod v τ
  have := Mod.deceq v w
  exact (if v = w ∧ evaluate Mod.M v τ then some 0 else none)
| α⋓β => min (distance Mod v w α) (distance Mod v w β)
| α;'β => sorry -- min { ... | u ∈ W } -- need map or enum over W here :-/
| ∗α => sorry -- min { ... | u ∈ W } -- need map or enum over W here :-/

def distance_list {W} (Mod : DecidableKripkeModel W) (v w : W) : (δ : List Program) → Option Nat
| [] => have := Mod.deceq v w
        if v = w then some 0 else none
| (α::δ) => sorry -- min { ... + ... | u ∈ W } need map or enum over W here :-/

theorem distance_iff_relate (Mod : DecidableKripkeModel W) :
    (distance Mod v w α).isSome ↔ relate Mod.M α v w := by
  sorry

theorem relate_existsH_distance (Mod : DecidableKripkeModel W) (α : Program) :
    relate Mod.M α v w → ∃ Fδ ∈ H α,
        evaluate Mod.M v (Con Fδ.1)
      ∧ distance_list Mod v w Fδ.2 = distance Mod v w α  := by
  sorry
