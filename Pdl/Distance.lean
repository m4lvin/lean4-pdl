
import Pdl.UnfoldBox
import Pdl.UnfoldDia

-- Alternative to `Paths.lean` for the proof of `correctRightIP`.

-- Currently unsure whether this is easier than doing world-paths.
-- Due to the general W type and M.Rel the distance may not be computable.
-- On the other hand, we *only need this for a proof* of correctness
-- of interpolants, not to define/compute the interpolant themselves.
-- So it may be fine to have noncomputable defs here.
-- Still leaves the map/enum problem though due to generality of W.

noncomputable -- for decidability
def distance {W} (M : KripkeModel W) (v w : W) : (α : Program) → Option Nat
| ·c => have:= Classical.propDecidable
        if M.Rel c w v then some 1 else none
| ?'τ => have:= Classical.propDecidable
         if evaluate M v τ ∧ v = w then some 0 else none
| α;'β => min (distance M v w α) (distance M v w β)
| α⋓β => sorry -- min { ... | u ∈ W } -- need map or enum over W here :-/
| ∗α => sorry -- min { ... | u ∈ W } -- need map or enum over W here :-/

noncomputable -- for decidability of M.Rel
def distance_list {W} (M : KripkeModel W) (v w : W) : (δ : List Program) → Option Nat
| [] => have:= Classical.propDecidable
        if v = w then some 0 else none
| (α::δ) => sorry -- min { ... + ... | u ∈ W } need map or enum over W here :-/

theorem distance_iff_relate :
    (distance M v w α).isSome ↔ relate M v w α := by
  sorry

theorem relate_existsH_distance :
    relate M v w α → ∃ Fδ ∈ H α,
        evaluate M v (Con Fδ.1)
      ∧ distance_list M v w Fδ.2 = distance M v w α  := by
  sorry
