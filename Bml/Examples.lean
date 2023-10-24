-- EXAMPLES
import Syntax
import Semantics

#align_import examples

open HasSat

theorem mytaut1 (p : Char) : Tautology ((·p)↣·p) :=
  by
  unfold Tautology Evaluate
  intro W M w
  simp; unfold Evaluate; tauto
#align mytaut1 mytaut1

open Classical

theorem mytaut2 (p : Char) : Tautology ((~~·p)↣·p) :=
  by
  unfold Tautology Evaluate
  intro W M w
  classical
  simp
  unfold Evaluate
  tauto
#align mytaut2 mytaut2

def myModel : KripkeModel ℕ where
  val _ _ := True
  Rel _ v := HEq v 1
#align myModel myModel

theorem mysat (p : Char) : Satisfiable (·p) :=
  by
  unfold satisfiable
  exists ℕ
  exists myModel
  exists 1
  unfold Evaluate
#align mysat mysat

-- Some validities of basic modal logic
theorem boxTop : Tautology (□⊤) := by
  unfold Tautology Evaluate
  tauto
#align boxTop boxTop

theorem A3 (X Y : Formula) : Tautology (□(X⋏Y)↣□X⋏□Y) :=
  by
  unfold Tautology Evaluate
  intro W M w
  by_contra hyp
  simp at hyp 
  unfold Evaluate at hyp 
  simp at hyp 
  cases' hyp with hl hr
  contrapose! hr
  constructor
  · intro v1 ass; exact (hl v1 ass).1
  · intro v2 ass; exact (hl v2 ass).2
#align A3 A3

