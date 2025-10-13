-- EXAMPLES

import Bml.Semantics

open HasSat

theorem mytaut1 (p : Char) : Tautology ((·p)↣·p) :=
  by
  unfold Tautology Evaluate
  intro W M w
  simp

theorem mytaut2 (p : Char) : Tautology ((~~·p)↣·p) :=
  by
  unfold Tautology Evaluate
  intro W M w
  classical
  simp

def myModel : KripkeModel ℕ where
  val _ _ := True
  Rel _ v := HEq v 1

theorem mysat (p : Char) : Satisfiable (·p) :=
  by
  unfold Satisfiable
  exists ℕ
  exists myModel
  exists 1

-- Some validities of basic modal logic

theorem boxTop : Tautology (□⊤) := by
  unfold Tautology Evaluate
  tauto

theorem A3 (X Y : Formula) : Tautology (□(X⋀Y) ↣ □X⋀□Y) :=
  by
  simp_all [Tautology, Evaluate]
