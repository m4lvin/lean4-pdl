import Pdl.Flip

/-- It seems we do not need this (yet)?
TODO: can this be stated better, without convert tactic? -/
lemma PathIn.flip_flip {Hist X} {tab : Tableau Hist X} (s : PathIn tab) :
    s.flip.flip = Tableau.flip_flip ▸ (by convert s <;> simp) := by
  simp
  induction s
  case nil =>
    simp [PathIn.flip]
    grind
  case loc IH =>
    simp only [flip, List.map_cons, eq_mpr_eq_cast]
    sorry
  case pdl Hist X Y nrep bas r next tail IH =>
    -- Ugly, but works :-)
    simp only [flip]
    rw! [IH]
    clear IH
    apply eq_of_heq
    have := @heq_of_eq _ (@tail.pdl _ _ _ nrep bas r)
    convert this ?_ <;> simp_all [PdlRule.flip_flip] <;> rfl
