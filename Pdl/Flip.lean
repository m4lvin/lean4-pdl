import Pdl.TableauPath

/-! # Flipping a tableau (for section 7)

Like the paper, we only prove interpolation for clusters with a loaded formulas on the right side.
For the case where the loaded formula is on the left, we flip the tableau left-to-right.

The lemmas here then allow us to prove `clusterInterpolation` from `clusterInterpolation_right`.
-/

def Olf.flip : Olf → Olf := Option.map Sum.swap

@[simp]
lemma Olf.flip_inj {O1 O2 : Olf} : O1.flip = O2.flip ↔ O1 = O2 := by
  rcases O1 with (_|_|_) <;> rcases O2 with (_|_|_) <;> simp_all [Olf.flip]

def Sequent.flip : Sequent → Sequent := fun ⟨L, R, O⟩ => ⟨R, L, O.flip⟩

@[simp]
lemma Sequent.flip_right {X : Sequent} : X.flip.right = X.left := by
  rcases X with ⟨L,R,_|_|_⟩ <;> simp [Sequent.flip, Olf.flip]
@[simp]
lemma Sequent.flip_left {X : Sequent} : X.flip.left = X.right := by
  rcases X with ⟨L,R,_|_|_⟩ <;> simp [Sequent.flip, Olf.flip]

@[simp]
lemma Sequent.flip_flip {X : Sequent} : X.flip.flip = X := by
  rcases X with ⟨L,R,O⟩
  simp_all [Sequent.flip, Olf.flip]

@[simp]
lemma Sequent.flip_setEqTo_flip {X Y : Sequent} : X.flip.setEqTo Y.flip ↔ X.setEqTo Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L', R', O'⟩
  grind [Sequent.setEqTo, Sequent.flip, Olf.flip_inj]

@[simp]
lemma basic_flip {X : Sequent} : X.flip.basic ↔ X.basic := by
  rcases X with ⟨L,R,O⟩
  unfold Sequent.basic Sequent.flip
  simp only
  simp only [List.append_assoc, List.mem_append, Option.mem_toList, Option.map_eq_some_iff,
    Sum.exists, Sum.elim_inl, Sum.elim_inr,
    Sequent.closed]
  constructor
  · intro ⟨fs_basic, not_closed⟩
    constructor
    · intro φ φ_in
      apply fs_basic
      rcases φ_in with h|h|h|h
      · grind
      · grind
      · right
        right
        right
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, Sum.inr.injEq,
          exists_eq_right, Sum.swap_inr, reduceCtorEq, and_false, exists_false, or_false, negUnload]
        simp only [negUnload] at h
        exact h
      · right
        right
        left
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, reduceCtorEq,
          and_false, exists_false, Sum.swap_inr, Sum.inl.injEq, exists_eq_right, false_or,
          negUnload]
        simp only [negUnload] at h
        exact h
    · aesop
  · intro ⟨fs_basic, not_closed⟩
    constructor
    · intro φ φ_in
      apply fs_basic
      rcases φ_in with h|h|h|h
      · grind
      · grind
      · right
        right
        right
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, reduceCtorEq,
          and_false, exists_false, Sum.swap_inr, Sum.inl.injEq, exists_eq_right, false_or,
          negUnload] at h
        simp
        exact h
      · right
        right
        left
        simp only [Olf.flip, Option.map_eq_some_iff, Sum.exists, Sum.swap_inl, Sum.inr.injEq,
          exists_eq_right, Sum.swap_inr, reduceCtorEq, and_false, exists_false, or_false,
          negUnload] at h
        simp
        exact h
    · aesop

lemma nrep_flip (nrep : ¬rep Hist X) : ¬rep (List.map Sequent.flip Hist) X.flip := by
  simp_all [rep]

def LocalTableau.flip : LocalTableau X → LocalTableau X.flip := sorry

lemma endNodesOf_flip : (Y ∈ endNodesOf lt.flip) → (Y.flip ∈ endNodesOf lt) := sorry

def PdlRule.flip : PdlRule X Y → PdlRule X.flip Y.flip := by sorry

def LoadedPathRepeat.flip :
  LoadedPathRepeat Hist X → LoadedPathRepeat (List.map Sequent.flip Hist) X.flip := sorry

/-- (┛ಠ_ಠ)┛彡┻━┻ -/
def Tableau.flip {Hist X} : Tableau Hist X → Tableau (Hist.map Sequent.flip) X.flip
| .loc nrep nbas lt next =>  .loc (nrep_flip nrep)
                                  (by simp; exact nbas)
                                  lt.flip
                                  (fun Y Y_in => by
                                    convert (next Y.flip (endNodesOf_flip Y_in)).flip using 1
                                    rw [Sequent.flip_flip])
| .pdl nrep bas r next =>  .pdl (nrep_flip nrep)
                                (by simp; exact bas)
                                r.flip
                                next.flip
| .lrep lpr =>  .lrep lpr.flip

@[simp]
lemma Hist_flip {Hist} : List.map Sequent.flip (List.map Sequent.flip Hist) = Hist := by ext; simp

@[simp]
lemma Tableau.flip_flip {Hist X} {tab : Tableau Hist X} :
    tab.flip.flip = Sequent.flip_flip ▸ Hist_flip ▸ tab := by
  induction tab
  case loc =>
    sorry
  case pdl =>
    sorry
  case lrep =>
    sorry

def PathIn.flip : PathIn tab → PathIn tab.flip := sorry
