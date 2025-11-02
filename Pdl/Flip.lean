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

@[simp]
lemma Olf.flip_flip {O : Olf} : O.flip.flip = O := by
  rcases O with (_|_|_) <;> simp_all [Olf.flip]

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

lemma Sequent.flip_eq_off {X Y : Sequent} : X.flip = Y ↔ X = Y.flip := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  simp_all only [flip]
  constructor <;> intro h <;> cases h <;> convert rfl <;> simp

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

def LocalRule.flip :
    LocalRule (Lcond, Rcond, Ocond) ress → LocalRule (Rcond, Lcond, Ocond.flip) (ress.map .flip) :=
  sorry

def LocalRuleApp.flip {X B} : LocalRuleApp X B → LocalRuleApp X.flip (B.map Sequent.flip) := by
  rintro ⟨Lcond, Rcond, Ocond, rule, preconditionProof⟩
  next L R ress O B_def =>
  refine @LocalRuleApp.mk _ _ _ _ _ Rcond Lcond Ocond.flip rule.flip ?_ ?_
  · subst B_def
    simp
    rintro ⟨Lnew, Rnew, Onew⟩ Y_in
    simp [Sequent.flip]
    convert rfl using 3
    rcases O with (_|_|_) <;> rcases Onew with (_|_|_) <;> rcases Ocond with (_|_|_)
      <;> simp [Olf.flip, Olf.change, Option.insHasSdiff] <;> grind
  · rcases preconditionProof with ⟨hL, hR, hO⟩
    refine ⟨hR, hL, ?_⟩
    rcases O with (_|_|_) <;> rcases Ocond with (_|_|_) <;> simp_all [Olf.flip, Sum.swap]

def LocalTableau.flip : LocalTableau X → LocalTableau X.flip
  | (@byLocalRule X B lra next) => .byLocalRule lra.flip
                                                (fun Y Y_in => by
                                                  rw [← @Sequent.flip_flip Y]
                                                  refine (next Y.flip ?_).flip -- lemma this?
                                                  grind [Sequent.flip_eq_off])
  | (@sim X Xbas) => .sim (basic_flip.mpr Xbas)

lemma LocalTableau.flip_flip {lt : LocalTableau X} : lt.flip.flip = Sequent.flip_flip ▸ lt := by
  cases lt <;> simp [LocalTableau.flip]
  · -- rw [Sequent.flip_flip] -- motive is not type correct :-( use HEq?
    sorry
  · grind

lemma LocalTableau.flip_inj {X} {lt : LocalTableau X} :
    lt.flip.flip = (Sequent.flip_flip ▸ lt) := by
  cases lt
  case byLocalRule =>
    rw [LocalTableau.flip_flip]
  · grind [LocalTableau.flip]

lemma endNodesOf_flip {X} {lt : LocalTableau X} {Y} :
    Y ∈ endNodesOf lt.flip → Y.flip ∈ endNodesOf lt := by
  intro Y_in
  induction lt
  case byLocalRule B next lra IH =>
    simp [endNodesOf, LocalTableau.flip] at *
    rcases Y_in with ⟨Z, ⟨W, W_in_B, def_Z⟩, Y_in_end⟩
    subst def_Z
    use W, W_in_B
    apply IH
    grind only [!LocalTableau.flip_inj]
  case sim Z Zbas =>
    simp_all [LocalTableau.flip]

def PdlRule.flip : PdlRule X Y → PdlRule X.flip Y.flip := by sorry

def LoadedPathRepeat.flip :
  LoadedPathRepeat Hist X → LoadedPathRepeat (List.map Sequent.flip Hist) X.flip := sorry

/-- (┛ಠ_ಠ)┛彡┻━┻ -/
def Tableau.flip {Hist X} : Tableau Hist X → Tableau (Hist.map Sequent.flip) X.flip
| .loc nrep nbas lt next =>  .loc (nrep_flip nrep)
                                  (by simp; exact nbas)
                                  lt.flip
                                  (fun Y Y_in =>
                                   @Sequent.flip_flip Y ▸ (next Y.flip (endNodesOf_flip Y_in)).flip)
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
    simp [Tableau.flip]
    -- rw [LocalTableau.flip_flip] -- motive is not type correct :-( use HEq?
    sorry
  case pdl =>
    simp [Tableau.flip]
    -- need PdlRule.flip first
    sorry
  case lrep =>
    simp [Tableau.flip]
    -- need LoadedPathRepeat.flip first
    sorry

def PathIn.flip {Hist X} {tab : Tableau Hist X} : PathIn tab → PathIn tab.flip
  | .nil => .nil
  | @PathIn.loc _ _ nrep Xnbas ltX next Y Y_in tail =>
      @PathIn.loc _ _ _ _ _ _ Y.flip
        (by apply endNodesOf_flip; grind [LocalTableau.flip_flip])
        (by
          have := tail.flip; convert this using 1
          -- rw [Sequent.flip_flip] -- motive is not type correct :-( use HEq?
          sorry
        )
  | .pdl tail => .pdl tail.flip
