import Mathlib.Tactic.DepRewrite

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

@[simp]
lemma Olf.flip_none : Olf.flip none = none := by simp [Olf.flip]

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

lemma Sequent.flip_eq_off {X Y : Sequent} : (X.flip = Y) = (X = Y.flip) := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  simp_all only [flip]
  rw [@propext_iff]
  constructor <;> intro h <;> cases h <;> convert rfl <;> simp

@[simp]
lemma Sequent.flip_setEqTo_flip {X Y : Sequent} : X.flip.setEqTo Y.flip ↔ X.setEqTo Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L', R', O'⟩
  grind [Sequent.setEqTo, Sequent.flip, Olf.flip_inj]

@[simp]
lemma Sequent.map_flip_map_flip {Hist} :
    (List.map Sequent.flip (List.map Sequent.flip Hist)) = Hist := by
  induction Hist <;> simp_all

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

def LocalRule.flip (lr : LocalRule (Lcond, Rcond, Ocond) ress) :
    LocalRule (Rcond, Lcond, Ocond.flip) (ress.map .flip) := by
  cases lr
  case oneSidedL YS orule YS_def =>
    apply LocalRule.oneSidedR orule
    aesop
  case oneSidedR YS orule YS_def =>
    apply LocalRule.oneSidedL orule
    aesop
  case LRnegL =>
    apply LocalRule.LRnegR
  case LRnegR =>
    apply LocalRule.LRnegL
  case loadedL YS χ lrule YS_def =>
    apply LocalRule.loadedR _ lrule
    subst YS_def
    simp only [List.empty_eq, List.map_map, List.map_inj_left, Function.comp_apply, Prod.forall]
    rintro L (_|_|_) <;> simp_all [Sequent.flip, Olf.flip]
  case loadedR lrule YS_def =>
    apply LocalRule.loadedL _ lrule
    subst YS_def
    simp only [List.empty_eq, List.map_map, List.map_inj_left, Function.comp_apply, Prod.forall]
    rintro L (_|_|_) <;> simp_all [Sequent.flip, Olf.flip]

lemma LocalRule.flip_flip (lr : LocalRule (Lcond, Rcond, Ocond) ress) :
    lr.flip.flip = Olf.flip_flip ▸ Sequent.map_flip_map_flip ▸ lr := by
  cases lr <;> simp_all [LocalRule.flip] <;> grind

/-- Note: is it possible and useful to rewrite this in more term and less tactic mode? -/
def LocalRuleApp.flip : LocalRuleApp → LocalRuleApp := by
  rintro ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconditionProof⟩
  refine @LocalRuleApp.mk R L O.flip Rcond Lcond Ocond.flip _ rule.flip (C.map Sequent.flip) ?_ ?_
  · subst hC
    simp
    rintro ⟨Lnew, Rnew, Onew⟩ Y_in
    simp [Sequent.flip]
    convert rfl using 3
    rcases O with (_|_|_) <;> rcases Onew with (_|_|_) <;> rcases Ocond with (_|_|_)
      <;> simp [Olf.flip, Olf.change, Option.insHasSdiff] <;> grind
  · rcases preconditionProof with ⟨hL, hR, hO⟩
    refine ⟨hR, hL, ?_⟩
    rcases O with (_|_|_) <;> rcases Ocond with (_|_|_) <;> simp_all [Olf.flip, Sum.swap]

@[simp]
lemma Sequent.flip_comp_flip : Sequent.flip ∘ Sequent.flip = id := by
  ext X
  rw [Function.comp_apply, Sequent.flip_flip, id_eq]

lemma LocalRuleApp.flip_flip {lra : LocalRuleApp} :
    lra.flip.flip = lra := by
  rcases lra with ⟨L, R, O, C, Lcond, Rcond, Ocond, ress, rule, hC, preconditionProof⟩
  simp [LocalRuleApp.flip]
  rw [LocalRule.flip_flip]
  grind

lemma Sequent.flip_mem_of_mem_map_flip {B : List Sequent} {Y : Sequent} :
    Y ∈ B.map Sequent.flip → Y.flip ∈ B := by aesop

def LocalTableau.flip {X} : LocalTableau X → LocalTableau X.flip
  | (@byLocalRule X lra X_def next) => .byLocalRule lra.flip
      (by subst X_def; simp [LocalRuleApp.flip, Sequent.flip])
      (fun Y Y_in =>
        @Sequent.flip_flip Y ▸ (next Y.flip (Sequent.flip_mem_of_mem_map_flip Y_in)).flip)
  | (@sim X Xbas) => .sim (basic_flip.mpr Xbas)

lemma LocalTableau.flip_flip {lt : LocalTableau X} : lt.flip.flip = Sequent.flip_flip ▸ lt := by
  induction lt <;> simp [LocalTableau.flip]
  case byLocalRule X lra X_def next IH =>
    apply eq_of_heq
    rw! (castMode := .all) [Sequent.flip_flip] -- :-)
    simp only [heq_eq_eq, byLocalRule.injEq]
    constructor
    · exact LocalRuleApp.flip_flip
    · refine Function.hfunext rfl ?_
      intro X X' X_heq_X'
      apply Function.hfunext
      · rw [LocalRuleApp.flip_flip]
        grind
      · grind
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
    simp only [LocalTableau.flip, endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach,
      true_and, Subtype.exists, ↓existsAndEq] at *
    rcases Y_in with ⟨W, W_in_B, Y_in_end⟩
    refine ⟨W.flip, ?_, ?_⟩ <;> grind
  case sim Z Zbas =>
    simp_all [LocalTableau.flip]

lemma exists_flip_of_endNodesOf {X : Sequent} {ltf : LocalTableau X.flip} {Zf} :
     Zf ∈ endNodesOf ltf → ∃ Z, Zf = Z.flip ∧ Z ∈ endNodesOf ltf.flip := by
  intro Z_in
  cases ltf
  case byLocalRule lra next X_def =>
    simp only [endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, ↓existsAndEq, LocalTableau.flip] at *
    rcases Z_in with ⟨Yf, Yf_in_B, Zf_via_Yf⟩
    refine ⟨Zf.flip, ?_, ⟨Yf.flip, ?_, ?_⟩⟩
    · simp
    · grind [LocalRuleApp.flip]
    · rw! (castMode := .all) [@Sequent.flip_flip Yf]
      simp only
      apply endNodesOf_flip
      rw [LocalTableau.flip_flip]
      grind
  case sim Xbas =>
    simp_all only [endNodesOf, List.mem_cons, List.not_mem_nil, or_false, LocalTableau.flip]
    subst_eqs
    simp

def PdlRule.flip {X Y} (r : PdlRule X Y) : PdlRule X.flip Y.flip := by
  cases r
  case loadL L δs α φ R in_L notBox Y_def =>
    apply PdlRule.loadR in_L notBox
    simp_all only [Sequent.flip, Prod.mk.injEq, true_and]
    rfl
  case loadR R δs α φ L in_R notBox Y_def =>
    apply PdlRule.loadL in_R notBox
    simp_all only [Sequent.flip, Prod.mk.injEq, true_and]
    rfl
  case freeL L R δs α φ X_def Y_def =>
    apply PdlRule.freeR
    all_goals
      subst X_def Y_def
      simp_all only [Sequent.flip]
      rfl
  case freeR L R δs α φ X_def Y_def =>
    apply PdlRule.freeL
    all_goals
      subst X_def Y_def
      simp_all only [Sequent.flip]
      rfl
  case modL L R a ξ X_def Y_def =>
    apply @PdlRule.modR Y.flip R L a X.flip ξ
    all_goals
      subst X_def Y_def
      cases ξ <;> simp_all [Sequent.flip,Olf.flip]
  case modR L R a ξ X_def Y_def =>
    apply @PdlRule.modL Y.flip R L a X.flip ξ
    all_goals
      subst X_def Y_def
      cases ξ <;> simp_all [Sequent.flip,Olf.flip]

lemma PdlRule.flip_flip {X Y} (r : PdlRule X Y) :
    r.flip.flip = (Sequent.flip_flip ▸ Sequent.flip_flip ▸ r) := by
  cases r <;> simp [PdlRule.flip] <;> grind

@[simp]
lemma Sequent.flip_multisetEqTo {X Y : Sequent} :
    X.flip.multisetEqTo Y.flip ↔ X.multisetEqTo Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L, R, O⟩
  simp only [multisetEqTo, flip, Multiset.coe_eq_coe, Olf.flip_inj]
  grind

@[simp]
lemma Sequent.flip_isLoaded {X : Sequent} :
    X.flip.isLoaded ↔ X.isLoaded := by
  rcases X with ⟨L, R, O⟩
  simp only [Sequent.isLoaded, Sequent.flip, Olf.flip]
  grind

def LoadedPathRepeat.flip {Hist X} : LoadedPathRepeat Hist X →
    LoadedPathRepeat (List.map Sequent.flip Hist) X.flip
| ⟨k, hk⟩ => by
  refine ⟨⟨k.1, ?_⟩, ?_⟩
  · simp_all [List.length_map]
  · rcases hk with ⟨same, path_loaded⟩
    constructor
    · simp only [List.get_eq_getElem, List.getElem_map, Sequent.flip_multisetEqTo]
      convert same
    · simp only [List.get_eq_getElem, List.getElem_map, Sequent.flip_isLoaded]
      intro m m_lt
      apply path_loaded ⟨m, by grind⟩
      omega

-- move elsewhere?
lemma LoadedPathRepeat.ext {Hist X} (lprA lprB : LoadedPathRepeat Hist X) :
    lprA.1 = lprB.1 → lprA = lprB := by
  rcases lprA with ⟨a, ha⟩
  rcases lprB with ⟨b, hb⟩
  grind

lemma LoadedPathRepeat.flip_flip {Hist X} (lpr : LoadedPathRepeat Hist X) :
    lpr.flip.flip = Sequent.map_flip_map_flip ▸ Sequent.flip_flip ▸ lpr := by
  rcases lpr with ⟨k, hk⟩
  simp [LoadedPathRepeat.flip]
  rw! [Sequent.map_flip_map_flip, Sequent.flip_flip]
  rfl

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
  case loc Hist X nrep nbas ltX next IH =>
    simp [Tableau.flip]
    rw! [LocalTableau.flip_flip]
    rw! (castMode := .all) [Sequent.flip_flip]
    simp
    convert Tableau.loc.congr_simp nrep nbas ltX next next ?_
    · exact Sequent.map_flip_map_flip
    · exact Sequent.map_flip_map_flip
    case h Y W Y_eq_W Y_in W_in Y_heq_W =>
      subst Y_eq_W
      simp_all
      specialize IH Y Y_in
      rw! (castMode := .all) [@Sequent.flip_flip Y]
      simp_all
    · simp
    · rfl
  case pdl r next IH =>
    nth_rewrite 1 [Tableau.flip]
    nth_rewrite 1 [Tableau.flip]
    rw [IH]; clear IH
    rw [PdlRule.flip_flip]
    grind
  case lrep lpr =>
    grind [Tableau.flip, LoadedPathRepeat.flip_flip]

def PathIn.flip {Hist X} {tab : Tableau Hist X} : PathIn tab → PathIn tab.flip
  | .nil => .nil
  | @PathIn.loc _ _ nrep Xnbas ltX next Y Y_in tail =>
      @PathIn.loc _ _ _ _ _ _ Y.flip
        (by apply endNodesOf_flip; grind [LocalTableau.flip_flip])
        (by
          have := tail.flip; convert this using 1
          rw! [@Sequent.flip_flip Y]
          rfl
        )
  | .pdl tail => .pdl tail.flip

lemma PathIn_helper {tabA : Tableau HistA XA} {tabB : Tableau HistB XB}
    (hHist : HistA = HistB)
    (hX : XA = XB) :
    tabA = hHist ▸ hX ▸ tabB → PathIn tabA = PathIn tabB := by
  subst_eqs
  simp_all

@[simp]
lemma PathIn_type_flip_flip {tab : Tableau Hist X} :
    PathIn tab.flip.flip = PathIn tab := by
  rw [Tableau.flip_flip]
  grind

lemma PathIn.nodeAt_flip {Hist X} {tab : Tableau Hist X} {e : PathIn tab} :
    nodeAt (e.flip) = (nodeAt e).flip := by
  induction e
  case nil => simp_all [PathIn.flip]
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    simp [PathIn.flip]
    rw [← IH]
    clear IH
    simp only [nodeAt, List.map_cons]
    convert rfl
    · rw! (castMode := .all) [@Sequent.flip_flip Y]
      rfl
    · simp_all
    · rw! (castMode := .all) [@Sequent.flip_flip Y]
      rfl
    · simp_all
  case pdl => simp_all [PathIn.flip]

/-- `Eq.mpr` is a heterogeneous identity. -/
theorem flip_aux_eq_mpr_heq {a b : Sort u} (h : a = b) (x : b) : HEq (Eq.mpr h x) x := by
  cases h; rfl

/-- Flipping a tableau twice gives back (heterogeneously) the original tableau. -/
theorem flip_aux_Tableau_flip_flip_heq {H X} (t : Tableau H X) : HEq t.flip.flip t := by
  rw [Tableau.flip_flip]; exact eqRec_heq_iff_heq.mpr (eqRec_heq_iff_heq.mpr HEq.rfl)

/-- Flipping a local tableau twice gives back (heterogeneously) the original one. -/
theorem flip_aux_LocalTableau_flip_flip_heq {X} (lt : LocalTableau X) : HEq lt.flip.flip lt := by
  rw [LocalTableau.flip_flip]; exact eqRec_heq_iff_heq.mpr HEq.rfl

/-- Flipping a pdl rule twice gives back (heterogeneously) the original one. -/
theorem flip_aux_PdlRule_flip_flip_heq {X Y} (r : PdlRule X Y) : HEq r.flip.flip r := by
  rw [PdlRule.flip_flip]; exact eqRec_heq_iff_heq.mpr (eqRec_heq_iff_heq.mpr HEq.rfl)

/-- End nodes are invariant under flipping a local tableau twice. -/
theorem endNodesOf_flip_flip {X} (lt : LocalTableau X) :
    endNodesOf lt.flip.flip = endNodesOf lt := by
  rw [LocalTableau.flip_flip]; congr 1
  · exact Sequent.flip_flip
  · exact eqRec_heq _ _

/-- `PathIn.flip` respects heterogeneous equality of paths. -/
theorem PathIn_flip_heq {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    {p1 : PathIn t1} {p2 : PathIn t2}
    (hH : H1 = H2) (hX : X1 = X2) (ht : HEq t1 t2) (hp : HEq p1 p2) :
    HEq p1.flip p2.flip := by
  subst hH hX; obtain rfl := eq_of_heq ht; rw [eq_of_heq hp]

/-- `Tableau.flip` respects heterogeneous equality of tableaux. -/
theorem Tableau_flip_heq {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    (hH : H1 = H2) (hX : X1 = X2) (h : HEq t1 t2) : HEq t1.flip t2.flip := by
  subst hH hX; rw [eq_of_heq h]

/-- Flipping a path twice gives back (after casting along `PathIn_type_flip_flip`)
the original path. -/
theorem PathIn.flip_flip {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    PathIn_type_flip_flip ▸ (p.flip.flip) = p := by
  induction p with
  | nil =>
    apply eq_of_heq
    rw [eqRec_heq_iff_heq]
    simp only [PathIn.flip]
    congr 1 <;> simp
  | @pdl Hist X Y nrep bas r next tail IH =>
    apply eq_of_heq
    rw [eqRec_heq_iff_heq]
    simp only [PathIn.flip]
    have hIH : HEq (tail.flip.flip) tail := eqRec_heq_iff_heq.mp (heq_of_eq IH)
    have hr : HEq r.flip.flip r := by
      rw [PdlRule.flip_flip, eqRec_heq_iff_heq, eqRec_heq_iff_heq]
    have hnext : HEq next.flip.flip next := by
      rw! [Tableau.flip_flip]; rw [eqRec_heq_iff_heq, eqRec_heq_iff_heq]
    congr 1 <;> first
      | rfl | exact hIH | exact hr | exact hnext | exact proof_irrel_heq _ _ | simp_all
  | @loc Hist X nrep nbas lt next Y Y_in tail IH =>
    apply eq_of_heq
    rw [eqRec_heq_iff_heq]
    simp only [PathIn.flip]
    have htail : HEq (tail.flip.flip) tail := eqRec_heq_iff_heq.mp (heq_of_eq IH)
    congr 1
    case e_1 => simp
    case e_2 => simp
    case e_5 => rw [LocalTableau.flip_flip, eqRec_heq_iff_heq]
    case e_6 =>
      apply Function.hfunext rfl
      intro a a' ha
      obtain rfl := eq_of_heq ha
      apply Function.hfunext
      · rw [endNodesOf_flip_flip]
      · intro b b' hb
        simp only [eqRec_heq_iff_heq]
        refine HEq.trans (Tableau_flip_heq (by simp) (by simp)
          (eqRec_heq_iff_heq.mpr HEq.rfl)) ?_
        refine HEq.trans (flip_aux_Tableau_flip_flip_heq _) ?_
        rw! (castMode := .all) [Sequent.flip_flip]
        apply heq_of_eq; congr 1
    case e_9 =>
      refine HEq.trans ?_ htail
      refine HEq.trans (flip_aux_eq_mpr_heq _ _) ?_
      refine PathIn_flip_heq (by simp) (by simp) ?_ (flip_aux_eq_mpr_heq _ _)
      simp only [eqRec_heq_iff_heq]
      refine Tableau_flip_heq (by simp) (by simp) ?_
      rw! (castMode := .all) [Sequent.flip_flip]
      apply heq_of_eq; congr 1
    all_goals (try exact proof_irrel_heq _ _)
    all_goals (try (simp))
