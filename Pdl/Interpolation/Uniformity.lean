import Pdl.Local.AllLocalTab
import Pdl.Interpolation.ClusterSatDown

/-! # Uniformity of split tableaux (Section 8.1)

This file defines when a tableau is *uniform*, by the two conditions U1 and U2 of the
paper, and shows that in a uniform tableau every loaded cluster has the property
`LoadedCluster.HasUniformSteps` that the construction of the quasi-tableau needs.

Recall the two conditions from the paper, where `Λ₁(s)` and `Λ₂(s)` are the left and the
right component of the sequent at the node `s`, and where `i ∈ {1,2}`:

* **U1.** If `Λᵢ(s)` is loaded then a local rule is applied to a formula in the unloaded
  component of `s`, unless that component is basic.
* **U2.** If `Λᵢ(s) = Λᵢ(t)` is loaded and not basic, and the unloaded components of both
  `s` and `t` are basic, then at `s` and at `t` the same rule is applied, to the same
  formula in the loaded component of the node.

Both conditions speak about the nodes of the tableau in the sense of the paper, i.e. also
about the nodes *inside* the local tableaux. Hence we state them for `FinePathIn tab`.
Note that in U2 the loaded component is not basic, so the rule applied at `s` and at `t`
must be a *local* rule; we therefore phrase U2 using `FinePathIn.lra?`, and "the same rule
applied to the same formula" becomes `LocalRuleApp.SameRuleAs`: the two rule applications
have the same principal formulas (`Lcond`, `Rcond` and `Ocond`) and the same results
(`ress`), and indeed use the same rule (`lr`).

The main result is `LoadedCluster.uniformOfUniTab`. Its proof splits into two cases, and
only the second one uses uniformity:

* If `Δ` is basic then by Lemma 9.7 (e) — here `Uniformity.basicModalStep` — the rule
  applied at a node of `C^R_Δ` is the modal rule `(M)` for the loaded formula of `Δ`, and
  hence the right component of the unique child only depends on `Δ`.
* If `Δ` is not basic then the rule applied at a node of `C^R_Δ` is a local rule acting on
  the right. By U1 the left component of such a node is basic, so U2 applies and says that
  the same rule with the same principal formula is used at all these nodes. Since a local
  rule application only changes the right component by deleting its principal formulas and
  adding the results, the right components of the children agree — this is
  `Uniformity.map_rightOnly_C_eq`.

## Duplicated helper lemmas

The file `Pdl.ClusterInterpolation` imports this file (it uses `Tableau.isUniform` and
`LoadedCluster.uniformOfUniTab`), so we cannot use the lemmas about right rules that are
proved there. The section `Uniformity` below therefore repeats those that are needed here,
under different names.
-/

/-! ## The components of a sequent -/

/-- The left component of a sequent, together with the loaded formula, again as a sequent.
This is `Λ₁` from the paper; compare `Sequent.rightOnly`, which is `Λ₂`. -/
def Sequent.leftOnly (X : Sequent) : Sequent := ⟨X.1, [], X.2.2⟩

/-- The left component of a sequent, without any loaded formula. When the loaded formula
is on the right, i.e. in the situation of a `LoadedCluster`, this is the *unloaded*
component `Λ₁` of the node, and `Sequent.leftFree X |>.basic` says that no local rule is
applicable to it. -/
def Sequent.leftFree (X : Sequent) : Sequent := ⟨X.1, [], none⟩

/-- The right component of a sequent, without any loaded formula. When the loaded formula
is on the left this is the *unloaded* component `Λ₂` of the node. -/
def Sequent.rightFree (X : Sequent) : Sequent := ⟨[], X.2.1, none⟩

/-- Two local rule applications use the same rule with the same principal formulas.
The fields `Lcond`, `Rcond` and `Ocond` are the principal formulas and `ress` is the list
of results of the rule, so this says that the *same rule instance* is applied at two nodes,
which may still have different sequents. -/
def LocalRuleApp.SameRuleAs (lra₁ lra₂ : LocalRuleApp) : Prop :=
  lra₁.Lcond = lra₂.Lcond ∧ lra₁.Rcond = lra₂.Rcond ∧ lra₁.Ocond = lra₂.Ocond
    ∧ lra₁.ress = lra₂.ress ∧ HEq lra₁.lr lra₂.lr

/-! ## Uniformity -/

/-- Condition U1: at a node with a loaded component, a rule is applied to the *unloaded*
component unless the latter is basic. Since every rule is a left rule or a right rule but
not both (`FinePathIn.not_left_and_right`), we state this as: a rule on the unloaded side
is applied.

The condition is only about nodes at which a rule is applied at all, i.e. we exclude the
leaves given by a loaded-path repeat, which is what `¬ f.base.isLrep` says. Note that this
exclusion is needed: at a loaded-path repeat the tableau stops, so no rule at all — and in
particular no rule on the unloaded component — is applied there, while the sequent of a
loaded-path repeat may well have a non-basic unloaded component. (For example, the sequent
reached again after a loop may contain a conjunction on the unloaded side; the tableau is
then forced to stop, because `Tableau.loc` and `Tableau.pdl` both require `¬ flprep`.)
Without the exclusion no tableau with such a repeat would be uniform, and `Tableau.toUniform`
would fail. -/
def Tableau.U1 {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  ∀ f : FinePathIn tab, ¬ f.base.isLrep →
      (f.label.2.2.isRight → ¬ f.label.leftFree.basic → f.usesLeftRule)
    ∧ (f.label.2.2.isLeft → ¬ f.label.rightFree.basic → f.usesRightRule)

/-- Condition U2: two nodes whose loaded component is the same and not basic, and whose
unloaded components are both basic, apply the same rule to the same formula of the loaded
component. As the loaded component is not basic the rule must be a local one, so we may
state this for the local rule applications `f.lra?` and `g.lra?`. -/
def Tableau.U2 {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  ∀ (f g : FinePathIn tab) (lraf lrag : LocalRuleApp),
      f.lra? = some lraf → g.lra? = some lrag →
      ( (f.label.2.2.isRight → f.label.rightOnly = g.label.rightOnly →
          ¬ f.label.rightOnly.basic → f.label.leftFree.basic → g.label.leftFree.basic →
          lraf.isRightRule → lrag.isRightRule → lraf.SameRuleAs lrag)
      ∧ (f.label.2.2.isLeft → f.label.leftOnly = g.label.leftOnly →
          ¬ f.label.leftOnly.basic → f.label.rightFree.basic → g.label.rightFree.basic →
          lraf.isLeftRule → lrag.isLeftRule → lraf.SameRuleAs lrag) )

/-- The conditions U1 and U2 together. -/
def Tableau.UniCore {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  tab.U1 ∧ tab.U2

/-- A sanity check that U1 and U2 are not contradictory: both conditions only constrain
nodes with a loaded component, so a tableau in which no node is loaded satisfies them. -/
lemma Tableau.uniCore_of_all_free {H : History} {X : Sequent} {tab : Tableau H X}
    (h : ∀ f : FinePathIn tab, f.label.2.2 = none) : tab.UniCore := by
  refine ⟨fun f _ => ⟨?_, ?_⟩, fun f g lraf lrag _ _ => ⟨?_, ?_⟩⟩ <;>
    intro hf <;> rw [h f] at hf <;> simp [Olf.isRight, Olf.isLeft] at hf

/-- A tableau is *uniform* if it satisfies the conditions U1 and U2.

We also demand U1 and U2 for the flipped tableau `tab.flip`, in which the left and the
right components of all sequents are swapped. This is not an extra demand: U1 and U2 are
symmetric in the two components, so `tab.UniCore` and `tab.flip.UniCore` say the same
thing. Asking for both here only spares us the purely technical work of transporting U1
and U2 along `Tableau.flip`, which would need a `flip` operation on `FinePathIn`.
What it buys us is `Tableau.isUniform.flip` below, which is needed because the
interpolation proof flips the tableau when the loaded formula is on the left. -/
def Tableau.isUniform {H : History} {X : Sequent} (tab : Tableau H X) : Prop :=
  tab.UniCore ∧ tab.flip.UniCore

/-- Transporting `Tableau.UniCore` along an equality of tableaux. -/
lemma Tableau.UniCore.heq_transfer {H₁ X₁ H₂ X₂} {t₁ : Tableau H₁ X₁} {t₂ : Tableau H₂ X₂}
    (hH : H₁ = H₂) (hX : X₁ = X₂) (h : HEq t₁ t₂) (h₁ : t₁.UniCore) : t₂.UniCore := by
  subst hH
  subst hX
  cases eq_of_heq h
  exact h₁

/-- Uniformity is preserved by flipping the tableau. -/
lemma Tableau.isUniform.flip {H : History} {X : Sequent} {tab : Tableau H X}
    (h : tab.isUniform) : tab.flip.isUniform :=
  ⟨h.2, Tableau.UniCore.heq_transfer Hist_flip.symm Sequent.flip_flip.symm
    (HEq.symm (flip_aux_Tableau_flip_flip_heq tab)) h.1⟩

/-! ## Uniform tableaux by construction

To obtain uniform tableaux we follow approach (B): instead of repairing a given tableau we
describe how a uniform one is built, by fixing *which* local rule is applied at each node.
The conditions U1 and U2 only speak about the local rules applied at the nodes, and both are
conditions that can be read off a single rule application together with the sequent it is
applied to. This is what `LocalRuleApp.IsUniChoice` below says:

* the rule is applied to the unloaded component, unless that component is basic (U1); and
* if it is applied to the loaded component (the unloaded one then being basic) then it is
  *the* canonical rule for that component, given by `uniRightChoice` resp. `uniLeftChoice`.

Since the canonical rule only depends on the loaded component `Λᵢ(s)`, any two nodes with
the same loaded component use the same rule, which is U2. A tableau all of whose rule
applications are `IsUniChoice` is called `Tableau.IsUni`, and `Tableau.IsUni.uniCore` shows
that such a tableau indeed satisfies U1 and U2. The construction is symmetric under flipping
(`Tableau.IsUni.flip`), which gives the second half of `Tableau.isUniform`. -/

/-! ### Flipping components, rules and rule applications -/

@[simp]
lemma LocalRuleApp.flip_O (lra : LocalRuleApp) : (lra.flip).O = lra.O.flip := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩; rfl

@[simp]
lemma LocalRuleApp.flip_X (lra : LocalRuleApp) : (lra.flip).X = lra.X.flip := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp [LocalRuleApp.flip, Sequent.flip]

@[simp]
lemma LocalRuleApp.flip_isRightRule (lra : LocalRuleApp) :
    (lra.flip).isRightRule = lra.isLeftRule := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;> simp [LocalRuleApp.flip, LocalRuleApp.isRightRule, LocalRuleApp.isLeftRule,
      LocalRule.isRightRule, LocalRule.isLeftRule, LocalRule.flip]

@[simp]
lemma LocalRuleApp.flip_isLeftRule (lra : LocalRuleApp) :
    (lra.flip).isLeftRule = lra.isRightRule := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;> simp [LocalRuleApp.flip, LocalRuleApp.isRightRule, LocalRuleApp.isLeftRule,
      LocalRule.isRightRule, LocalRule.isLeftRule, LocalRule.flip]

@[simp]
lemma Sequent.flip_leftFree {X : Sequent} : X.flip.leftFree = X.rightFree.flip := by
  rcases X with ⟨L, R, O⟩; rfl

@[simp]
lemma Sequent.flip_rightFree {X : Sequent} : X.flip.rightFree = X.leftFree.flip := by
  rcases X with ⟨L, R, O⟩; rfl

@[simp]
lemma Sequent.flip_rightOnly {X : Sequent} : X.flip.rightOnly = X.leftOnly.flip := by
  rcases X with ⟨L, R, O⟩; rfl

@[simp]
lemma Sequent.flip_leftOnly {X : Sequent} : X.flip.leftOnly = X.rightOnly.flip := by
  rcases X with ⟨L, R, O⟩; rfl

/-- Being the same rule is preserved by flipping. -/
lemma LocalRuleApp.SameRuleAs.flip {lra₁ lra₂ : LocalRuleApp} (h : lra₁.SameRuleAs lra₂) :
    lra₁.flip.SameRuleAs lra₂.flip := by
  obtain ⟨hL, hR, hO, hress, hlr⟩ := h
  rcases lra₁ with ⟨L₁, R₁, O₁, Lcond₁, Rcond₁, Ocond₁, ress₁, lr₁, C₁, hC₁, pre₁⟩
  rcases lra₂ with ⟨L₂, R₂, O₂, Lcond₂, Rcond₂, Ocond₂, ress₂, lr₂, C₂, hC₂, pre₂⟩
  simp_all only
  subst hL; subst hR; subst hO; subst hress
  cases eq_of_heq hlr
  exact ⟨rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- Being the same rule is reflexive. -/
lemma LocalRuleApp.SameRuleAs.refl (lra : LocalRuleApp) : lra.SameRuleAs lra :=
  ⟨rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- Being the same rule is symmetric. -/
lemma LocalRuleApp.SameRuleAs.symm {lra₁ lra₂ : LocalRuleApp} (h : lra₁.SameRuleAs lra₂) :
    lra₂.SameRuleAs lra₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

/-- Being the same rule is transitive. -/
lemma LocalRuleApp.SameRuleAs.trans {lra₁ lra₂ lra₃ : LocalRuleApp}
    (h : lra₁.SameRuleAs lra₂) (h' : lra₂.SameRuleAs lra₃) : lra₁.SameRuleAs lra₃ :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.trans h'.2.2.2.2⟩

/-! ### The canonical rule for a component -/

/-- The canonical local rule to be applied to the right component of a sequent.
We use the first right rule in the list `LocalRuleApp.all` of all applicable rules.
Which rule exactly is picked does not matter for uniformity; all that matters is that
this is a *function* of the sequent — and that it is applied to sequents of the form
`X.rightOnly`, so that it only depends on the right component. -/
def uniRightChoice (Y : Sequent) : Option LocalRuleApp :=
  (LocalRuleApp.all Y).find? (fun lra => lra.isRightRule)

/-- The canonical local rule to be applied to the left component of a sequent.
Defined as the flip of `uniRightChoice`, which makes the whole construction symmetric. -/
def uniLeftChoice (Y : Sequent) : Option LocalRuleApp :=
  (uniRightChoice Y.flip).map LocalRuleApp.flip

lemma uniLeftChoice_flip (Y : Sequent) :
    uniLeftChoice Y.flip = (uniRightChoice Y).map LocalRuleApp.flip := by
  simp [uniLeftChoice]

lemma uniRightChoice_flip (Y : Sequent) :
    uniRightChoice Y.flip = (uniLeftChoice Y).map LocalRuleApp.flip := by
  simp [uniLeftChoice, Option.map_map, Function.comp_def, LocalRuleApp.flip_flip]

/-! ### Uniform rule applications -/

/-- The conditions on a single local rule application in a uniform tableau: the first two
fields are the local form of U1 and the last two are the local form of U2. -/
structure LocalRuleApp.IsUniChoice (lra : LocalRuleApp) : Prop where
  /-- If loaded on the right and the left component is not basic, a left rule is applied. -/
  leftFirst : lra.X.2.2.isRight → ¬ lra.X.leftFree.basic → lra.isLeftRule
  /-- If loaded on the left and the right component is not basic, a right rule is applied. -/
  rightFirst : lra.X.2.2.isLeft → ¬ lra.X.rightFree.basic → lra.isRightRule
  /-- A right rule applied at a node loaded on the right whose left component is basic is
  the canonical rule for the right component. -/
  rightCanon : lra.isRightRule → lra.X.2.2.isRight → lra.X.leftFree.basic →
      ∃ lrb, uniRightChoice lra.X.rightOnly = some lrb ∧ lra.SameRuleAs lrb
  /-- A left rule applied at a node loaded on the left whose right component is basic is
  the canonical rule for the left component. -/
  leftCanon : lra.isLeftRule → lra.X.2.2.isLeft → lra.X.rightFree.basic →
      ∃ lrb, uniLeftChoice lra.X.leftOnly = some lrb ∧ lra.SameRuleAs lrb

/-- The conditions on rule applications are symmetric under flipping. -/
lemma LocalRuleApp.IsUniChoice.flip {lra : LocalRuleApp} (h : lra.IsUniChoice) :
    lra.flip.IsUniChoice := by
  have hXf : lra.flip.X = lra.X.flip := LocalRuleApp.flip_X lra
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    have h1' : lra.X.2.2.isLeft := by
      rw [hXf] at h1; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h2' : ¬ lra.X.rightFree.basic := by
      rw [hXf] at h2; simpa using h2
    simpa using h.rightFirst h1' h2'
  · intro h1 h2
    have h1' : lra.X.2.2.isRight := by
      rw [hXf] at h1; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h2' : ¬ lra.X.leftFree.basic := by
      rw [hXf] at h2; simpa using h2
    simpa using h.leftFirst h1' h2'
  · intro h1 h2 h3
    have h1' : lra.isLeftRule := by simpa using h1
    have h2' : lra.X.2.2.isLeft := by
      rw [hXf] at h2; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h3' : lra.X.rightFree.basic := by
      rw [hXf] at h3; simpa using h3
    obtain ⟨lrb, hb, hsame⟩ := h.leftCanon h1' h2' h3'
    refine ⟨lrb.flip, ?_, hsame.flip⟩
    rw [hXf, Sequent.flip_rightOnly, uniRightChoice_flip, hb]
    rfl
  · intro h1 h2 h3
    have h1' : lra.isRightRule := by simpa using h1
    have h2' : lra.X.2.2.isRight := by
      rw [hXf] at h2; rcases hO : lra.O with _|(a|b) <;> simp_all [Olf.flip, Sequent.flip]
    have h3' : lra.X.leftFree.basic := by
      rw [hXf] at h3; simpa using h3
    obtain ⟨lrb, hb, hsame⟩ := h.rightCanon h1' h2' h3'
    refine ⟨lrb.flip, ?_, hsame.flip⟩
    rw [hXf, Sequent.flip_leftOnly, uniLeftChoice_flip, hb]
    rfl

/-! ### Basic sequents have basic components -/

lemma Sequent.leftFree_basic_of_basic {X : Sequent} (h : X.basic) : X.leftFree.basic := by
  rcases X with ⟨L, R, o⟩
  rcases h with ⟨hall, hcl⟩
  refine ⟨fun f hf => hall f (by simp_all), ?_⟩
  rintro (hbot | ⟨f, hf, hnf⟩)
  · exact hcl (Or.inl (by simp_all [instMembershipFormulaSequent]))
  · exact hcl (Or.inr ⟨f, by simp_all [instMembershipFormulaSequent]⟩)

lemma Sequent.rightFree_basic_of_basic {X : Sequent} (h : X.basic) : X.rightFree.basic := by
  rcases X with ⟨L, R, o⟩
  rcases h with ⟨hall, hcl⟩
  refine ⟨fun f hf => hall f (by simp_all), ?_⟩
  rintro (hbot | ⟨f, hf, hnf⟩)
  · exact hcl (Or.inl (by simp_all [instMembershipFormulaSequent]))
  · exact hcl (Or.inr ⟨f, by simp_all [instMembershipFormulaSequent]⟩)

/-- All local rule applications inside a local tableau are uniform choices. -/
def LocalTableau.IsUni : {X : Sequent} → LocalTableau X → Prop
  | _, (.sim _) => True
  | _, (.byLocalRule lra _ next) =>
      lra.IsUniChoice ∧ ∀ Y, ∀ h : Y ∈ lra.C, (next Y h).IsUni
termination_by X => X
decreasing_by
  subst_eqs
  apply localRuleApp.decreases_DM lra Y h

/-- All local rule applications inside a tableau are uniform choices. -/
def Tableau.IsUni : {H : History} → {X : Sequent} → Tableau H X → Prop
  | _, _, .loc _ _ lt next => lt.IsUni ∧ ∀ Y, ∀ h : Y ∈ endNodesOf lt, (next Y h).IsUni
  | _, _, .pdl _ _ _ next => next.IsUni
  | _, _, .lrep _ => True

lemma LocalTableau.IsUni.ltAt {X} {lt : LocalTableau X} (h : lt.IsUni) (lp : LocalPathIn lt) :
    (lp.ltAt).IsUni := by
  induction lp
  case nil => exact h
  case cons X lra X_def next Y Y_in tail IH =>
    rw [LocalTableau.IsUni] at h
    exact IH (h.2 Y Y_in)

lemma Tableau.IsUni.lra?_isUniChoice {H X} {tab : Tableau H X} (h : tab.IsUni)
    {f : FinePathIn tab} {lra : LocalRuleApp} (hf : f.lra? = some lra) : lra.IsUniChoice := by
  induction f
  case inLoc Hist X nrep nbas lt next lp lp_int =>
    rw [Tableau.IsUni] at h
    have hlt := h.1.ltAt lp
    simp only [FinePathIn.lra?] at hf
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas
    · rw [hltAt] at hf hlt
      simp only [Option.some.injEq] at hf
      subst hf
      rw [LocalTableau.IsUni] at hlt
      exact hlt.1
    · rw [hltAt] at hf; simp at hf
  case pdlHere => simp [FinePathIn.lra?] at hf
  case lrepHere => simp [FinePathIn.lra?] at hf
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    rw [Tableau.IsUni] at h
    exact IH (h.2 Y Y_in) hf
  case pdl IH =>
    rw [Tableau.IsUni] at h
    exact IH h hf

lemma FinePathIn.usesLeftRule_eq_of_lra? {H X} {tab : Tableau H X} {f : FinePathIn tab}
    {lra : LocalRuleApp} (hf : f.lra? = some lra) : f.usesLeftRule = lra.isLeftRule := by
  induction f
  case inLoc lp lp_int =>
    simp only [FinePathIn.lra?, FinePathIn.usesLeftRule] at *
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas <;> simp_all
  case pdlHere => simp [FinePathIn.lra?] at hf
  case lrepHere => simp [FinePathIn.lra?] at hf
  case loc IH => simpa [FinePathIn.usesLeftRule] using IH (by simpa [FinePathIn.lra?] using hf)
  case pdl IH => simpa [FinePathIn.usesLeftRule] using IH (by simpa [FinePathIn.lra?] using hf)

lemma FinePathIn.usesRightRule_eq_of_lra? {H X} {tab : Tableau H X} {f : FinePathIn tab}
    {lra : LocalRuleApp} (hf : f.lra? = some lra) : f.usesRightRule = lra.isRightRule := by
  induction f
  case inLoc lp lp_int =>
    simp only [FinePathIn.lra?, FinePathIn.usesRightRule] at *
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas <;> simp_all
  case pdlHere => simp [FinePathIn.lra?] at hf
  case lrepHere => simp [FinePathIn.lra?] at hf
  case loc IH => simpa [FinePathIn.usesRightRule] using IH (by simpa [FinePathIn.lra?] using hf)
  case pdl IH => simpa [FinePathIn.usesRightRule] using IH (by simpa [FinePathIn.lra?] using hf)

lemma FinePathIn.isLrep_or_basic_of_lra?_eq_none {H X} {tab : Tableau H X} {f : FinePathIn tab}
    (hf : f.lra? = none) : f.base.isLrep ∨ f.label.basic := by
  induction f
  case inLoc lp lp_int =>
    exfalso
    simp only [FinePathIn.lra?] at hf
    rcases hltAt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas
    · rw [hltAt] at hf; simp at hf
    · exact absurd lp_int (by simp [LocalPathIn.isInternal, hltAt, LocalTableau.hasRule])
  case pdlHere Hist X Y nrep bas r next => exact Or.inr bas
  case lrepHere => exact Or.inl (by simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep])
  case loc IH =>
    rcases IH (by simpa [FinePathIn.lra?] using hf) with h | h
    · exact Or.inl (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)
    · exact Or.inr (by simpa [FinePathIn.label] using h)
  case pdl IH =>
    rcases IH (by simpa [FinePathIn.lra?] using hf) with h | h
    · exact Or.inl (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)
    · exact Or.inr (by simpa [FinePathIn.label] using h)

theorem Tableau.IsUni.uniCore {H X} {tab : Tableau H X} (h : tab.IsUni) : tab.UniCore := by
  constructor
  · -- U1
    intro f hnlrep
    rcases hl : f.lra? with _ | lra
    · rcases FinePathIn.isLrep_or_basic_of_lra?_eq_none hl with hb | hbas
      · exact absurd hb hnlrep
      · exact ⟨fun _ hcon => absurd (Sequent.leftFree_basic_of_basic hbas) hcon,
               fun _ hcon => absurd (Sequent.rightFree_basic_of_basic hbas) hcon⟩
    · have hu := h.lra?_isUniChoice hl
      have hX : f.label = lra.X := (f.lra?_spec hl).1
      constructor
      · intro h1 h2
        rw [FinePathIn.usesLeftRule_eq_of_lra? hl]
        exact hu.leftFirst (hX ▸ h1) (hX ▸ h2)
      · intro h1 h2
        rw [FinePathIn.usesRightRule_eq_of_lra? hl]
        exact hu.rightFirst (hX ▸ h1) (hX ▸ h2)
  · -- U2
    intro f g lraf lrag hf hg
    have huf := h.lra?_isUniChoice hf
    have hug := h.lra?_isUniChoice hg
    have hXf : f.label = lraf.X := (f.lra?_spec hf).1
    have hXg : g.label = lrag.X := (g.lra?_spec hg).1
    constructor
    · intro hfR hfg _ hfl hgl hfRule hgRule
      have hOeq : f.label.2.2 = g.label.2.2 := congrArg (fun Y => Y.2.2) hfg
      have hgR : g.label.2.2.isRight := hOeq ▸ hfR
      obtain ⟨lrb, hb, hsame⟩ := huf.rightCanon hfRule (hXf ▸ hfR) (hXf ▸ hfl)
      obtain ⟨lrb', hb', hsame'⟩ := hug.rightCanon hgRule (hXg ▸ hgR) (hXg ▸ hgl)
      have : lrb = lrb' := by
        rw [← hXf, hfg] at hb
        rw [← hXg] at hb'
        exact Option.some.inj (hb.symm.trans hb')
      exact hsame.trans (this ▸ hsame'.symm)
    · intro hfL hfg _ hfr hgr hfRule hgRule
      have hOeq : f.label.2.2 = g.label.2.2 := congrArg (fun Y => Y.2.2) hfg
      have hgL : g.label.2.2.isLeft := hOeq ▸ hfL
      obtain ⟨lrb, hb, hsame⟩ := huf.leftCanon hfRule (hXf ▸ hfL) (hXf ▸ hfr)
      obtain ⟨lrb', hb', hsame'⟩ := hug.leftCanon hgRule (hXg ▸ hgL) (hXg ▸ hgr)
      have : lrb = lrb' := by
        rw [← hXf, hfg] at hb
        rw [← hXg] at hb'
        exact Option.some.inj (hb.symm.trans hb')
      exact hsame.trans (this ▸ hsame'.symm)

lemma LocalTableau.IsUni_cast {A B : Sequent} (h : A = B) (t : LocalTableau A) :
    (h ▸ t).IsUni ↔ t.IsUni := by subst h; rfl

lemma Tableau.IsUni_cast {H} {A B : Sequent} (h : A = B) (t : Tableau H A) :
    (h ▸ t).IsUni ↔ t.IsUni := by subst h; rfl

lemma LocalTableau.IsUni.flip {X} {lt : LocalTableau X} (h : lt.IsUni) : (lt.flip).IsUni := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    rw [LocalTableau.IsUni] at h
    rw [LocalTableau.flip, LocalTableau.IsUni]
    refine ⟨h.1.flip, ?_⟩
    intro Y Y_in
    rw [LocalTableau.IsUni_cast]
    exact IH _ (Sequent.flip_mem_of_mem_map_flip Y_in) (h.2 _ _)
  case sim bas => rw [LocalTableau.flip, LocalTableau.IsUni]; trivial

lemma Tableau.IsUni.flip {H X} {tab : Tableau H X} (h : tab.IsUni) : (tab.flip).IsUni := by
  induction tab
  case loc Hist X nrep nbas lt next IH =>
    rw [Tableau.IsUni] at h
    rw [Tableau.flip, Tableau.IsUni]
    refine ⟨h.1.flip, ?_⟩
    intro Y Y_in
    rw [Tableau.IsUni_cast]
    exact IH _ (endNodesOf_flip Y_in) (h.2 _ _)
  case pdl IH =>
    rw [Tableau.IsUni] at h
    rw [Tableau.flip, Tableau.IsUni]
    exact IH h
  case lrep => trivial

/-- A tableau all of whose local rule applications are uniform choices is uniform. -/
theorem Tableau.IsUni.isUniform {X} {tab : Tableau .nil X} (h : tab.IsUni) : tab.isUniform :=
  ⟨h.uniCore, h.flip.uniCore⟩

/-! ## Building a uniform tableau

We now show `Tableau.exists_isUni`: for every tableau there is one that applies the rules in
the canonical order. The construction is deterministic: `uniChoiceAt` picks, at each sequent,
the canonical rule application (first a rule for the unloaded component, and once that is
basic the canonical rule for the loaded component), and `uniLocalTab` iterates this to a
local tableau all of whose rule applications are uniform choices (`uniLocalTab_isUni`).

Given an arbitrary tableau we then re-build it, replacing the local tableau at each `loc`
step by the canonical one. Because the end nodes of the canonical local tableau need not be
literally the same lists as the end nodes of the original one, we prove the statement in the
more flexible form `Tableau.exists_isUni_of_msEq`, allowing the sequent and the history to
change up to `Sequent.multisetEqTo`, i.e. up to permutation of the two lists in a sequent.
That the calculus does not care about such permutations is `PdlRule.exists_of_multisetEqTo`
and `lpr_of_multisetEqTo`.

The only step that is left open is `uniLocalTab_endNode_dominated`. -/

/-- Put a local rule application into a different context, keeping the rule itself. -/
def LocalRuleApp.inContext (lra : LocalRuleApp) (L R : List Formula) (O : Olf)
    (hL : lra.Lcond.Subperm L) (hR : lra.Rcond.Subperm R) (hO : lra.Ocond ⊆ O) :
    LocalRuleApp :=
  { L := L, R := R, O := O,
    Lcond := lra.Lcond, Rcond := lra.Rcond, Ocond := lra.Ocond,
    ress := lra.ress, lr := lra.lr,
    C := applyLocalRule lra.lr (L, R, O), hC := rfl,
    preconditionProof := ⟨hL, hR, hO⟩ }

open Classical in
/-- Put a local rule application into the context of the sequent `X`, if possible. -/
noncomputable def LocalRuleApp.toContext (lra : LocalRuleApp) (X : Sequent) : LocalRuleApp :=
  if h : lra.Lcond.Subperm X.1 ∧ lra.Rcond.Subperm X.2.1 ∧ lra.Ocond ⊆ X.2.2 then
    lra.inContext X.1 X.2.1 X.2.2 h.1 h.2.1 h.2.2
  else lra

lemma LocalRuleApp.toContext_sameRuleAs (lra : LocalRuleApp) (X : Sequent) :
    (lra.toContext X).SameRuleAs lra := by
  unfold LocalRuleApp.toContext
  split
  · exact ⟨rfl, rfl, rfl, rfl, HEq.rfl⟩
  · exact LocalRuleApp.SameRuleAs.refl lra

@[simp]
lemma LocalRuleApp.toContext_isLeftRule (lra : LocalRuleApp) (X : Sequent) :
    (lra.toContext X).isLeftRule = lra.isLeftRule := by
  unfold LocalRuleApp.toContext
  split <;> rfl

@[simp]
lemma LocalRuleApp.toContext_isRightRule (lra : LocalRuleApp) (X : Sequent) :
    (lra.toContext X).isRightRule = lra.isRightRule := by
  unfold LocalRuleApp.toContext
  split <;> rfl

lemma LocalRuleApp.toContext_X (lra : LocalRuleApp) (X : Sequent)
    (h : lra.Lcond.Subperm X.1 ∧ lra.Rcond.Subperm X.2.1 ∧ lra.Ocond ⊆ X.2.2) :
    (lra.toContext X).X = X := by
  unfold LocalRuleApp.toContext
  rw [dif_pos h]
  rfl

lemma uniRightChoice_spec {Y : Sequent} {lra : LocalRuleApp} (h : uniRightChoice Y = some lra) :
    lra.X = Y ∧ lra.isRightRule := by
  unfold uniRightChoice at h
  exact ⟨LocalRuleApp.all_X Y lra (List.mem_of_find?_eq_some h), by
    simpa using List.find?_some h⟩

lemma uniRightChoice_isSome {Y : Sequent} {lra : LocalRuleApp} (hX : lra.X = Y)
    (hr : lra.isRightRule) : (uniRightChoice Y).isSome := by
  unfold uniRightChoice
  rcases h : (LocalRuleApp.all Y).find? (fun lra => lra.isRightRule) with _ | lrb
  · exfalso
    rw [List.find?_eq_none] at h
    exact h lra (hX ▸ lra.all_spec) (by simpa using hr)
  · rw [h]; rfl

lemma uniLeftChoice_spec {Y : Sequent} {lra : LocalRuleApp} (h : uniLeftChoice Y = some lra) :
    lra.X = Y ∧ lra.isLeftRule := by
  unfold uniLeftChoice at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨lrb, hb, rfl⟩ := h
  obtain ⟨hX, hr⟩ := uniRightChoice_spec hb
  refine ⟨?_, by simpa using hr⟩
  rw [LocalRuleApp.flip_X, hX, Sequent.flip_flip]

lemma uniLeftChoice_isSome {Y : Sequent} {lra : LocalRuleApp} (hX : lra.X = Y)
    (hl : lra.isLeftRule) : (uniLeftChoice Y).isSome := by
  unfold uniLeftChoice
  have : (uniRightChoice Y.flip).isSome := by
    refine uniRightChoice_isSome (lra := lra.flip) ?_ (by simpa using hl)
    rw [LocalRuleApp.flip_X, hX]
  simpa using this

/-! ### Shapes of left and right rules -/

lemma LocalRuleApp.isLeftRule_shape {lra : LocalRuleApp} (h : lra.isLeftRule) :
    lra.Rcond = [] ∧ (lra.Ocond = none ∨ lra.Ocond.isLeft) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;>
    simp_all [LocalRuleApp.isLeftRule, LocalRule.isLeftRule, Olf.isLeft]

lemma LocalRuleApp.isRightRule_shape {lra : LocalRuleApp} (h : lra.isRightRule) :
    lra.Lcond = [] ∧ (lra.Ocond = none ∨ lra.Ocond.isRight) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;>
    simp_all [LocalRuleApp.isRightRule, LocalRule.isRightRule, Olf.isRight]

/-- Any local rule applicable to a sequent of the shape `(L, [], none)` is a left rule. -/
lemma LocalRuleApp.isLeftRule_of_X_eq {lra : LocalRuleApp} {L : List Formula}
    (h : lra.X = (L, [], none)) : lra.isLeftRule := by
  rcases lra with ⟨L', R', O', Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨preL, preR, preO⟩ := pre
  cases lr
  case oneSidedL => simp [LocalRuleApp.isLeftRule, LocalRule.isLeftRule]
  case oneSidedR orule YS_def =>
    exact absurd (List.subperm_nil.mp preR) (orule.precond_ne_nil)
  case LRnegL φ => simp at preR
  case LRnegR φ => simp at preR
  case loadedL => simp at preO
  case loadedR => simp at preO

/-! ### Moving rules between a sequent and its components -/

lemma LocalRuleApp.toContext_X_of_leftOnly {lra : LocalRuleApp} {X : Sequent}
    (h : lra.X = X.leftOnly) : (lra.toContext X).X = X := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hL : lra.L = X.1 := congrArg (fun Y => Y.1) h
  have hR : lra.R = [] := congrArg (fun Y => Y.2.1) h
  have hO : lra.O = X.2.2 := congrArg (fun Y => Y.2.2) h
  refine lra.toContext_X X ⟨hL ▸ preL, ?_, hO ▸ preO⟩
  rw [hR] at preR
  rw [List.subperm_nil.mp preR]
  exact List.nil_subperm

lemma LocalRuleApp.toContext_X_of_rightOnly {lra : LocalRuleApp} {X : Sequent}
    (h : lra.X = X.rightOnly) : (lra.toContext X).X = X := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hL : lra.L = [] := congrArg (fun Y => Y.1) h
  have hR : lra.R = X.2.1 := congrArg (fun Y => Y.2.1) h
  have hO : lra.O = X.2.2 := congrArg (fun Y => Y.2.2) h
  refine lra.toContext_X X ⟨?_, hR ▸ preR, hO ▸ preO⟩
  rw [hL] at preL
  rw [List.subperm_nil.mp preL]
  exact List.nil_subperm

lemma LocalRuleApp.toContext_leftOnly_X {lra : LocalRuleApp} {X : Sequent}
    (hX : lra.X = X) (hl : lra.isLeftRule) : (lra.toContext X.leftOnly).X = X.leftOnly := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  subst hX
  refine lra.toContext_X _ ⟨preL, ?_, preO⟩
  rw [(LocalRuleApp.isLeftRule_shape hl).1]
  exact List.nil_subperm

lemma LocalRuleApp.toContext_rightOnly_X {lra : LocalRuleApp} {X : Sequent}
    (hX : lra.X = X) (hr : lra.isRightRule) : (lra.toContext X.rightOnly).X = X.rightOnly := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  subst hX
  refine lra.toContext_X _ ⟨?_, preR, preO⟩
  rw [(LocalRuleApp.isRightRule_shape hr).1]
  exact List.nil_subperm

lemma LocalRuleApp.toContext_leftFree_X {lra : LocalRuleApp} {X : Sequent}
    (hX : lra.X = X) (hl : lra.isLeftRule) (hO : lra.Ocond = none) :
    (lra.toContext X.leftFree).X = X.leftFree := by
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  subst hX
  refine lra.toContext_X _ ⟨preL, ?_, by simp [hO, Sequent.leftFree]⟩
  rw [(LocalRuleApp.isLeftRule_shape hl).1]
  exact List.nil_subperm

/-! ### When is the canonical choice available? -/

lemma exists_localRuleApp_of_not_basic {Y : Sequent} (h : ¬ Y.basic) :
    ∃ lra : LocalRuleApp, lra.X = Y := by
  by_contra hcon
  exact h (basic_iff_noLocalRuleApp.mpr hcon)

lemma uniLeftChoice_leftOnly_isSome {X : Sequent} (h : ¬ X.leftFree.basic) :
    (uniLeftChoice X.leftOnly).isSome := by
  obtain ⟨lra, hlra⟩ := exists_localRuleApp_of_not_basic h
  have hl : lra.isLeftRule := LocalRuleApp.isLeftRule_of_X_eq hlra
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hL : lra.L = X.1 := congrArg (fun Y => Y.1) hlra
  have hR : lra.R = [] := congrArg (fun Y => Y.2.1) hlra
  have hO : lra.O = none := congrArg (fun Y => Y.2.2) hlra
  have hOc : lra.Ocond = none := by
    rw [hO] at preO
    rcases hOcond : lra.Ocond with _|(a|b) <;> simp_all
  refine uniLeftChoice_isSome (lra := lra.toContext X.leftOnly) ?_ (by simpa using hl)
  refine lra.toContext_X X.leftOnly ⟨hL ▸ preL, ?_, by simp [hOc, Sequent.leftOnly]⟩
  rw [(LocalRuleApp.isLeftRule_shape hl).1]
  exact List.nil_subperm

lemma uniLeftChoice_leftOnly_eq_none {X : Sequent} (hb : X.leftFree.basic)
    (hO : ¬ X.2.2.isLeft) : uniLeftChoice X.leftOnly = none := by
  rcases hc : uniLeftChoice X.leftOnly with _ | lra
  · rfl
  exfalso
  obtain ⟨hX, hl⟩ := uniLeftChoice_spec hc
  obtain ⟨hRcond, hOcond⟩ := LocalRuleApp.isLeftRule_shape hl
  obtain ⟨preL, preR, preO⟩ := lra.preconditionProof
  have hLL : lra.L = X.1 := congrArg (fun Y => Y.1) hX
  have hOO : lra.O = X.2.2 := congrArg (fun Y => Y.2.2) hX
  have hOc : lra.Ocond = none := by
    rcases hOcond with h' | h'
    · exact h'
    · exfalso
      rw [hOO] at preO
      rcases hOcond' : lra.Ocond with _|(a|b) <;> rcases hX22 : X.2.2 with _|(c|d) <;>
        simp_all [Olf.isLeft]
  have : ∃ lra' : LocalRuleApp, lra'.X = X.leftFree := by
    refine ⟨lra.toContext X.leftFree, ?_⟩
    refine lra.toContext_X X.leftFree ⟨hLL ▸ preL, ?_, by simp [hOc, Sequent.leftFree]⟩
    rw [hRcond]
    exact List.nil_subperm
  exact (basic_iff_noLocalRuleApp.mp hb) this

lemma uniRightChoice_rightOnly_isSome {X : Sequent} {lra : LocalRuleApp} (hX : lra.X = X)
    (hr : lra.isRightRule) : (uniRightChoice X.rightOnly).isSome :=
  uniRightChoice_isSome (lra := lra.toContext X.rightOnly)
    (lra.toContext_rightOnly_X hX hr) (by simpa using hr)

/-! ### The canonical rule choice -/

open Classical in
/-- The canonical rule application for a sequent that is free or loaded on the right:
first reduce the left component, then use the canonical rule for the right component. -/
noncomputable def uniChoiceRL (X : Sequent) : Option LocalRuleApp :=
  match uniLeftChoice X.leftOnly with
  | some lra => some (lra.toContext X)
  | none =>
    match uniRightChoice X.rightOnly with
    | some lra => some (lra.toContext X)
    | none => (LocalRuleApp.all X).head?

lemma uniChoiceRL_X {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceRL X = some lra) :
    lra.X = X := by
  unfold uniChoiceRL at h
  rcases hl : uniLeftChoice X.leftOnly with _ | lrl
  · rcases hr : uniRightChoice X.rightOnly with _ | lrr
    · rw [hl, hr] at h
      simp only at h
      exact LocalRuleApp.all_X X lra (List.mem_of_mem_head? h)
    · rw [hl, hr] at h
      simp only [Option.some.injEq] at h
      subst h
      exact LocalRuleApp.toContext_X_of_rightOnly (uniRightChoice_spec hr).1
  · rw [hl] at h
    simp only [Option.some.injEq] at h
    subst h
    exact LocalRuleApp.toContext_X_of_leftOnly (uniLeftChoice_spec hl).1

lemma uniChoiceRL_isSome {X : Sequent} (h : ¬ X.basic) : (uniChoiceRL X).isSome := by
  unfold uniChoiceRL
  rcases hl : uniLeftChoice X.leftOnly with _ | lrl
  · rcases hr : uniRightChoice X.rightOnly with _ | lrr
    · simp only [Option.isSome]
      rcases hh : (LocalRuleApp.all X).head? with _ | lra
      · exfalso
        rw [List.head?_eq_none_iff] at hh
        exact LocalRuleApp.all_nonempty_of_nonbasic h hh
      · rfl
    · rfl
  · rfl

lemma uniChoiceRL_isUniChoice {X : Sequent} {lra : LocalRuleApp} (hnl : ¬ X.2.2.isLeft)
    (h : uniChoiceRL X = some lra) : lra.IsUniChoice := by
  have hX : lra.X = X := uniChoiceRL_X h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- leftFirst
    intro _ h2
    have h2' : ¬ X.leftFree.basic := by rwa [hX] at h2
    obtain ⟨lrl, hl⟩ := Option.isSome_iff_exists.mp (uniLeftChoice_leftOnly_isSome h2')
    unfold uniChoiceRL at h
    rw [hl] at h
    simp only [Option.some.injEq] at h
    subst h
    simpa using (uniLeftChoice_spec hl).2
  · -- rightFirst
    intro h1
    exact absurd (hX ▸ h1) hnl
  · -- rightCanon
    intro hr _ _
    have hnleft : uniLeftChoice X.leftOnly = none := by
      rcases hl : uniLeftChoice X.leftOnly with _ | lrl
      · rfl
      · exfalso
        unfold uniChoiceRL at h
        rw [hl] at h
        simp only [Option.some.injEq] at h
        subst h
        exact LocalRuleApp.not_left_and_right _ ⟨by simpa using (uniLeftChoice_spec hl).2, hr⟩
    rcases hrr : uniRightChoice X.rightOnly with _ | lrr
    · exfalso
      have : (uniRightChoice X.rightOnly).isSome := uniRightChoice_rightOnly_isSome hX hr
      rw [hrr] at this
      exact Bool.false_ne_true this
    · refine ⟨lrr, by rw [hX, hrr], ?_⟩
      unfold uniChoiceRL at h
      rw [hnleft, hrr] at h
      simp only [Option.some.injEq] at h
      subst h
      exact LocalRuleApp.toContext_sameRuleAs lrr X
  · -- leftCanon
    intro _ h2
    exact absurd (hX ▸ h2) hnl

open Classical in
/-- The canonical local rule application at a sequent: when the sequent is loaded on the
left we flip, use `uniChoiceRL` and flip back. -/
noncomputable def uniChoiceAt (X : Sequent) : Option LocalRuleApp :=
  if X.2.2.isLeft then (uniChoiceRL X.flip).map LocalRuleApp.flip else uniChoiceRL X

lemma uniChoiceAt_X {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceAt X = some lra) :
    lra.X = X := by
  unfold uniChoiceAt at h
  split at h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨lrb, hb, rfl⟩ := h
    rw [LocalRuleApp.flip_X, uniChoiceRL_X hb, Sequent.flip_flip]
  · exact uniChoiceRL_X h

lemma uniChoiceAt_isSome {X : Sequent} (h : ¬ X.basic) : (uniChoiceAt X).isSome := by
  unfold uniChoiceAt
  split
  · simpa using uniChoiceRL_isSome (X := X.flip) (by rwa [basic_flip])
  · exact uniChoiceRL_isSome h

lemma uniChoiceAt_isUniChoice {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceAt X = some lra) :
    lra.IsUniChoice := by
  unfold uniChoiceAt at h
  split at h
  · rename_i hleft
    rw [Option.map_eq_some_iff] at h
    obtain ⟨lrb, hb, rfl⟩ := h
    refine LocalRuleApp.IsUniChoice.flip (uniChoiceRL_isUniChoice ?_ hb)
    clear hb
    rcases X with ⟨L, R, O⟩
    rcases O with _ | (a | b) <;> simp_all [Sequent.flip, Olf.flip, Olf.isLeft]
  · rename_i hleft
    exact uniChoiceRL_isUniChoice hleft h

lemma uniChoiceAt_C_lt {X : Sequent} {lra : LocalRuleApp} (h : uniChoiceAt X = some lra)
    {Y : Sequent} (hY : Y ∈ lra.C) : lt_Sequent Y X := by
  have hdec := localRuleApp.decreases_DM lra Y hY
  rwa [uniChoiceAt_X h] at hdec

open Classical in
/-- The canonical local tableau: always apply the canonical rule `uniChoiceAt`. -/
noncomputable def uniLocalTab : (X : Sequent) → LocalTableau X
  | X =>
    if bas : X.basic then .sim bas
    else
      have hX : ((uniChoiceAt X).get (uniChoiceAt_isSome bas)).X = X :=
        uniChoiceAt_X (Option.some_get (uniChoiceAt_isSome bas)).symm
      .byLocalRule ((uniChoiceAt X).get (uniChoiceAt_isSome bas)) hX.symm
        (fun Y _ => uniLocalTab Y)
termination_by X => X
decreasing_by
  exact uniChoiceAt_C_lt (Option.some_get _).symm (by assumption)

lemma uniLocalTab_isUni (X : Sequent) : (uniLocalTab X).IsUni := by
  rw [uniLocalTab]
  split
  · rw [LocalTableau.IsUni]; trivial
  · rename_i bas
    rw [LocalTableau.IsUni]
    refine ⟨uniChoiceAt_isUniChoice (Option.some_get (uniChoiceAt_isSome bas)).symm, ?_⟩
    intro Y hY
    exact uniLocalTab_isUni Y
termination_by X
decreasing_by
  exact uniChoiceAt_C_lt (Option.some_get _).symm (by assumption)

/-! ## Transporting tableaux along multiset-equal sequents -/

lemma Sequent.multisetEqTo_iff {L R O L' R' O'} :
    Sequent.multisetEqTo (L, R, O) (L', R', O') ↔ L.Perm L' ∧ R.Perm R' ∧ O = O' := by
  simp [Sequent.multisetEqTo, Multiset.coe_eq_coe]

lemma Sequent.multisetEqTo_trans {X Y Z : Sequent} (h1 : X.multisetEqTo Y)
    (h2 : Y.multisetEqTo Z) : X.multisetEqTo Z := by
  rcases X with ⟨L, R, O⟩; rcases Y with ⟨L', R', O'⟩; rcases Z with ⟨L'', R'', O''⟩
  rw [Sequent.multisetEqTo_iff] at *
  exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- Histories that are pointwise multiset-equal. -/
abbrev History.multisetEqTo (H H' : History) : Prop := List.Forall₂ Sequent.multisetEqTo H H'

lemma History.multisetEqTo.length {H H' : History} (h : H.multisetEqTo H') :
    H.length = H'.length := h.length_eq

lemma rep_of_multisetEqTo {H H' : History} {X X' : Sequent} (hH : H.multisetEqTo H')
    (hX : X.multisetEqTo X') (h : rep H' X') : rep H X := by
  obtain ⟨Y', Y'_in, hY'⟩ := h
  obtain ⟨Y, Y_in, hY⟩ : ∃ Y ∈ H, Y.multisetEqTo Y' := by
    induction hH with
    | nil => simp at Y'_in
    | cons hd tl IH =>
        rename_i a b l₁ l₂
        rcases List.mem_cons.mp Y'_in with rfl | hmem
        · exact ⟨a, List.mem_cons_self, hd⟩
        · obtain ⟨Y, Y_in, hY⟩ := IH hmem
          exact ⟨Y, List.mem_cons_of_mem _ Y_in, hY⟩
  refine ⟨Y, Y_in, ?_⟩
  refine Sequent.setEqTo_trans _ _ _ (Sequent.setEqTo_of_multisetEqTo _ _ hY) ?_
  refine Sequent.setEqTo_trans _ _ _ hY' ?_
  exact (Sequent.setEqTo_symm _ _).mp (Sequent.setEqTo_of_multisetEqTo _ _ hX)

lemma setEqTo_of_msEq {X Y : Sequent} (h : X.multisetEqTo Y) : X.setEqTo Y :=
  Sequent.setEqTo_of_multisetEqTo _ _ h

lemma msEq_get {H H' : History} (hH : H.multisetEqTo H') (k : Fin H.length)
    (hk : (k : Nat) < H'.length) : (H.get k).multisetEqTo (H'.get ⟨k, hk⟩) :=
  (List.forall₂_iff_get.mp hH).2 k k.2 hk

/-- Loaded path repeats transfer along multiset-equal histories and sequents. -/
def lpr_of_multisetEqTo {H H' : History} {X X' : Sequent} (hH : H.multisetEqTo H')
    (hX : X.multisetEqTo X') (lpr : LoadedPathRepeat H' X') : LoadedPathRepeat H X := by
  have hlen : H.length = H'.length := hH.length_eq
  obtain ⟨k, hk_eq, hk_loaded⟩ := lpr
  refine ⟨⟨k.1, by omega⟩, ?_, ?_⟩
  · refine Sequent.setEqTo_trans _ _ _ (setEqTo_of_msEq (msEq_get hH ⟨k.1, by omega⟩ (by omega))) ?_
    refine Sequent.setEqTo_trans _ _ _ ?_ ((Sequent.setEqTo_symm _ _).mp (setEqTo_of_msEq hX))
    simpa using hk_eq
  · intro m hm
    have h1 : (H.get m).multisetEqTo (H'.get ⟨m.1, by omega⟩) := msEq_get hH m (by omega)
    rw [setEqTo_isLoaded_iff (setEqTo_of_msEq h1)]
    exact hk_loaded ⟨m.1, by omega⟩ (by simpa using hm)

lemma History.multisetEqTo.symm {H H' : History} (h : H.multisetEqTo H') : H'.multisetEqTo H := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hd _ IH => exact List.Forall₂.cons ((Sequent.multisetEqTo_symm _ _).mp hd) IH

lemma flprep_of_multisetEqTo {H H' : History} {X X' : Sequent} (hH : H.multisetEqTo H')
    (hX : X.multisetEqTo X') (h : flprep H' X') : flprep H X := by
  rcases h with ⟨hrep, hfree⟩ | lpr
  · refine Or.inl ⟨rep_of_multisetEqTo hH hX hrep, ?_⟩
    unfold Sequent.isFree at *
    rw [setEqTo_isLoaded_iff (setEqTo_of_msEq hX)]
    exact hfree
  · exact Or.inr (lpr.elim fun l => ⟨lpr_of_multisetEqTo hH hX l⟩)

lemma projection_perm {A : Nat} {L L' : List Formula} (h : L.Perm L') :
    (projection A L).Perm (projection A L') := by
  have : ∀ (M : List Formula), projection A M = (M.map (formProjection A)).filterMap id :=
    fun _ => rfl
  rw [this, this]
  exact ((h.map _).filterMap id)

/-- PDL rules can be applied to multiset-equal sequents, with multiset-equal results. -/
lemma PdlRule.exists_of_multisetEqTo {X X' Y : Sequent} (hX : X.multisetEqTo X')
    (r : PdlRule X Y) : ∃ Y', Nonempty (PdlRule X' Y') ∧ Y.multisetEqTo Y' := by
  rcases X' with ⟨L', R', O'⟩
  cases r
  case loadL L δ α φ R hin hnb hY =>
    rw [Sequent.multisetEqTo_iff] at hX
    obtain ⟨hL, hR, hO⟩ := hX
    subst hY
    subst hO
    exact ⟨(L'.erase (~⌈⌈δ⌉⌉⌈α⌉φ), R', some (Sum.inl (~'⌊⌊δ⌋⌋⌊α⌋AnyFormula.normal φ))),
      ⟨PdlRule.loadL (hL.mem_iff.mp hin) hnb rfl⟩,
      Sequent.multisetEqTo_iff.mpr ⟨hL.erase _, hR, rfl⟩⟩
  case loadR R δ α φ L hin hnb hY =>
    rw [Sequent.multisetEqTo_iff] at hX
    obtain ⟨hL, hR, hO⟩ := hX
    subst hY
    subst hO
    exact ⟨(L', R'.erase (~⌈⌈δ⌉⌉⌈α⌉φ), some (Sum.inr (~'⌊⌊δ⌋⌋⌊α⌋AnyFormula.normal φ))),
      ⟨PdlRule.loadR (hR.mem_iff.mp hin) hnb rfl⟩,
      Sequent.multisetEqTo_iff.mpr ⟨hL, hR.erase _, rfl⟩⟩
  case freeL L R δ α φ hX_def hY =>
    subst hX_def
    rw [Sequent.multisetEqTo_iff] at hX
    obtain ⟨hL, hR, hO⟩ := hX
    subst hY
    subst hO
    exact ⟨(List.insert (~⌈⌈δ⌉⌉⌈α⌉φ) L', R', none), ⟨PdlRule.freeL rfl rfl⟩,
      Sequent.multisetEqTo_iff.mpr ⟨hL.insert _, hR, rfl⟩⟩
  case freeR L R δ α φ hX_def hY =>
    subst hX_def
    rw [Sequent.multisetEqTo_iff] at hX
    obtain ⟨hL, hR, hO⟩ := hX
    subst hY
    subst hO
    exact ⟨(L', List.insert (~⌈⌈δ⌉⌉⌈α⌉φ) R', none), ⟨PdlRule.freeR rfl rfl⟩,
      Sequent.multisetEqTo_iff.mpr ⟨hL, hR.insert _, rfl⟩⟩
  case modL L R A ξ hX_def hY =>
    subst hX_def
    rw [Sequent.multisetEqTo_iff] at hX
    obtain ⟨hL, hR, hO⟩ := hX
    subst hY
    subst hO
    cases ξ
    case normal φ =>
      exact ⟨((~φ) :: projection A L', projection A R', none), ⟨PdlRule.modL rfl rfl⟩,
        Sequent.multisetEqTo_iff.mpr ⟨(projection_perm hL).cons _, projection_perm hR, rfl⟩⟩
    case loaded χ =>
      exact ⟨(projection A L', projection A R', some (Sum.inl (~'χ))), ⟨PdlRule.modL rfl rfl⟩,
        Sequent.multisetEqTo_iff.mpr ⟨projection_perm hL, projection_perm hR, rfl⟩⟩
  case modR L R A ξ hX_def hY =>
    subst hX_def
    rw [Sequent.multisetEqTo_iff] at hX
    obtain ⟨hL, hR, hO⟩ := hX
    subst hY
    subst hO
    cases ξ
    case normal φ =>
      exact ⟨(projection A L', (~φ) :: projection A R', none), ⟨PdlRule.modR rfl rfl⟩,
        Sequent.multisetEqTo_iff.mpr ⟨projection_perm hL, (projection_perm hR).cons _, rfl⟩⟩
    case loaded χ =>
      exact ⟨(projection A L', projection A R', some (Sum.inr (~'χ))), ⟨PdlRule.modR rfl rfl⟩,
        Sequent.multisetEqTo_iff.mpr ⟨projection_perm hL, projection_perm hR, rfl⟩⟩


/-! ## Refutable sequents

To show that the local development of a sequent does not depend on the order in which the
rules are applied we have to deal with *clashes*: one local tableau may close a branch with
a closure rule while another one first decomposes the two clashing formulas. So we need to
know that a clash cannot get lost, i.e. that after applying any local rule to a closed
sequent the resulting sequents can still be closed.

We call a sequent `Refutable` if it has a local tableau without any end nodes. Note that we
only ask for the *existence* of such a local tableau; this is all that is needed below, and
it can be shown by purely syntactic means: the interesting case is when the rule applied is
the box or the diamond unfolding for the two clashing formulas `⌈α⌉ψ` and `~⌈α⌉ψ`. There
the branches of `unfoldBox` and of `unfoldDiamond` clash pairwise, either on a test or on a
formula `⌈⌈δ⌉⌉ψ`, which is `Dset_mem_P_of_tests` below. -/


theorem Dset_mem_P_of_tests (α : Program) (ℓ : TP α) (Fs : List Formula) (δ : List Program)
    (h : (Fs, δ) ∈ Dset α) (hF : ∀ τ ∈ Fs, (~τ) ∉ F α ℓ) : δ ∈ P α ℓ := by
  cases α
  case atom_prog a => simp [Dset] at h; simp [P, h.2]
  case test τ =>
    simp [Dset] at h
    obtain ⟨hFs, hδ⟩ := h
    subst hFs; subst hδ
    have hℓ : ℓ ⟨τ, by simp [testsOfProgram]⟩ = true := by
      by_contra hc
      simp at hc
      exact hF τ (by simp) (by simp [F, hc])
    simp [P, hℓ]
  case union α β =>
    simp only [Dset, List.mem_union_iff] at h
    simp only [F, List.mem_union_iff] at hF
    rcases h with h | h
    · have := Dset_mem_P_of_tests α _ _ _ h (fun τ hτ hc => hF τ hτ (Or.inl hc))
      simp only [P, List.mem_union_iff]; tauto
    · have := Dset_mem_P_of_tests β _ _ _ h (fun τ hτ hc => hF τ hτ (Or.inr hc))
      simp only [P, List.mem_union_iff]; tauto
  case sequence α β =>
    simp only [Dset, List.mem_flatMap] at h
    simp only [F, List.mem_union_iff] at hF
    obtain ⟨⟨G, γ⟩, hGγ, hmem⟩ := h
    by_cases hγ : γ = []
    · subst hγ
      simp at hmem
      obtain ⟨H, hHδ, rfl⟩ := hmem
      have hG : [] ∈ P α (ℓ : TP α) := by
        refine Dset_mem_P_of_tests α _ _ _ hGγ (fun τ hτ hc => hF τ ?_ (Or.inl hc))
        simp only [List.mem_union_iff]; tauto
      have hH : δ ∈ P β (ℓ : TP β) := by
        refine Dset_mem_P_of_tests β _ _ _ hHδ (fun τ hτ hc => hF τ ?_ (Or.inr hc))
        simp only [List.mem_union_iff]; tauto
      simp only [P, List.mem_union_iff]
      right
      simp [hG, hH]
    · simp only [if_neg hγ, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      have hG : γ ∈ P α (ℓ : TP α) :=
        Dset_mem_P_of_tests α _ _ _ hGγ (fun τ hτ hc => hF τ hτ (Or.inl hc))
      simp only [P, List.mem_union_iff]
      left
      simp only [List.mem_map, List.mem_filter]
      exact ⟨γ, ⟨hG, by simp [hγ]⟩, rfl⟩
  case star α =>
    simp only [Dset, List.mem_union_iff, List.mem_flatten, List.mem_map] at h
    simp only [F] at hF
    rcases h with h | ⟨l, ⟨⟨G, γ⟩, hGγ, rfl⟩, hin⟩
    · simp at h
      simp [P, h.2]
    · by_cases hγ : γ = []
      · simp [hγ] at hin
      · simp only [if_neg hγ, List.mem_singleton, Prod.mk.injEq] at hin
        obtain ⟨rfl, rfl⟩ := hin
        have hG : γ ∈ P α (ℓ : TP α) := Dset_mem_P_of_tests α _ _ _ hGγ hF
        simp only [P, List.mem_union_iff]
        right
        simp only [List.mem_map, List.mem_filter]
        exact ⟨γ, ⟨hG, by simp [hγ]⟩, rfl⟩

/-! ### Refutable and dominated sequents -/

/-- The sequent `W` is *dominated by* the list `Ys` if it has a local tableau all of whose
end nodes occur in `Ys`, up to permutation of the two components. -/
def Sequent.DominatedBy (W : Sequent) (Ys : List Sequent) : Prop :=
  ∃ lt : LocalTableau W, ∀ Y ∈ endNodesOf lt, ∃ Y' ∈ Ys, Y.multisetEqTo Y'

/-- A sequent is *refutable* if it has a local tableau without any end nodes. -/
def Sequent.Refutable (X : Sequent) : Prop := X.DominatedBy []

lemma Sequent.refutable_iff {X : Sequent} :
    X.Refutable ↔ ∃ lt : LocalTableau X, endNodesOf lt = [] := by
  constructor
  · rintro ⟨lt, h⟩
    refine ⟨lt, List.eq_nil_iff_forall_not_mem.mpr (fun Y hY => ?_)⟩
    obtain ⟨Y', hY', _⟩ := h Y hY
    simp at hY'
  · rintro ⟨lt, h⟩
    exact ⟨lt, fun Y hY => absurd (h ▸ hY) (by simp)⟩

lemma Sequent.DominatedBy.mono {W : Sequent} {Ys Zs : List Sequent} (h : W.DominatedBy Ys)
    (hsub : ∀ Y ∈ Ys, ∃ Z ∈ Zs, Y.multisetEqTo Z) : W.DominatedBy Zs := by
  obtain ⟨lt, hlt⟩ := h
  refine ⟨lt, fun Y hY => ?_⟩
  obtain ⟨Y', hY', he⟩ := hlt Y hY
  obtain ⟨Z, hZ, he2⟩ := hsub Y' hY'
  exact ⟨Z, hZ, Sequent.multisetEqTo_trans he he2⟩

lemma Sequent.Refutable.dominatedBy {W : Sequent} (h : W.Refutable) (Ys : List Sequent) :
    W.DominatedBy Ys :=
  h.mono (by simp)

/-- If all children of a rule application are dominated by `Ys` then so is the sequent. -/
lemma Sequent.DominatedBy.byRule {W : Sequent} {Ys : List Sequent} {lra : LocalRuleApp}
    (hX : lra.X = W) (h : ∀ V ∈ lra.C, V.DominatedBy Ys) : W.DominatedBy Ys := by
  choose f hf using h
  refine ⟨LocalTableau.byLocalRule lra hX.symm f, ?_⟩
  intro Y hY
  simp only [endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
    Subtype.exists] at hY
  obtain ⟨_, ⟨V, hV, rfl⟩, hY⟩ := hY
  exact hf V hV Y hY

/-- A closed sequent is refutable: a closure rule can be applied to it. -/
lemma Sequent.Refutable.of_closed {X : Sequent} (h : X.closed) : X.Refutable := by
  have key : ∃ lra : LocalRuleApp, lra.X = X ∧ lra.C = [] := by
    rcases X with ⟨L, R, O⟩
    rcases h with bot_in | ⟨φ, φ_in, not_φ_in⟩
    · simp only [instMembershipFormulaSequent] at bot_in
      cases bot_in
      · exact ⟨⟨L, R, O, [⊥], [], none, [], .oneSidedL .bot rfl, [], rfl, by simp_all⟩,
          by simp, rfl⟩
      · exact ⟨⟨L, R, O, [], [⊥], none, [], .oneSidedR .bot rfl, [], rfl, by simp_all⟩,
          by simp, rfl⟩
    · simp only [instMembershipFormulaSequent] at φ_in not_φ_in
      cases φ_in <;> cases not_φ_in
      · refine ⟨⟨L, R, O, [φ, ~φ], [], none, [], .oneSidedL (.not _) rfl, [], rfl, ?_⟩,
          by simp, rfl⟩
        exact ⟨ List.cons_subperm_of_not_mem_of_mem
                (by simp [φ.neq_neg_self]) ‹_›
                (by rw [List.singleton_subperm_iff]; exact ‹_›),
                List.nil_subperm, by simp ⟩
      · exact ⟨⟨L, R, O, [φ], [~φ], none, [], LocalRule.LRnegL φ, [], rfl, by simp_all⟩,
          by simp, rfl⟩
      · exact ⟨⟨L, R, O, [~φ], [φ], none, [], LocalRule.LRnegR φ, [], rfl, by simp_all⟩,
          by simp, rfl⟩
      · refine ⟨⟨L, R, O, [], [φ, ~φ], none, [], .oneSidedR (.not _) rfl, [], rfl, ?_⟩,
          by simp, rfl⟩
        exact ⟨ List.nil_subperm,
                List.cons_subperm_of_not_mem_of_mem
                (by simp; exact φ.neq_neg_self) ‹_›
                (by rw [List.singleton_subperm_iff]; exact ‹_›),
                by simp ⟩
  obtain ⟨lra, hX, hC⟩ := key
  exact Sequent.DominatedBy.byRule hX (by simp [hC])

/-! ### Clashes survive the application of a rule

The next lemmas say that a clash in a sequent cannot be lost by applying a local rule:
the results are again refutable. The interesting cases are those where the rule is applied
to one of the two clashing formulas. -/

/-- To show that `X` is refutable it suffices to apply a one-sided rule to a formula `p` of
`X` and to refute all the results. The resulting sequents are only described by two
properties, so that we do not have to care about which of the two components `p` is in:
all formulas of `X` other than `p` are still present, and the result of the rule was added. -/
lemma Sequent.Refutable.byOneSided {X : Sequent} {p : Formula} {ress : List (List Formula)}
    (orule : OneSidedLocalRule [p] ress) (hp : p ∈ X)
    (h : ∀ res ∈ ress, ∀ W : Sequent,
        (∀ f ∈ X, f ≠ p → f ∈ W) → (∀ φ ∈ res, φ ∈ W) → W.Refutable) :
    X.Refutable := by
  rcases X with ⟨L, R, O⟩
  simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R] at hp
  rcases hp with hp | hp
  · refine Sequent.DominatedBy.byRule (lra := ⟨L, R, O, [p], [], none,
      ress.map (fun res => (res, ∅, none)), .oneSidedL orule rfl, _, rfl,
      ⟨by rw [List.singleton_subperm_iff]; exact hp, List.nil_subperm, by simp⟩⟩) rfl ?_
    intro V hV
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hV
    obtain ⟨res, hres, rfl⟩ := hV
    refine h res hres _ ?_ ?_
    · rintro f hf hne
      simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R] at hf ⊢
      rcases hf with hf | hf
      · exact Or.inl (List.mem_append_left _ (by
          simpa [List.diff_cons] using (List.mem_erase_of_ne hne).mpr hf))
      · exact Or.inr (by simpa using hf)
    · intro φ hφ
      exact Or.inl (List.mem_append_right _ hφ)
  · refine Sequent.DominatedBy.byRule (lra := ⟨L, R, O, [], [p], none,
      ress.map (fun res => (∅, res, none)), .oneSidedR orule rfl, _, rfl,
      ⟨List.nil_subperm, by rw [List.singleton_subperm_iff]; exact hp, by simp⟩⟩) rfl ?_
    intro V hV
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hV
    obtain ⟨res, hres, rfl⟩ := hV
    refine h res hres _ ?_ ?_
    · rintro f hf hne
      simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R] at hf ⊢
      rcases hf with hf | hf
      · exact Or.inl (by simpa using hf)
      · exact Or.inr (List.mem_append_left _ (by
          simpa [List.diff_cons] using (List.mem_erase_of_ne hne).mpr hf))
    · intro φ hφ
      exact Or.inr (List.mem_append_right _ hφ)

/-- Two formulas of different length are different. -/
lemma Formula.ne_of_length_lt {φ ψ : Formula}
    (h : lengthOfFormula φ < lengthOfFormula ψ) : φ ≠ ψ := by
  rintro rfl
  omega

/-- Two formulas of different length are different. -/
lemma Formula.ne_of_length_ne {φ ψ : Formula}
    (h : lengthOfFormula φ ≠ lengthOfFormula ψ) : φ ≠ ψ := by
  rintro rfl
  exact h rfl

/-- Adding formulas to a closed sequent keeps it closed. -/
lemma Sequent.closed.append {L R Ln Rn : List Formula} {O O' : Olf}
    (hX : Sequent.closed (L, R, O)) : Sequent.closed (L ++ Ln, R ++ Rn, O') := by
  rcases hX with hbot | ⟨f, hf, hnf⟩
  · left
    simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R, List.mem_append] at hbot ⊢
    tauto
  · right
    refine ⟨f, ?_, ?_⟩ <;>
      simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R, List.mem_append]
        at hf hnf ⊢ <;>
      tauto

/-- A one-sided rule that is not a closure rule has exactly one principal formula. -/
lemma OneSidedLocalRule.singleton_precond {pre : List Formula} {ress : List (List Formula)}
    (orule : OneSidedLocalRule pre ress) (h : ress ≠ []) : ∃ p, pre = [p] := by
  cases orule <;> simp_all

/-- Tests are shorter than the program they occur in. -/
lemma lengthOfFormula_lt_of_mem_testsOfProgram {α : Program} : ∀ {τ : Formula},
    τ ∈ testsOfProgram α → lengthOfFormula τ < lengthOfProgram α := by
  intro τ hτ
  cases α
  all_goals simp only [testsOfProgram, lengthOfProgram, List.mem_append, List.not_mem_nil,
    List.mem_singleton] at hτ ⊢
  case test φ => subst hτ; omega
  case sequence α β =>
    rcases hτ with h | h
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := α) h; omega
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := β) h; omega
  case union α β =>
    rcases hτ with h | h
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := α) h; omega
    · have := lengthOfFormula_lt_of_mem_testsOfProgram (α := β) h; omega
  case star α => have := lengthOfFormula_lt_of_mem_testsOfProgram (α := α) hτ; omega

/-- A list of boxes in front of a short formula is not the negation of a longer one. -/
lemma boxes_ne_neg {δ : List Program} {ψ χ : Formula}
    (h : lengthOfFormula ψ ≤ lengthOfFormula χ) : Formula.boxes δ ψ ≠ (~χ) := by
  cases δ with
  | nil => simp only [Formula.boxes_nil]; exact Formula.ne_of_length_lt (by simp; omega)
  | cons γ δ => simp [Formula.boxes_cons]

/-- A formula in the unfolding of `⌈α⌉ψ` is not `~⌈α⌉ψ`. -/
lemma ne_neg_box_of_mem_Bset {α : Program} {ψ : Formula} {ℓ : TP α} {f : Formula}
    (hf : f ∈ Bset α ℓ ψ) : f ≠ (~⌈α⌉ψ) := by
  simp only [Bset, List.mem_append, List.mem_map] at hf
  rcases hf with hf | ⟨δ, _, rfl⟩
  · exact Formula.ne_of_length_lt (by have := F_goes_down hf; simp; omega)
  · exact boxes_ne_neg (by simp)

/-- A formula in the unfolding of `~⌈α⌉ψ` is neither `⌈α⌉ψ` nor `~~⌈α⌉ψ`. -/
lemma ne_box_of_mem_Yset {α : Program} {ψ : Formula} {Fs : List Formula} {δ : List Program}
    (hFδ : (Fs, δ) ∈ Dset α) {f : Formula} (hf : f ∈ Yset (Fs, δ) ψ) :
    f ≠ (⌈α⌉ψ) ∧ f ≠ (~~⌈α⌉ψ) := by
  simp only [Yset, List.mem_union_iff, List.mem_singleton] at hf
  rcases hf with hf | rfl
  · obtain ⟨τ, hτ, rfl⟩ := Dset_mem_test α f hFδ hf
    have := lengthOfFormula_lt_of_mem_testsOfProgram hτ
    exact ⟨Formula.ne_of_length_lt (by simp; omega), Formula.ne_of_length_lt (by simp; omega)⟩
  · refine ⟨by simp, ?_⟩
    simp only [ne_eq, Formula.neg.injEq]
    exact boxes_ne_neg (by simp)

/-- **The branches of the box unfolding and of the diamond unfolding clash.**
Given a test profile `ℓ` and a pair `(Fs, δ) ∈ Dset α`, the two lists `Bset α ℓ ψ` and
`Yset (Fs, δ) ψ` contain a formula and its negation: either the two disagree about a test,
or `δ ∈ P α ℓ` and then `⌈⌈δ⌉⌉ψ` is in the first and `~⌈⌈δ⌉⌉ψ` is in the second list. -/
lemma Bset_Yset_clash {α : Program} {ψ : Formula} (ℓ : TP α) {Fs : List Formula}
    {δ : List Program} (hFδ : (Fs, δ) ∈ Dset α) :
    ∃ f, (f ∈ Bset α ℓ ψ ∧ (~f) ∈ Yset (Fs, δ) ψ)
       ∨ ((~f) ∈ Bset α ℓ ψ ∧ f ∈ Yset (Fs, δ) ψ) := by
  by_cases hcase : ∀ τ ∈ Fs, (~τ) ∉ F α ℓ
  · have hδ : δ ∈ P α ℓ := Dset_mem_P_of_tests α ℓ _ _ hFδ hcase
    refine ⟨⌈⌈δ⌉⌉ψ, Or.inl ⟨?_, ?_⟩⟩
    · simp only [Bset, List.mem_append, List.mem_map]
      exact Or.inr ⟨δ, hδ, rfl⟩
    · simp [Yset]
  · push_neg at hcase
    obtain ⟨τ, hτ, hτF⟩ := hcase
    exact ⟨τ, Or.inr ⟨by simp [Bset, hτF], by simp [Yset]; tauto⟩⟩

lemma refutable_of_negneg {X : Sequent} {χ : Formula} (h1 : χ ∈ X) (h2 : (~(~(~χ))) ∈ X) :
    X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.neg (~χ)) h2 ?_
  rintro res hres W hsurv hmem
  simp only [List.mem_singleton] at hres
  subst hres
  refine Sequent.Refutable.of_closed (Or.inr ⟨χ, ?_, hmem _ (by simp)⟩)
  exact hsurv χ h1 (Formula.ne_of_length_ne (by simp; omega))

lemma refutable_of_con_nCo {X : Sequent} {χ ρ : Formula} (h1 : χ ∈ X) (h2 : ρ ∈ X)
    (h3 : (~(χ ⋀ ρ)) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.nCo χ ρ) h3 ?_
  rintro res hres W hsurv hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hres
  rcases hres with rfl | rfl
  · exact Sequent.Refutable.of_closed (Or.inr ⟨χ,
      hsurv χ h1 (Formula.ne_of_length_ne (by simp; omega)), hmem _ (by simp)⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨ρ,
      hsurv ρ h2 (Formula.ne_of_length_ne (by simp; omega)), hmem _ (by simp)⟩)

lemma refutable_of_nCo_con {X : Sequent} {χ ρ : Formula} (h1 : (~χ) ∈ X ∨ (~ρ) ∈ X)
    (h2 : (χ ⋀ ρ) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.con χ ρ) h2 ?_
  rintro res hres W hsurv hmem
  simp only [List.mem_singleton] at hres
  subst hres
  rcases h1 with h1 | h1
  · exact Sequent.Refutable.of_closed (Or.inr ⟨χ, hmem _ (by simp), hsurv _ h1 (by simp)⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨ρ, hmem _ (by simp), hsurv _ h1 (by simp)⟩)

lemma refutable_of_nCo_negneg {X : Sequent} {χ ρ : Formula} (h1 : (~χ) ∈ X ∨ (~ρ) ∈ X)
    (h2 : (~~(χ ⋀ ρ)) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.neg (χ ⋀ ρ)) h2 ?_
  rintro res hres W hsurv hmem
  simp only [List.mem_singleton] at hres
  subst hres
  have k1 : (~χ) ≠ (~~(χ ⋀ ρ)) := Formula.ne_of_length_ne (by simp; omega)
  have k2 : (~ρ) ≠ (~~(χ ⋀ ρ)) := Formula.ne_of_length_ne (by simp; omega)
  refine refutable_of_nCo_con (χ := χ) (ρ := ρ) ?_ (hmem _ (by simp))
  rcases h1 with h1 | h1
  · exact Or.inl (hsurv _ h1 k1)
  · exact Or.inr (hsurv _ h1 k2)

lemma refutable_of_box_dia {X : Sequent} {α : Program} {ψ : Formula} {ℓ : TP α}
    (hna : ¬ α.isAtomic) (hB : ∀ φ ∈ Bset α ℓ ψ, φ ∈ X) (hd : (~⌈α⌉ψ) ∈ X) :
    X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.dia α ψ hna) hd ?_
  rintro res hres W hsurv hmem
  simp only [unfoldDiamond, List.mem_map] at hres
  obtain ⟨⟨Fs, δ⟩, hFδ, rfl⟩ := hres
  have hBW : ∀ φ ∈ Bset α ℓ ψ, φ ∈ W :=
    fun φ hφ => hsurv φ (hB φ hφ) (ne_neg_box_of_mem_Bset hφ)
  obtain ⟨f, hf | hf⟩ := Bset_Yset_clash (ψ := ψ) ℓ hFδ
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hBW _ hf.1, hmem _ hf.2⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hmem _ hf.2, hBW _ hf.1⟩)

lemma refutable_of_dia_box {X : Sequent} {α : Program} {ψ : Formula} {Fs : List Formula}
    {δ : List Program} (hna : ¬ α.isAtomic) (hFδ : (Fs, δ) ∈ Dset α)
    (hY : ∀ φ ∈ Yset (Fs, δ) ψ, φ ∈ X) (hb : (⌈α⌉ψ) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.box α ψ hna) hb ?_
  rintro res hres W hsurv hmem
  simp only [unfoldBox, List.mem_map] at hres
  obtain ⟨ℓ, _, rfl⟩ := hres
  have hYW : ∀ φ ∈ Yset (Fs, δ) ψ, φ ∈ W :=
    fun φ hφ => hsurv φ (hY φ hφ) (ne_box_of_mem_Yset hFδ hφ).1
  obtain ⟨f, hf | hf⟩ := Bset_Yset_clash (ψ := ψ) ℓ hFδ
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hmem _ hf.1, hYW _ hf.2⟩)
  · exact Sequent.Refutable.of_closed (Or.inr ⟨f, hYW _ hf.2, hmem _ hf.1⟩)

lemma refutable_of_dia_negneg {X : Sequent} {α : Program} {ψ : Formula} {Fs : List Formula}
    {δ : List Program} (hna : ¬ α.isAtomic) (hFδ : (Fs, δ) ∈ Dset α)
    (hY : ∀ φ ∈ Yset (Fs, δ) ψ, φ ∈ X) (hb : (~~⌈α⌉ψ) ∈ X) : X.Refutable := by
  refine Sequent.Refutable.byOneSided (OneSidedLocalRule.neg (⌈α⌉ψ)) hb ?_
  rintro res hres W hsurv hmem
  simp only [List.mem_singleton] at hres
  subst hres
  exact refutable_of_dia_box hna hFδ
    (fun φ hφ => hsurv φ (hY φ hφ) (ne_box_of_mem_Yset hFδ hφ).2) (hmem _ (by simp))

/-- **A clash survives a one-sided rule.** If `X` is closed and `W` is obtained from `X` by
removing the principal formula `p` of a one-sided rule and adding one of its results, then
`W` is refutable. -/
lemma Sequent.Refutable.of_oneSided_step {X W : Sequent} (hX : X.closed) {p : Formula}
    {ress : List (List Formula)} (orule : OneSidedLocalRule [p] ress) {res : List Formula}
    (hres : res ∈ ress) (hsurv : ∀ f ∈ X, f ≠ p → f ∈ W) (hmem : ∀ φ ∈ res, φ ∈ W) :
    W.Refutable := by
  have easy : ∀ f, f ∈ X → (~f) ∈ X → f ≠ p → (~f) ≠ p → W.Refutable := fun f h1 h2 h3 h4 =>
    Sequent.Refutable.of_closed (Or.inr ⟨f, hsurv f h1 h3, hsurv _ h2 h4⟩)
  cases orule
  case bot => simp at hres
  case neg φ =>
    simp only [List.mem_singleton] at hres
    subst hres
    have hφW : φ ∈ W := hmem _ (by simp)
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (~~φ)
      · subst h1
        have hne : (~(~~φ)) ≠ (~~φ) := Formula.ne_of_length_ne (by simp)
        exact refutable_of_negneg (χ := φ) hφW (hsurv _ hnf hne)
      · by_cases h2 : (~f) = (~~φ)
        · simp only [Formula.neg.injEq] at h2
          subst h2
          have hne : (~φ) ≠ (~~φ) := Formula.ne_of_length_ne (by simp)
          exact Sequent.Refutable.of_closed (Or.inr ⟨φ, hφW, hsurv _ hf hne⟩)
        · exact easy f hf hnf h1 h2
  case con φ ψ =>
    simp only [List.mem_singleton] at hres
    subst hres
    have hφW : φ ∈ W := hmem _ (by simp)
    have hψW : ψ ∈ W := hmem _ (by simp)
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (φ ⋀ ψ)
      · subst h1
        exact refutable_of_con_nCo hφW hψW (hsurv _ hnf (by simp))
      · exact easy f hf hnf h1 (by simp)
  case nCo φ ψ =>
    have hres' : res = [~φ] ∨ res = [~ψ] := by simpa using hres
    have hin : (~φ) ∈ W ∨ (~ψ) ∈ W := by
      rcases hres' with rfl | rfl
      · exact Or.inl (hmem _ (by simp))
      · exact Or.inr (hmem _ (by simp))
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (~(φ ⋀ ψ))
      · subst h1
        have hne : (~~(φ ⋀ ψ)) ≠ (~(φ ⋀ ψ)) := Formula.ne_of_length_ne (by simp)
        exact refutable_of_nCo_negneg hin (hsurv _ hnf hne)
      · by_cases h2 : (~f) = (~(φ ⋀ ψ))
        · simp only [Formula.neg.injEq] at h2
          subst h2
          exact refutable_of_nCo_con hin (hsurv _ hf (by simp))
        · exact easy f hf hnf h1 h2
  case box α φ hna =>
    simp only [unfoldBox, List.mem_map] at hres
    obtain ⟨ℓ, _, rfl⟩ := hres
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (⌈α⌉φ)
      · subst h1
        exact refutable_of_box_dia (ℓ := ℓ) hna (fun x hx => hmem x hx) (hsurv _ hnf (by simp))
      · exact easy f hf hnf h1 (by simp)
  case dia α φ hna =>
    simp only [unfoldDiamond, List.mem_map] at hres
    obtain ⟨⟨Fs, δ⟩, hFδ, rfl⟩ := hres
    rcases hX with hbot | ⟨f, hf, hnf⟩
    · exact Sequent.Refutable.of_closed (Or.inl (hsurv _ hbot (by simp)))
    · by_cases h1 : f = (~⌈α⌉φ)
      · subst h1
        have hne : (~~⌈α⌉φ) ≠ (~⌈α⌉φ) := Formula.ne_of_length_ne (by simp)
        exact refutable_of_dia_negneg hna hFδ (fun x hx => hmem x hx) (hsurv _ hnf hne)
      · by_cases h2 : (~f) = (~⌈α⌉φ)
        · simp only [Formula.neg.injEq] at h2
          subst h2
          exact refutable_of_dia_box hna hFδ (fun x hx => hmem x hx) (hsurv _ hf (by simp))
        · exact easy f hf hnf h1 h2

/-- **A clash survives any local rule:** every child of a rule application to a closed
sequent is refutable. -/
lemma Sequent.Refutable.child_of_closed {X W : Sequent} (hX : X.closed) {lra : LocalRuleApp}
    (hXl : lra.X = X) (hW : W ∈ lra.C) : W.Refutable := by
  rcases lra with ⟨L, R, O, Lc, Rc, Oc, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X] at hXl
  subst hXl
  subst hC
  cases lr
  case oneSidedL ress' orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hW
    obtain ⟨res, hres, rfl⟩ := hW
    obtain ⟨p, rfl⟩ := orule.singleton_precond (by rintro rfl; simp at hres)
    refine Sequent.Refutable.of_oneSided_step hX orule hres ?_ ?_
    · rintro f hf hne
      simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R] at hf ⊢
      rcases hf with hf | hf
      · exact Or.inl (List.mem_append_left _ (by
          simpa [List.diff_cons] using (List.mem_erase_of_ne hne).mpr hf))
      · exact Or.inr (by simpa using hf)
    · intro φ hφ
      simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R]
      exact Or.inl (List.mem_append_right _ hφ)
  case oneSidedR ress' orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hW
    obtain ⟨res, hres, rfl⟩ := hW
    obtain ⟨p, rfl⟩ := orule.singleton_precond (by rintro rfl; simp at hres)
    refine Sequent.Refutable.of_oneSided_step hX orule hres ?_ ?_
    · rintro f hf hne
      simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R] at hf ⊢
      rcases hf with hf | hf
      · exact Or.inl (by simpa using hf)
      · exact Or.inr (List.mem_append_left _ (by
          simpa [List.diff_cons] using (List.mem_erase_of_ne hne).mpr hf))
    · intro φ hφ
      simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R]
      exact Or.inr (List.mem_append_right _ hφ)
  case LRnegL => simp at hW
  case LRnegR => simp at hW
  case loadedL ress' χ lrule YS_def =>
    subst YS_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hW
    obtain ⟨⟨Ln, on⟩, hres, rfl⟩ := hW
    exact Sequent.Refutable.of_closed hX.append
  case loadedR ress' χ lrule YS_def =>
    subst YS_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hW
    obtain ⟨⟨Ln, on⟩, hres, rfl⟩ := hW
    exact Sequent.Refutable.of_closed hX.append

/-! ### Transporting local tableaux along permutations -/

/-- Local rule applications can be transported along `Sequent.multisetEqTo`. -/
lemma LocalRuleApp.exists_of_msEq {X X' : Sequent} (h : X.multisetEqTo X')
    {lra : LocalRuleApp} (hX : lra.X = X) : ∃ lra' : LocalRuleApp, lra'.X = X' ∧
      (∀ W' ∈ lra'.C, ∃ W ∈ lra.C, W.multisetEqTo W')
      ∧ (∀ W ∈ lra.C, ∃ W' ∈ lra'.C, W.multisetEqTo W') := by
  rcases lra with ⟨L, R, O, Lc, Rc, Oc, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X] at hX
  subst hX
  subst hC
  obtain ⟨L', R', O'⟩ := X'
  rw [Sequent.multisetEqTo_iff] at h
  obtain ⟨hL, hR, rfl⟩ := h
  refine ⟨⟨L', R', O, Lc, Rc, Oc, ress, lr, _, rfl,
    ⟨pre.1.trans hL.subperm, pre.2.1.trans hR.subperm, pre.2.2⟩⟩, rfl, ?_, ?_⟩
  · intro W' hW'
    simp only [applyLocalRule, List.mem_map] at hW' ⊢
    obtain ⟨⟨Ln, Rn, On⟩, hmem, rfl⟩ := hW'
    refine ⟨_, ⟨(Ln, Rn, On), hmem, rfl⟩, ?_⟩
    exact Sequent.multisetEqTo_iff.mpr ⟨(hL.diff_right Lc).append_right _,
      (hR.diff_right Rc).append_right _, rfl⟩
  · intro W hW
    simp only [applyLocalRule, List.mem_map] at hW ⊢
    obtain ⟨⟨Ln, Rn, On⟩, hmem, rfl⟩ := hW
    refine ⟨_, ⟨(Ln, Rn, On), hmem, rfl⟩, ?_⟩
    exact Sequent.multisetEqTo_iff.mpr ⟨(hL.diff_right Lc).append_right _,
      (hR.diff_right Rc).append_right _, rfl⟩

/-- A local tableau for `X` can be transported to any sequent that is multiset-equal to `X`,
changing the end nodes only up to permutation. -/
lemma Sequent.dominatedBy_of_msEq : ∀ {X : Sequent} (lt : LocalTableau X) {X' : Sequent},
    X.multisetEqTo X' → X'.DominatedBy (endNodesOf lt) := by
  intro X lt
  induction lt with
  | @sim X bas =>
      intro X' h
      have bas' : X'.basic := (Sequent.basic_iff_of_setEqTo (setEqTo_of_msEq h)).mp bas
      exact ⟨LocalTableau.sim bas', by
        intro Y hY
        simp only [endNodesOf, List.mem_singleton] at hY ⊢
        subst hY
        exact ⟨X, rfl, (Sequent.multisetEqTo_symm _ _).mp h⟩⟩
  | @byLocalRule X lra X_def next IH =>
      subst X_def
      intro X' h
      obtain ⟨lra', hlra', hchild, -⟩ := LocalRuleApp.exists_of_msEq h (lra := lra) rfl
      have hdom : ∀ W' ∈ lra'.C,
          W'.DominatedBy (endNodesOf (LocalTableau.byLocalRule lra rfl next)) := by
        intro W' hW'
        obtain ⟨W, hW, hWW⟩ := hchild W' hW'
        refine (IH W hW hWW).mono (fun Y hY => ⟨Y, ?_, Sequent.multisetEqTo_refl Y⟩)
        exact endNodeOfChild_to_endNode lra next rfl hW hY
      refine ⟨LocalTableau.byLocalRule lra' hlra'.symm (fun W' hW' => (hdom W' hW').choose), ?_⟩
      intro Y hY
      obtain ⟨W', hW', hYl⟩ := endNodeIsEndNodeOfChild _ hY
      exact (hdom W' hW').choose_spec Y hYl

/-! ### Local rules commute

Two local rule applications to the same sequent either have the same principal formulas —
and then they are the same rule with the same children — or they can be applied in either
order, leading to the same children up to permutation. -/

/-- A one-sided rule is determined by its principal formulas. -/
lemma OneSidedLocalRule.ress_eq {pre : List Formula} {ress ress' : List (List Formula)}
    (r : OneSidedLocalRule pre ress) (r' : OneSidedLocalRule pre ress') : ress = ress' := by
  cases r <;> cases r' <;> simp_all

/-- A loaded rule is determined by its principal formula. -/
lemma LoadRule.ress_eq {chi : LoadFormula}
    {ress ress' : List (List Formula × Option NegLoadFormula)}
    (r : LoadRule (~'chi) ress) (r' : LoadRule (~'chi) ress') : ress = ress' := by
  cases r <;> cases r' <;> simp_all

/-- A local rule is determined by its principal formulas. -/
lemma LocalRule.ress_eq {Lc Rc : List Formula} {Oc : Olf} {ress ress' : List Sequent}
    (r : LocalRule (Lc, Rc, Oc) ress) (r' : LocalRule (Lc, Rc, Oc) ress') : ress = ress' := by
  cases r <;> cases r' <;> simp_all
  all_goals first
    | exact absurd rfl (OneSidedLocalRule.precond_ne_nil (by assumption))
    | (congr 1; exact OneSidedLocalRule.ress_eq (by assumption) (by assumption))
    | (congr 1; exact LoadRule.ress_eq (by assumption) (by assumption))

/-- Two rule applications to the same sequent with the same principal formulas have the
same children. -/
lemma LocalRuleApp.C_eq_of_cond_eq {lra lra' : LocalRuleApp} (hX : lra.X = lra'.X)
    (hL : lra.Lcond = lra'.Lcond) (hR : lra.Rcond = lra'.Rcond) (hO : lra.Ocond = lra'.Ocond) :
    lra.C = lra'.C := by
  rcases lra with ⟨L, R, O, Lc, Rc, Oc, ress, lr, C, hC, pre⟩
  rcases lra' with ⟨L', R', O', Lc', Rc', Oc', ress', lr', C', hC', pre'⟩
  simp only [LocalRuleApp.X] at hX
  simp only at hL hR hO
  obtain ⟨rfl, rfl, rfl⟩ := hX
  subst hL; subst hR; subst hO
  subst hC; subst hC'
  obtain rfl := LocalRule.ress_eq lr lr'
  simp only [applyLocalRule]

/-! ### Closure rules

A local rule has no results if and only if it is one of the closure rules. For the direction
we need here we must know that the box and diamond unfoldings are never empty. -/

/-- The box unfolding is never empty. -/
lemma unfoldBox_ne_nil (a : Program) (phi : Formula) : unfoldBox a phi ≠ [] := by
  intro h
  have hmem : Bset a (fun _ => true) phi ∈ unfoldBox a phi :=
    List.mem_map.mpr ⟨_, allTP_mem _, rfl⟩
  rw [h] at hmem
  simp at hmem

/-- The program unfolding used for diamonds is never empty. -/
theorem Dset_ne_nil : ∀ (a : Program), Dset a ≠ []
  | ·_ => by simp [Dset]
  | ?'_ => by simp [Dset]
  | a ⋓ b => by
      simp only [Dset]
      intro h
      refine Dset_ne_nil a (List.eq_nil_iff_forall_not_mem.mpr (fun x hx => ?_))
      rw [List.eq_nil_iff_forall_not_mem] at h
      exact h x (by simp [hx])
  | a ;' b => by
      simp only [Dset]
      intro h
      rw [List.flatMap_eq_nil_iff] at h
      obtain ⟨⟨F, delta⟩, hmem⟩ := List.exists_mem_of_ne_nil _ (Dset_ne_nil a)
      have hthis := h _ hmem
      by_cases hd : delta = []
      · subst hd
        simp only [if_true] at hthis
        obtain ⟨⟨G, delta'⟩, hmem2⟩ := List.exists_mem_of_ne_nil _ (Dset_ne_nil b)
        have hh : (F ∪ G, delta') ∈ ((Dset b).map
            (fun x : List Formula × List Program => [(F ∪ x.1, x.2)])).flatten :=
          List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨(G, delta'), hmem2, rfl⟩, by simp⟩
        rw [hthis] at hh
        simp at hh
      · simp [hd] at hthis
  | ∗_ => by simp [Dset]

/-- A rule without results is a closure rule, so the sequent it is applied to is closed. -/
lemma LocalRuleApp.closed_of_ress_nil {lra : LocalRuleApp} (h : lra.ress = []) :
    lra.X.closed := by
  rcases lra with ⟨L, R, O, Lc, Rc, Oc, ress, lr, C, hC, pre⟩
  simp only at h
  simp only [LocalRuleApp.X, Sequent.closed, instMembershipFormulaSequent, Sequent.L, Sequent.R]
  obtain ⟨preL, preR, preO⟩ := pre
  cases lr
  case oneSidedL ress' orule YS_def =>
    subst YS_def
    rw [List.map_eq_nil_iff] at h
    cases orule
    case bot => left; left; exact preL.subset (by simp)
    case not f => right; exact ⟨f, Or.inl (preL.subset (by simp)), Or.inl (preL.subset (by simp))⟩
    case box a f _ => exact absurd h (unfoldBox_ne_nil a f)
    case dia a f _ => exact absurd h (by simpa [unfoldDiamond] using Dset_ne_nil a)
    all_goals simp at h
  case oneSidedR ress' orule YS_def =>
    subst YS_def
    rw [List.map_eq_nil_iff] at h
    cases orule
    case bot => left; right; exact preR.subset (by simp)
    case not f => right; exact ⟨f, Or.inr (preR.subset (by simp)), Or.inr (preR.subset (by simp))⟩
    case box a f _ => exact absurd h (unfoldBox_ne_nil a f)
    case dia a f _ => exact absurd h (by simpa [unfoldDiamond] using Dset_ne_nil a)
    all_goals simp at h
  case LRnegL f =>
    exact Or.inr ⟨f, Or.inl (preL.subset (by simp)), Or.inr (preR.subset (by simp))⟩
  case LRnegR f =>
    exact Or.inr ⟨f, Or.inr (preR.subset (by simp)), Or.inl (preL.subset (by simp))⟩
  case loadedL ress' chi lrule YS_def =>
    subst YS_def
    rw [List.map_eq_nil_iff] at h
    cases lrule
    case dia a _ _ => exact absurd h (by simpa [unfoldDiamondLoaded] using Dset_ne_nil a)
    case dia' a _ _ => exact absurd h (by simpa [unfoldDiamondLoaded'] using Dset_ne_nil a)
  case loadedR ress' chi lrule YS_def =>
    subst YS_def
    rw [List.map_eq_nil_iff] at h
    cases lrule
    case dia a _ _ => exact absurd h (by simpa [unfoldDiamondLoaded] using Dset_ne_nil a)
    case dia' a _ _ => exact absurd h (by simpa [unfoldDiamondLoaded'] using Dset_ne_nil a)

/-- The shape of a rule application that is not a closure rule: it has exactly one principal
formula, in the left component, in the right component, or the loaded formula. -/
lemma LocalRuleApp.shape_of_ress_ne_nil {lra : LocalRuleApp} (h : lra.ress ≠ []) :
    (∃ p, lra.Lcond = [p] ∧ lra.Rcond = [] ∧ lra.Ocond = none
        ∧ ∀ Y ∈ lra.ress, Y.2.2 = none)
  ∨ (∃ p, lra.Lcond = [] ∧ lra.Rcond = [p] ∧ lra.Ocond = none
        ∧ ∀ Y ∈ lra.ress, Y.2.2 = none)
  ∨ (lra.Lcond = [] ∧ lra.Rcond = [] ∧ lra.Ocond ≠ none) := by
  rcases lra with ⟨L, R, O, Lc, Rc, Oc, ress, lr, C, hC, pre⟩
  simp only at h ⊢
  cases lr
  case oneSidedL ress' orule YS_def =>
    subst YS_def
    obtain ⟨p, rfl⟩ := orule.singleton_precond (by rintro rfl; simp at h)
    exact Or.inl ⟨p, rfl, rfl, rfl, by intro Y hY; simp at hY; obtain ⟨r, _, rfl⟩ := hY; rfl⟩
  case oneSidedR ress' orule YS_def =>
    subst YS_def
    obtain ⟨p, rfl⟩ := orule.singleton_precond (by rintro rfl; simp at h)
    exact Or.inr (Or.inl ⟨p, rfl, rfl, rfl,
      by intro Y hY; simp at hY; obtain ⟨r, _, rfl⟩ := hY; rfl⟩)
  case LRnegL => simp at h
  case LRnegR => simp at h
  case loadedL => exact Or.inr (Or.inr ⟨rfl, rfl, by simp⟩)
  case loadedR => exact Or.inr (Or.inr ⟨rfl, rfl, by simp⟩)

/-- If the principal formula of a rule is in `L` and different from `p` then it is still
in `L.diff [p]`. -/
lemma List.singleton_subperm_diff {L : List Formula} {p q : Formula} (hq : [q].Subperm L)
    (hne : q ≠ p) : [q].Subperm (L.diff [p]) := by
  rw [List.singleton_subperm_iff] at hq ⊢
  simpa [List.diff_cons] using (List.mem_erase_of_ne hne).mpr hq

/-- A loaded rule can only be applied when its condition is the loaded formula present. -/
lemma LocalRuleApp.Ocond_eq_O {lra : LocalRuleApp} (h : lra.Ocond ≠ none) : lra.Ocond = lra.O := by
  rcases hc : lra.Ocond with _ | x
  · exact absurd hc h
  · have hsub := lra.preconditionProof.2.2
    rw [hc] at hsub
    exact hc ▸ Option.some_subseteq.mp hsub

/-- **Two different rules at the same sequent are independent:** the principal formulas of
each of them survive the application of the other one, and at most one of them touches the
loaded formula. -/
lemma LocalRuleApp.independent {lra1 lra2 : LocalRuleApp} (hX : lra1.X = lra2.X)
    (h1 : lra1.ress ≠ []) (h2 : lra2.ress ≠ [])
    (hne : ¬ (lra1.Lcond = lra2.Lcond ∧ lra1.Rcond = lra2.Rcond ∧ lra1.Ocond = lra2.Ocond)) :
    lra2.Lcond.Subperm (lra1.L.diff lra1.Lcond)
  ∧ lra1.Lcond.Subperm (lra2.L.diff lra2.Lcond)
  ∧ lra2.Rcond.Subperm (lra1.R.diff lra1.Rcond)
  ∧ lra1.Rcond.Subperm (lra2.R.diff lra2.Rcond)
  ∧ ((lra1.Ocond = none ∧ ∀ Y ∈ lra1.ress, Y.2.2 = none)
     ∨ (lra2.Ocond = none ∧ ∀ Y ∈ lra2.ress, Y.2.2 = none)) := by
  have hL : lra1.L = lra2.L := congrArg (fun s => s.1) hX
  have hR : lra1.R = lra2.R := congrArg (fun s => s.2.1) hX
  have hO : lra1.O = lra2.O := congrArg (fun s => s.2.2) hX
  obtain ⟨pre1L, pre1R, pre1O⟩ := lra1.preconditionProof
  obtain ⟨pre2L, pre2R, pre2O⟩ := lra2.preconditionProof
  rcases LocalRuleApp.shape_of_ress_ne_nil h1 with ⟨p1, e1L, e1R, e1O, e1res⟩ |
    ⟨p1, e1L, e1R, e1O, e1res⟩ | ⟨e1L, e1R, e1O⟩
  · have m1a : [p1].Subperm lra1.L := by rw [← e1L]; exact pre1L
    have m1b : [p1].Subperm lra2.L := by rw [← hL]; exact m1a
    rcases LocalRuleApp.shape_of_ress_ne_nil h2 with ⟨p2, e2L, e2R, e2O, e2res⟩ |
      ⟨p2, e2L, e2R, e2O, e2res⟩ | ⟨e2L, e2R, e2O⟩
    · have m2a : [p2].Subperm lra1.L := by rw [hL, ← e2L]; exact pre2L
      have hpp : p2 ≠ p1 := by
        rintro rfl
        exact hne ⟨e1L.trans e2L.symm, e1R.trans e2R.symm, e1O.trans e2O.symm⟩
      rw [e1L, e1R, e2L, e2R]
      exact ⟨List.singleton_subperm_diff m2a hpp,
        List.singleton_subperm_diff m1b (Ne.symm hpp), by simp, by simp, Or.inl ⟨e1O, e1res⟩⟩
    · have m2b : [p2].Subperm lra1.R := by rw [hR, ← e2R]; exact pre2R
      rw [e1L, e1R, e2L, e2R]
      exact ⟨by simp, by simpa using m1b, by simpa using m2b, by simp, Or.inl ⟨e1O, e1res⟩⟩
    · rw [e1L, e1R, e2L, e2R]
      exact ⟨by simp, by simpa using m1b, by simp, by simp, Or.inl ⟨e1O, e1res⟩⟩
  · have m1a : [p1].Subperm lra1.R := by rw [← e1R]; exact pre1R
    have m1b : [p1].Subperm lra2.R := by rw [← hR]; exact m1a
    rcases LocalRuleApp.shape_of_ress_ne_nil h2 with ⟨p2, e2L, e2R, e2O, e2res⟩ |
      ⟨p2, e2L, e2R, e2O, e2res⟩ | ⟨e2L, e2R, e2O⟩
    · have m2a : [p2].Subperm lra1.L := by rw [hL, ← e2L]; exact pre2L
      rw [e1L, e1R, e2L, e2R]
      exact ⟨by simpa using m2a, by simp, by simp, by simpa using m1b, Or.inl ⟨e1O, e1res⟩⟩
    · have m2b : [p2].Subperm lra1.R := by rw [hR, ← e2R]; exact pre2R
      have hpp : p2 ≠ p1 := by
        rintro rfl
        exact hne ⟨e1L.trans e2L.symm, e1R.trans e2R.symm, e1O.trans e2O.symm⟩
      rw [e1L, e1R, e2L, e2R]
      exact ⟨by simp, by simp, List.singleton_subperm_diff m2b hpp,
        List.singleton_subperm_diff m1b (Ne.symm hpp), Or.inl ⟨e1O, e1res⟩⟩
    · rw [e1L, e1R, e2L, e2R]
      exact ⟨by simp, by simp, by simp, by simpa using m1b, Or.inl ⟨e1O, e1res⟩⟩
  · rcases LocalRuleApp.shape_of_ress_ne_nil h2 with ⟨p2, e2L, e2R, e2O, e2res⟩ |
      ⟨p2, e2L, e2R, e2O, e2res⟩ | ⟨e2L, e2R, e2O⟩
    · have m2a : [p2].Subperm lra1.L := by rw [hL, ← e2L]; exact pre2L
      rw [e1L, e1R, e2L, e2R]
      exact ⟨by simpa using m2a, by simp, by simp, by simp, Or.inr ⟨e2O, e2res⟩⟩
    · have m2b : [p2].Subperm lra1.R := by rw [hR, ← e2R]; exact pre2R
      rw [e1L, e1R, e2L, e2R]
      exact ⟨by simp, by simp, by simpa using m2b, by simp, Or.inr ⟨e2O, e2res⟩⟩
    · exact absurd ⟨e1L.trans e2L.symm, e1R.trans e2R.symm,
        ((LocalRuleApp.Ocond_eq_O e1O).trans hO).trans (LocalRuleApp.Ocond_eq_O e2O).symm⟩ hne

/-! ### Local rules commute -/

/-- Removing a sublist from the front of an append. -/
lemma List.append_diff_of_subperm {alpha : Type*} [DecidableEq alpha] :
    ∀ (C A B : List alpha), C.Subperm A → (A ++ B).diff C = A.diff C ++ B
  | [], A, B, _ => by simp
  | c :: C, A, B, h => by
      have hc : c ∈ A := h.subset (by simp)
      have hsub : C.Subperm (A.erase c) := by
        have hcount := List.subperm_ext_iff.mp h
        rw [List.subperm_ext_iff]
        intro x hx
        by_cases hxc : x = c
        · subst hxc
          have hle := hcount x (by simp)
          rw [List.count_erase_self]
          simp only [List.count_cons_self] at hle
          omega
        · rw [List.count_erase_of_ne hxc]
          have hle := hcount x (by simp [hx])
          rwa [List.count_cons_of_ne (fun hh => hxc hh.symm)] at hle
      rw [List.diff_cons, List.diff_cons, List.erase_append_left _ hc]
      exact List.append_diff_of_subperm C (A.erase c) B hsub

lemma List.diff_erase_comm {alpha : Type*} [DecidableEq alpha] :
    ∀ (C : List alpha) (L : List alpha) (a : alpha), (L.diff C).erase a = (L.erase a).diff C
  | [], L, a => by simp
  | c :: C, L, a => by
      rw [List.diff_cons, List.diff_cons, List.diff_erase_comm C, List.erase_comm]

lemma List.diff_comm {alpha : Type*} [DecidableEq alpha] :
    ∀ (D : List alpha) (L C : List alpha), (L.diff C).diff D = (L.diff D).diff C
  | [], L, C => by simp
  | d :: D, L, C => by
      rw [List.diff_cons, List.diff_cons, List.diff_erase_comm C L d, List.diff_comm D]

/-- Applying two independent rules in the two possible orders gives the same sequent, up to
permutation of the two components. -/
lemma applyLocalRule_comm {L R Ln₁ Rn₁ Ln₂ Rn₂ Lc₁ Rc₁ Lc₂ Rc₂ : List Formula}
    {O On₁ Oc₁ On₂ Oc₂ : Olf}
    (hL₁ : Lc₂.Subperm (L.diff Lc₁)) (hL₂ : Lc₁.Subperm (L.diff Lc₂))
    (hR₁ : Rc₂.Subperm (R.diff Rc₁)) (hR₂ : Rc₁.Subperm (R.diff Rc₂))
    (hO : (Oc₁ = none ∧ On₁ = none) ∨ (Oc₂ = none ∧ On₂ = none)) :
    Sequent.multisetEqTo
      ((L.diff Lc₁ ++ Ln₁).diff Lc₂ ++ Ln₂, (R.diff Rc₁ ++ Rn₁).diff Rc₂ ++ Rn₂,
        Olf.change (Olf.change O Oc₁ On₁) Oc₂ On₂)
      ((L.diff Lc₂ ++ Ln₂).diff Lc₁ ++ Ln₁, (R.diff Rc₂ ++ Rn₂).diff Rc₁ ++ Rn₁,
        Olf.change (Olf.change O Oc₂ On₂) Oc₁ On₁) := by
  rw [List.append_diff_of_subperm _ _ _ hL₁, List.append_diff_of_subperm _ _ _ hL₂,
      List.append_diff_of_subperm _ _ _ hR₁, List.append_diff_of_subperm _ _ _ hR₂]
  refine Sequent.multisetEqTo_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [List.diff_comm Lc₂ L Lc₁, List.append_assoc, List.append_assoc]
    exact List.perm_append_comm.append_left _
  · rw [List.diff_comm Rc₂ R Rc₁, List.append_assoc, List.append_assoc]
    exact List.perm_append_comm.append_left _
  · rcases hO with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- The children of a rule application, written out. -/
lemma LocalRuleApp.C_eq (lra : LocalRuleApp) : lra.C = lra.ress.map (fun Z =>
    (lra.L.diff lra.Lcond ++ Z.1, lra.R.diff lra.Rcond ++ Z.2.1,
      Olf.change lra.O lra.Ocond Z.2.2)) := by
  rcases lra with ⟨L, R, O, Lc, Rc, Oc, ress, lr, C, hC, pre⟩
  subst hC
  simp only [applyLocalRule]
  exact List.map_congr_left (by rintro ⟨a, b, c⟩ _; rfl)

/-- A rule can be applied at any sequent that satisfies its precondition. -/
lemma LocalRuleApp.exists_at (lra : LocalRuleApp) (Y : Sequent)
    (hL : lra.Lcond.Subperm Y.1) (hR : lra.Rcond.Subperm Y.2.1) (hO : lra.Ocond ⊆ Y.2.2) :
    ∃ lra' : LocalRuleApp, lra'.X = Y ∧ lra'.C = lra.ress.map (fun Z =>
      (Y.1.diff lra.Lcond ++ Z.1, Y.2.1.diff lra.Rcond ++ Z.2.1,
       Olf.change Y.2.2 lra.Ocond Z.2.2)) := by
  refine ⟨⟨Y.1, Y.2.1, Y.2.2, lra.Lcond, lra.Rcond, lra.Ocond, lra.ress, lra.lr, _, rfl,
    ⟨hL, hR, hO⟩⟩, rfl, ?_⟩
  simp only [applyLocalRule]
  exact List.map_congr_left (by rintro ⟨a, b, c⟩ _; rfl)

/-- **Two different rules at the same sequent can be applied in either order.** After
applying the first rule we can still apply the second one, and each sequent obtained in this
way also arises, up to permutation, by applying the two rules in the other order. -/
lemma LocalRuleApp.swap {lra1 lra2 : LocalRuleApp} (hX : lra1.X = lra2.X)
    (h1 : lra1.ress ≠ []) (h2 : lra2.ress ≠ [])
    (hne : ¬ (lra1.Lcond = lra2.Lcond ∧ lra1.Rcond = lra2.Rcond ∧ lra1.Ocond = lra2.Ocond))
    {W : Sequent} (hW : W ∈ lra1.C) :
    ∃ lraW : LocalRuleApp, lraW.X = W ∧ ∀ V ∈ lraW.C, ∃ Z ∈ lra2.C,
      ∃ lraZ : LocalRuleApp, lraZ.X = Z ∧ ∃ V' ∈ lraZ.C, V'.multisetEqTo V := by
  have hL : lra1.L = lra2.L := congrArg (fun s => s.1) hX
  have hR : lra1.R = lra2.R := congrArg (fun s => s.2.1) hX
  have hO : lra1.O = lra2.O := congrArg (fun s => s.2.2) hX
  obtain ⟨iL2, iL1, iR2, iR1, iO⟩ := LocalRuleApp.independent hX h1 h2 hne
  rw [← hL] at iL1
  rw [← hR] at iR1
  rw [LocalRuleApp.C_eq, List.mem_map] at hW
  obtain ⟨⟨Ln₁, Rn₁, On₁⟩, hres1, rfl⟩ := hW
  have hOW : lra2.Ocond ⊆ Olf.change lra1.O lra1.Ocond On₁ := by
    rcases iO with ⟨hc, hr⟩ | ⟨hc, _⟩
    · have hn : On₁ = none := hr _ hres1
      rw [hc, hn, Olf.change_old_none_none, hO]
      exact lra2.preconditionProof.2.2
    · rw [hc]; simp
  obtain ⟨lraW, hlraWX, hlraWC⟩ := LocalRuleApp.exists_at lra2
    (lra1.L.diff lra1.Lcond ++ Ln₁, lra1.R.diff lra1.Rcond ++ Rn₁,
      Olf.change lra1.O lra1.Ocond On₁)
    (by simpa using iL2.trans ((List.sublist_append_left _ _).subperm))
    (by simpa using iR2.trans ((List.sublist_append_left _ _).subperm))
    hOW
  refine ⟨lraW, hlraWX, ?_⟩
  intro V hV
  rw [hlraWC, List.mem_map] at hV
  obtain ⟨⟨Ln₂, Rn₂, On₂⟩, hres2, rfl⟩ := hV
  refine ⟨(lra1.L.diff lra2.Lcond ++ Ln₂, lra1.R.diff lra2.Rcond ++ Rn₂,
      Olf.change lra1.O lra2.Ocond On₂), ?_, ?_⟩
  · rw [LocalRuleApp.C_eq, List.mem_map]
    exact ⟨(Ln₂, Rn₂, On₂), hres2, by rw [hL, hR, hO]⟩
  · have hOZ : lra1.Ocond ⊆ Olf.change lra1.O lra2.Ocond On₂ := by
      rcases iO with ⟨hc, _⟩ | ⟨hc, hr⟩
      · rw [hc]; simp
      · have hn : On₂ = none := hr _ hres2
        rw [hc, hn, Olf.change_old_none_none]
        exact lra1.preconditionProof.2.2
    obtain ⟨lraZ, hlraZX, hlraZC⟩ := LocalRuleApp.exists_at lra1
      (lra1.L.diff lra2.Lcond ++ Ln₂, lra1.R.diff lra2.Rcond ++ Rn₂,
        Olf.change lra1.O lra2.Ocond On₂)
      (by simpa using iL1.trans ((List.sublist_append_left _ _).subperm))
      (by simpa using iR1.trans ((List.sublist_append_left _ _).subperm))
      hOZ
    refine ⟨lraZ, hlraZX,
      ((lra1.L.diff lra2.Lcond ++ Ln₂).diff lra1.Lcond ++ Ln₁,
       (lra1.R.diff lra2.Rcond ++ Rn₂).diff lra1.Rcond ++ Rn₁,
       Olf.change (Olf.change lra1.O lra2.Ocond On₂) lra1.Ocond On₁), ?_, ?_⟩
    · rw [hlraZC, List.mem_map]
      exact ⟨(Ln₁, Rn₁, On₁), hres1, rfl⟩
    · refine (Sequent.multisetEqTo_symm _ _).mp ?_
      refine applyLocalRule_comm iL2 iL1 iR2 iR1 ?_
      rcases iO with ⟨hc, hr⟩ | ⟨hc, hr⟩
      · exact Or.inl ⟨hc, hr _ hres1⟩
      · exact Or.inr ⟨hc, hr _ hres2⟩

/-- **Any rule may be applied first.** Given a local tableau for `X` and a rule application
to `X`, each child of that rule application has a local tableau whose end nodes are, up to
permutation, among the end nodes of the given local tableau. -/
lemma Sequent.dominatedBy_child : ∀ {X : Sequent} (lt : LocalTableau X) {lra : LocalRuleApp},
    lra.X = X → ∀ {W : Sequent}, W ∈ lra.C → W.DominatedBy (endNodesOf lt) := by
  intro X lt
  induction lt with
  | @sim X bas => intro lra hlra _ _; exact absurd (hlra ▸ bas) (nonbasic_of_localRuleApp lra)
  | @byLocalRule X lra2 X_def next IH =>
      subst X_def
      intro lra1 hX W hW
      by_cases hcl : lra2.X.closed
      · exact (Sequent.Refutable.child_of_closed hcl hX hW).dominatedBy _
      · have h1 : lra1.ress ≠ [] := fun h => hcl (hX ▸ LocalRuleApp.closed_of_ress_nil h)
        have h2 : lra2.ress ≠ [] := fun h => hcl (LocalRuleApp.closed_of_ress_nil h)
        by_cases hsame : lra1.Lcond = lra2.Lcond ∧ lra1.Rcond = lra2.Rcond
            ∧ lra1.Ocond = lra2.Ocond
        · have hCC : lra1.C = lra2.C :=
            LocalRuleApp.C_eq_of_cond_eq hX hsame.1 hsame.2.1 hsame.2.2
          rw [hCC] at hW
          exact ⟨next W hW, fun Y hY => ⟨Y, endNodeOfChild_to_endNode lra2 next rfl hW hY,
            Sequent.multisetEqTo_refl Y⟩⟩
        · obtain ⟨lraW, hlraWX, hswap⟩ := LocalRuleApp.swap hX h1 h2 hsame hW
          refine Sequent.DominatedBy.byRule hlraWX ?_
          intro V hV
          obtain ⟨Z, hZ, lraZ, hlraZX, V', hV', hVV⟩ := hswap V hV
          obtain ⟨lt', hlt'⟩ := IH Z hZ hlraZX hV'
          refine (Sequent.dominatedBy_of_msEq lt' hVV).mono ?_
          intro Y hY
          obtain ⟨Y', hY', he⟩ := hlt' Y hY
          exact ⟨Y', endNodeOfChild_to_endNode lra2 next rfl hZ hY', he⟩

/-- A local tableau for a basic sequent has that sequent as its only end node. -/
lemma endNodesOf_of_basic {X : Sequent} (bas : X.basic) (lt : LocalTableau X) :
    endNodesOf lt = [X] := by
  cases lt with
  | byLocalRule lra X_def next => exact absurd (X_def ▸ bas) (nonbasic_of_localRuleApp lra)
  | sim => simp only [endNodesOf]

/-- **The end nodes of a local tableau do not depend on the order in which the local rules
are applied.**

Local tableaux are maximal: their end nodes are basic. Here we only need the direction that
says that every end node of the *canonical* local tableau `uniLocalTab X'` occurs among the
end nodes of an arbitrary local tableau for a sequent `X` that is multiset-equal to `X'`. -/
theorem uniLocalTab_endNode_dominated {X X' : Sequent} (hX : X.multisetEqTo X')
    (lt : LocalTableau X) {Y' : Sequent} (hY' : Y' ∈ endNodesOf (uniLocalTab X')) :
    ∃ Y ∈ endNodesOf lt, Y.multisetEqTo Y' := by
  rw [uniLocalTab] at hY'
  split at hY'
  · rename_i bas
    have basX : X.basic := (Sequent.basic_iff_of_setEqTo (setEqTo_of_msEq hX)).mpr bas
    rw [endNodesOf_of_basic basX lt]
    simp only [endNodesOf, List.mem_singleton] at hY'
    subst hY'
    exact ⟨X, by simp, hX⟩
  · rename_i bas
    obtain ⟨W', hW', hY'W⟩ := endNodeIsEndNodeOfChild _ hY'
    obtain ⟨lraX, hlraXX, -, hfwd⟩ :=
      LocalRuleApp.exists_of_msEq ((Sequent.multisetEqTo_symm _ _).mp hX)
        (uniChoiceAt_X (Option.some_get (uniChoiceAt_isSome bas)).symm)
    obtain ⟨V, hV, hWV⟩ := hfwd W' hW'
    obtain ⟨ltV, hltV⟩ := Sequent.dominatedBy_child lt hlraXX hV
    obtain ⟨Y, hY, hYY'⟩ :=
      uniLocalTab_endNode_dominated ((Sequent.multisetEqTo_symm _ _).mp hWV) ltV hY'W
    obtain ⟨Z, hZ, hYZ⟩ := hltV Y hY
    exact ⟨Z, hZ, Sequent.multisetEqTo_trans ((Sequent.multisetEqTo_symm _ _).mp hYZ) hYY'⟩
termination_by X'
decreasing_by
  exact uniChoiceAt_C_lt (Option.some_get _).symm hW'


theorem Tableau.exists_isUni_of_msEq {H : History} {X : Sequent} (tab : Tableau H X) :
    ∀ (H' : History) (X' : Sequent), H.multisetEqTo H' → X.multisetEqTo X' →
      ∃ t : Tableau H' X', t.IsUni := by
  induction tab with
  | @loc H X nflprep nbas lt next IH =>
      intro H' X' hH hX
      have nflprep' : ¬ flprep H' X' := fun h => nflprep (flprep_of_multisetEqTo hH hX h)
      have nbas' : ¬ X'.basic := fun h =>
        nbas ((Sequent.basic_iff_of_setEqTo (setEqTo_of_msEq hX)).mpr h)
      have hall : ∀ Y' ∈ endNodesOf (uniLocalTab X'), ∃ t : Tableau (X' :: H') Y', t.IsUni := by
        intro Y' hY'
        obtain ⟨Y, hY, hYY⟩ := uniLocalTab_endNode_dominated hX lt hY'
        exact IH Y hY (X' :: H') Y' (List.Forall₂.cons hX hH) hYY
      choose f hf using hall
      exact ⟨.loc nflprep' nbas' (uniLocalTab X') f, ⟨uniLocalTab_isUni X', hf⟩⟩
  | @pdl H X Y nflprep bas r next IH =>
      intro H' X' hH hX
      have nflprep' : ¬ flprep H' X' := fun h => nflprep (flprep_of_multisetEqTo hH hX h)
      have bas' : X'.basic := (Sequent.basic_iff_of_setEqTo (setEqTo_of_msEq hX)).mp bas
      obtain ⟨Y', ⟨r'⟩, hYY⟩ := PdlRule.exists_of_multisetEqTo hX r
      obtain ⟨t, ht⟩ := IH (X' :: H') Y' (List.Forall₂.cons hX hH) hYY
      exact ⟨.pdl nflprep' bas' r' t, ht⟩
  | @lrep H X lpr =>
      intro H' X' hH hX
      exact ⟨.lrep (lpr_of_multisetEqTo hH.symm ((Sequent.multisetEqTo_symm _ _).mp hX) lpr),
        trivial⟩

lemma History.multisetEqTo_refl (H : History) : H.multisetEqTo H := by
  induction H with
  | nil => exact List.Forall₂.nil
  | cons hd tl IH => exact List.Forall₂.cons (Sequent.multisetEqTo_refl hd) IH

/-- For every tableau there is one that applies the rules in the canonical order, i.e. that
satisfies `Tableau.IsUni`. Immediate from `Tableau.exists_isUni_of_msEq`. -/
theorem Tableau.exists_isUni {H : History} {X : Sequent} (tab : Tableau H X) :
    ∃ t : Tableau H X, t.IsUni :=
  tab.exists_isUni_of_msEq H X (History.multisetEqTo_refl H) (Sequent.multisetEqTo_refl X)

/-- If there is any tableau, then there is a uniform one. -/
lemma Tableau.toUniform (tab : Tableau .nil X) :
    ∃ u_tab : Tableau .nil X, u_tab.isUniform :=
  let ⟨t, ht⟩ := tab.exists_isUni
  ⟨t, ht.isUniform⟩

namespace Uniformity

/-! ## Helpers

These are copies of results in `Pdl.ClusterInterpolation`, which are not available here
because that file imports this one. -/

/-- The right component of a basic sequent is basic.
Same as `Sequent.basic_rightOnly` in `Pdl.ClusterInterpolation`. -/
lemma basic_rightOnly {X : Sequent} (h : X.basic) : X.rightOnly.basic := by
  rcases X with ⟨L, R, O⟩
  obtain ⟨hb, hc⟩ := h
  constructor
  · intro f hf
    apply hb
    simp only [List.nil_append, List.mem_append] at hf ⊢
    tauto
  · intro hcl
    apply hc
    rcases hcl with hbot | ⟨f, hf, hnf⟩
    · left
      revert hbot
      simp_all [instMembershipFormulaSequent]
    · right
      exact ⟨f, by simp_all [instMembershipFormulaSequent], by simp_all
        [instMembershipFormulaSequent]⟩

/-- A right local rule cannot be applied when the right component of the sequent is basic.
Same as `LocalRuleApp.not_rightOnly_basic_of_isRightRule` in `Pdl.ClusterInterpolation`. -/
lemma not_rightOnly_basic_of_isRightRule (lra : LocalRuleApp)
    (h : lra.isRightRule) : ¬ lra.X.rightOnly.basic := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr
  case oneSidedR ress orule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨[], R, O, ∅, Rcond, none, _, LocalRule.oneSidedR orule YS_def, _, rfl,
        ⟨List.nil_subperm, pre.2.1, by simp⟩⟩
    simpa [Sequent.rightOnly] using this
  case loadedR χ lrule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨[], R, O, ∅, ∅, some (Sum.inr (~'χ)), _, LocalRule.loadedR χ lrule YS_def, _, rfl,
        ⟨List.nil_subperm, List.nil_subperm, pre.2.2⟩⟩
    simpa [Sequent.rightOnly] using this
  all_goals
    simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at h

/-- Where a right rule is applied, it is either a local rule or the node is basic.
Same as `FinePathIn.lra_or_basic_of_usesRightRule` in `Pdl.ClusterInterpolation`. -/
lemma lra_or_basic_of_usesRightRule : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), f.usesRightRule →
      (∃ lra, f.lra? = some lra ∧ lra.isRightRule) ∨ f.label.basic
  | _, _, _, .inLoc lp hint, h => by
      simp only [FinePathIn.usesRightRule, FinePathIn.lra?] at h ⊢
      rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
      · rw [hlt] at h
        exact Or.inl ⟨lra, rfl, h⟩
      · rw [hlt] at h; simp at h
  | _, _, .pdl _ bas _ _, .pdlHere, _ => Or.inr bas
  | _, _, _, .lrepHere, h => by simp [FinePathIn.usesRightRule] at h
  | _, _, _, .loc Y_in tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lra?, FinePathIn.label] using
        lra_or_basic_of_usesRightRule tail h
  | _, _, _, .pdl tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lra?, FinePathIn.label] using
        lra_or_basic_of_usesRightRule tail h

/-- The right component of the child obtained by applying the modal rule `(M)` to a sequent
whose loaded formula `~⌊·A⌋ξ` is on the right.
Same as `modRChildRightOnly` in `Pdl.ClusterInterpolation`. -/
def modRChildRight (A : Nat) (ξ : AnyFormula) (R : List Formula) : Sequent :=
  match ξ with
  | .normal φ => ⟨[], (~φ) :: projection A R, none⟩
  | .loaded χ => ⟨[], projection A R, some (Sum.inr (~'χ))⟩

/-- At a fine node with a *basic* right component where a right rule is applied, that rule
is one of the three `PdlRule`s acting on the right.
Same as `FinePathIn.basicRightStep` in `Pdl.ClusterInterpolation`. -/
lemma basicRightStep {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesRightRule) (hb : f.label.rightOnly.basic) :
      (f.atBigRoot ∧ f.label.2.2 = none)
      ∨ (∃ g, f.children = [g] ∧ g.atBigRoot ∧ g.label.2.2 = none)
      ∨ (∃ A ξ, f.label.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, f.children = [g] ∧ g.atBigRoot
          ∧ g.label.left = projection A f.label.left
          ∧ g.label.rightOnly = modRChildRight A ξ f.label.2.1) := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp hint =>
    simp only [FinePathIn.usesRightRule] at h
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at h
      simp only [FinePathIn.label] at hb
      rw [X_def] at hb
      exact absurd hb (not_rightOnly_basic_of_isRightRule lra h)
    · rw [hlt] at h; simp at h
  | @pdlHere Hist X Y nrep bas r next =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label, FinePathIn.children, FinePathIn.atBigRoot]
    cases r with
    | loadR hmem hnb hY => exact Or.inl ⟨trivial, rfl⟩
    | freeR hX hY =>
      exact Or.inr (Or.inl ⟨_, rfl, by simp [FinePathIn.atBigRoot],
        by simp [FinePathIn.label, hY]⟩)
    | @modR Y' L R A X' ξ hX hY =>
      subst hX
      right; right
      refine ⟨A, ξ, rfl, _, rfl, by simp [FinePathIn.atBigRoot], ?_, ?_⟩ <;>
        cases ξ <;> simp_all [modRChildRight, Sequent.rightOnly, FinePathIn.label]
    | _ => simp [PdlRule.isRightRule] at h
  | lrepHere => simp [FinePathIn.usesRightRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.loc Y_in g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .loc Y_in g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)
  | pdl tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.pdl g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .pdl g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)

/-- A fine node that is a node in the coarse sense has the label of that coarse node.
Same as `FinePathIn.label_eq_nodeAt_base` in `Pdl.ClusterInterpolation`. -/
lemma label_eq_nodeAt_base {H Z} {tab' : Tableau H Z} (f : FinePathIn tab')
    (h : f.atBigRoot) : f.label = nodeAt f.base := by
  have := congrArg FinePathIn.label (f.eq_toFine_base_of_atBigRoot h)
  rwa [PathIn.label_toFine] at this

/-- If a child of a local rule application is loaded on the right, then so is its premise.
Same as `LocalRuleApp.isRight_of_mem_C` in `Pdl.ClusterInterpolation`. -/
lemma isRight_of_mem_C (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.2.2.isRight → lra.X.2.2.isRight := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  intro Y hY hYR
  cases lr
  case oneSidedL ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hY
    obtain ⟨res, -, rfl⟩ := hY
    simpa using hYR
  case oneSidedR ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hY
    obtain ⟨res, -, rfl⟩ := hY
    simpa using hYR
  case LRnegL => simp [applyLocalRule] at hY
  case LRnegR => simp [applyLocalRule] at hY
  case loadedL χ lrule YS_def =>
    exfalso
    subst YS_def
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    simp only at hO
    subst hO
    simp only [applyLocalRule, List.map_map, List.mem_map, Function.comp_apply] at hY
    obtain ⟨⟨Lnew, Onew⟩, -, rfl⟩ := hY
    rcases Onew with _ | o <;> simp_all [Olf.isRight]
  case loadedR χ lrule YS_def =>
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    simp only at hO
    subst hO
    simp [Olf.isRight]

/-- If some end node of a local tableau is loaded on the right, then so is its root.
Same as `LocalTableau.isRight_of_mem_endNodesOf` in `Pdl.ClusterInterpolation`. -/
lemma isRight_of_mem_endNodesOf : ∀ {Z : Sequent} (lt : LocalTableau Z),
    ∀ Y ∈ endNodesOf lt, Y.2.2.isRight → Z.2.2.isRight
  | _, .sim _, Y, hY, hYR => by
      simp only [endNodesOf, List.mem_singleton] at hY
      exact hY ▸ hYR
  | _, .byLocalRule lra X_def next, Y, hY, hYR => by
      subst X_def
      simp only [endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
        Subtype.exists] at hY
      obtain ⟨_, ⟨W, W_in, rfl⟩, hY⟩ := hY
      exact isRight_of_mem_C lra W W_in
        (isRight_of_mem_endNodesOf (next W W_in) Y hY hYR)

/-- The end nodes below a local path are end nodes of the local tableau at that path.
Same as `LocalPathIn.mem_endNodesOf_ltAt` in `Pdl.ClusterInterpolation`. -/
lemma mem_endNodesOf_ltAt {Z : Sequent} {lt : LocalTableau Z} (lp : LocalPathIn lt) :
    ∀ Yh ∈ lp.endNodesBelow, (Yh : Sequent) ∈ endNodesOf lp.ltAt := by
  induction lp with
  | nil => intro Yh _; exact Yh.2
  | cons Y_in tail IH =>
    intro Yh h
    simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at h
    obtain ⟨Z, hZ, hmem, rfl⟩ := h
    exact IH ⟨Z, hZ⟩ hmem

/-- A fine node that is not a coarse node and has a coarse child loaded on the right is
itself loaded on the right.
Same as `FinePathIn.isRight_of_mem_coarseChildrenBelow` in `Pdl.ClusterInterpolation`. -/
lemma isRight_of_mem_coarseChildrenBelow : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ¬ f.atBigRoot →
      ∀ q ∈ f.coarseChildrenBelow, (nodeAt q).2.2.isRight → f.label.2.2.isRight
  | _, _, _, .inLoc lp _, _, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
      obtain ⟨Y, Y_in, hmem, rfl⟩ := hq
      rw [nodeAt_loc_nil] at hqR
      exact isRight_of_mem_endNodesOf lp.ltAt Y (mem_endNodesOf_ltAt lp ⟨Y, Y_in⟩ hmem) hqR
  | _, _, _, .pdlHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .lrepHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .loc Y_in tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_loc] at hqR
      exact isRight_of_mem_coarseChildrenBelow tail
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR
  | _, _, _, .pdl tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_pdl] at hqR
      exact isRight_of_mem_coarseChildrenBelow tail
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR

variable {X : Sequent} {tab : Tableau .nil X}

/-- Lemma 9.4 (a) at the fine level: every fine node of a loaded cluster is loaded on the
right. For a coarse node this is `LoadedCluster.all_right_loaded`, and for a node inside a
local tableau it follows because that node has a coarse child in the cluster. -/
lemma isRight_of_memFine (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : C.memFine f) : f.label.2.2.isRight := by
  by_cases hbr : f.atBigRoot
  · rw [label_eq_nodeAt_base f hbr]
    exact C.all_right_loaded _ hf.1
  · rcases hf.2 with h | ⟨q, hq, hqC⟩
    · exact absurd h hbr
    · exact isRight_of_mem_coarseChildrenBelow f hbr q hq (C.all_right_loaded q hqC)

/-- Lemma 9.7 (e): at a node `t` of `C^R_Δ` with `Δ` basic the rule applied is the modal
rule `(M)` for the loaded formula `~⌊·A⌋ξ` of `Δ`, so that the right component of the
unique child of `t` only depends on `Δ`.
Same as `LoadedCluster.basicModalStepAt` in `Pdl.ClusterInterpolation`. -/
lemma basicModalStep (C : LoadedCluster tab) {Δ : Sequent}
    (hb : Δ.basic) {t : FinePathIn tab} (ht : t ∈ C.nodesWithFineRight Δ) :
    ∃ A ξ, Δ.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, t.children = [g]
      ∧ g.label.rightOnly = modRChildRight A ξ Δ.2.1 := by
  simp only [LoadedCluster.nodesWithFineRight, LoadedCluster.nodesWithFine, List.mem_filter,
    decide_eq_true_eq] at ht
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht
  have hmf : C.memFine t := (C.mem_fineCL t).mp ht_CL
  have hDl : Δ.2.2 = t.label.2.2 := by rw [← ht_lab]; rfl
  have hDr : Δ.2.1 = t.label.2.1 := by rw [← ht_lab]; rfl
  obtain ⟨c, hc, hcmf⟩ := C.exists_child_memFine_of_not_isLrep hmf
    (t.not_isLrep_base_of_usesRightRule ht_right)
  rcases basicRightStep t ht_right (ht_lab ▸ hb) with
    ⟨hbr, hnone⟩ | ⟨g, hg, hgbr, hgnone⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
  · exfalso
    have hrl := C.all_right_loaded t.base hmf.1
    rw [← label_eq_nodeAt_base t hbr, hnone] at hrl
    simp at hrl
  · exfalso
    rw [hg, List.mem_singleton] at hc
    subst hc
    have hrl := C.all_right_loaded c.base hcmf.1
    rw [← label_eq_nodeAt_base c hgbr, hgnone] at hrl
    simp at hrl
  · exact ⟨A, ξ, by rw [hDl]; exact hA, g, hg, by rw [hDr]; exact hg2⟩

/-- The key computation for condition U2: if the same local rule with the same principal
formulas is applied at two nodes with the same right component, then the right components
of the children agree, including their order. This holds because a local rule application
deletes the principal formulas from, and adds the results to, the given sequent. -/
lemma map_rightOnly_C_eq {lra₁ lra₂ : LocalRuleApp} (hsame : lra₁.SameRuleAs lra₂)
    (hX : lra₁.X.rightOnly = lra₂.X.rightOnly) :
    lra₁.C.map Sequent.rightOnly = lra₂.C.map Sequent.rightOnly := by
  obtain ⟨-, hRcond, hOcond, hress, -⟩ := hsame
  have hR : lra₁.R = lra₂.R := congrArg (fun Y => Y.2.1) hX
  have hO : lra₁.O = lra₂.O := congrArg (fun Y => Y.2.2) hX
  rw [lra₁.hC, lra₂.hC]
  simp only [applyLocalRule, List.map_map, Function.comp_def, Sequent.rightOnly]
  rw [hress]
  refine List.map_congr_left ?_
  rintro ⟨Lnew, Rnew, Onew⟩ -
  simp only [hRcond, hOcond, hR, hO]

end Uniformity

/-- In a uniform tableau any loaded cluster has the property `HasUniformSteps` needed for
the construction of the quasi-tableau: any two nodes of the cluster with the same right
component `Δ` at which a right rule is applied have the same right components below them.

The case where `Δ` is basic does not use uniformity: there the rule applied is the modal
rule for the loaded formula of `Δ` (Lemma 9.7 (e)). The case where `Δ` is not basic is
Lemma 9.7 (f), and uses both U1 and U2. -/
def LoadedCluster.uniformOfUniTab {tab : Tableau .nil X}
    (C : LoadedCluster tab) (uni_tab : tab.isUniform)
    : C.HasUniformSteps := by
  obtain ⟨u1, u2⟩ := uni_tab.1
  intro Δ f hf g hg
  have hf' := hf
  have hg' := hg
  simp only [LoadedCluster.nodesWithFineRight, LoadedCluster.nodesWithFine, List.mem_filter,
    decide_eq_true_eq] at hf' hg'
  obtain ⟨⟨hf_CL, hf_lab⟩, hf_right⟩ := hf'
  obtain ⟨⟨hg_CL, hg_lab⟩, hg_right⟩ := hg'
  by_cases hb : Δ.basic
  · -- Lemma 9.7 (e): the modal rule is applied at both nodes, to the loaded formula of `Δ`.
    obtain ⟨A, ξ, hAξ, cf, hcf, hcf_right⟩ := Uniformity.basicModalStep C hb hf
    obtain ⟨A', ξ', hAξ', cg, hcg, hcg_right⟩ := Uniformity.basicModalStep C hb hg
    have hAA : A' = A ∧ ξ' = ξ := by
      rw [hAξ] at hAξ'
      simp only [Option.some.injEq, Sum.inr.injEq] at hAξ'
      rcases ξ' with φ | χ <;> rcases ξ with φ' | χ' <;> simp_all
    rw [hAA.1, hAA.2] at hcg_right
    rw [hcf, hcg]
    simp only [List.map_cons, List.map_nil, hcf_right, hcg_right]
  · -- Lemma 9.7 (f): the same local rule is applied at both nodes, by U1 and U2.
    have hfb : ¬ f.label.basic := fun h => hb (hf_lab ▸ Uniformity.basic_rightOnly h)
    have hgb : ¬ g.label.basic := fun h => hb (hg_lab ▸ Uniformity.basic_rightOnly h)
    obtain ⟨lraf, hlraf, hfR⟩ :=
      (Uniformity.lra_or_basic_of_usesRightRule f hf_right).resolve_right hfb
    obtain ⟨lrag, hlrag, hgR⟩ :=
      (Uniformity.lra_or_basic_of_usesRightRule g hg_right).resolve_right hgb
    -- Both nodes are loaded on the right, being nodes of the cluster.
    have hfRight : f.label.2.2.isRight :=
      Uniformity.isRight_of_memFine C ((C.mem_fineCL f).mp hf_CL)
    have hgRight : g.label.2.2.isRight :=
      Uniformity.isRight_of_memFine C ((C.mem_fineCL g).mp hg_CL)
    -- By U1 their left components are basic, because a right rule is applied at them.
    have hfleft : f.label.leftFree.basic := by
      by_contra hcon
      exact f.not_left_and_right
        ⟨(u1 f (f.not_isLrep_base_of_usesRightRule hf_right)).1 hfRight hcon, hf_right⟩
    have hgleft : g.label.leftFree.basic := by
      by_contra hcon
      exact g.not_left_and_right
        ⟨(u1 g (g.not_isLrep_base_of_usesRightRule hg_right)).1 hgRight hcon, hg_right⟩
    -- Hence U2 applies.
    have hsame := (u2 f g lraf lrag hlraf hlrag).1 hfRight (hf_lab.trans hg_lab.symm)
      (hf_lab ▸ hb) hfleft hgleft hfR hgR
    obtain ⟨hfX, hfC⟩ := f.lra?_spec hlraf
    obtain ⟨hgX, hgC⟩ := g.lra?_spec hlrag
    have hXeq : lraf.X.rightOnly = lrag.X.rightOnly := by
      rw [← hfX, ← hgX, hf_lab, hg_lab]
    calc f.children.map (fun h => h.label.rightOnly)
        = (f.children.map FinePathIn.label).map Sequent.rightOnly := by
          simp only [List.map_map, Function.comp_def]
      _ = lraf.C.map Sequent.rightOnly := by rw [hfC]
      _ = lrag.C.map Sequent.rightOnly := Uniformity.map_rightOnly_C_eq hsame hXeq
      _ = (g.children.map FinePathIn.label).map Sequent.rightOnly := by rw [hgC]
      _ = g.children.map (fun h => h.label.rightOnly) := by
          simp only [List.map_map, Function.comp_def]
