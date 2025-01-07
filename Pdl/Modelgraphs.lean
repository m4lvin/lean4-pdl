import Mathlib.Tactic.ClearExcept
import Mathlib.Data.Vector.Basic

import Pdl.UnfoldBox
import Pdl.UnfoldDia

/-! # Model Graphs (Section 7.1) -/

open Formula

open HasLength

/-! ## Definition of Model Graphs -/

def saturated : Finset Formula → Prop
  -- TODO: change P Q notation to φ ψ
  | X => ∀ (P Q : Formula) (α : Program),
    -- propositional closure:
      ((~~P) ∈ X → P ∈ X)
    ∧ (P⋀Q ∈ X → P ∈ X ∧ Q ∈ X)
    ∧ ((~(P⋀Q)) ∈ X → (~P) ∈ X ∨ (~Q) ∈ X)
    -- programs closure, now only two general cases, no program subcases:
    ∧ ((⌈α⌉P) ∈ X → ∃ l : TP α, (Xset α l P).all (fun y => y ∈ X))
    ∧ ((~⌈α⌉P) ∈ X → ∃ Fδ ∈ H α, (Yset Fδ P).all (fun y => y ∈ X))

/-- Q α -/
def Q {W : Finset (Finset Formula)} (R : Nat → W → W → Prop)
  : Program → W → W → Prop
| ·c     => R c
| ?'τ    => fun v w => v = w ∧ τ ∈ v.1
| α ⋓ β  => fun v w => Q R α v w ∨ Q R β v w
| α ;' β => Relation.Comp (Q R α) (Q R β)
| ∗ α    => Relation.ReflTransGen (Q R α)

-- Definition 19, page 31
def ModelGraph (W : Finset (Finset Formula)) :=
  let i := ∀ X : W, saturated X.val ∧ ⊥ ∉ X.val ∧ ∀ pp, (·pp : Formula) ∈ X.val → (~(·pp)) ∉ X.val
  let ii M := ∀ X p, (·p : Formula) ∈ X.val ↔ M.val X p
  -- Note: Borzechowski only has → in ii. We follow BRV, Def 4.18 and 4.84.
  let iii M := ∀ X Y a P, M.Rel a X Y → (⌈·a⌉P) ∈ X.val → P ∈ Y.val
  let iv M := ∀ X α P, (~⌈α⌉P) ∈ X.val → ∃ Y, (Q M.Rel) α X Y ∧ (~P) ∈ Y.val
  -- Note: In iii "a" is atomic, but in iv "α" is any program!
  Subtype fun M : KripkeModel W => i ∧ ii M ∧ iii M ∧ iv M

/-! ## Truth Lemma -/

-- TODO: it seems default 200000 is not enough for mutual theorems below?!
set_option maxHeartbeats 2000000
-- set_option trace.profiler true

theorem get_eq_getzip {X Y : α} {i : Fin ((List.length (l ++ [Y])))} {h} :
  List.get (X :: (l ++ [Y])) (Fin.castSucc i) = (List.get ((x, X) :: List.zip δ (l ++ [Y])) ⟨i.val, h⟩).2 := by
  -- special thanks to droplet739
  simp only [←List.zip_cons_cons]
  simp only [List.get_eq_getElem, List.length_cons, Fin.coe_castSucc]
  rw [List.getElem_zip]

theorem loadClaimHelper {Worlds : Finset (Finset Formula)}
    {MG : ModelGraph Worlds}
    {X Y : { x // x ∈ Worlds }}
    {δ : List Program}
    {φ : Formula}
    {l : List { x // x ∈ Worlds }}
    (length_def: l.length + 1 = δ.length)
    (δφ_in_X : (⌈⌈δ⌉⌉φ) ∈ X.val)
    (lchain : List.Chain' (pairRel MG.1) (List.zip ((?'⊤) :: δ) (X :: l ++ [Y])))
    (IHδ : ∀ d ∈ δ, ∀ (X' Y' : { x // x ∈ Worlds }) (φ' : Formula), (⌈d⌉φ') ∈ X'.1 → relate (MG.1) d X' Y' → φ' ∈ Y'.1)
    (i : Fin (List.length (X :: l ++ [Y])))
    :
    (⌈⌈δ.drop i⌉⌉φ) ∈ ((X :: l ++ [Y]).get i).val := by
  induction i using Fin.inductionOn
  case zero =>
    simp_all only [instBot, insTop, List.cons_append, List.zip_cons_cons, Subtype.forall,
      List.length_cons, Nat.succ_eq_add_one, Fin.val_zero, List.drop_zero, List.get_cons_zero]
      -- uses δφ_in_X
  case succ i IH =>
    simp_all only [List.cons_append, List.length_cons, List.append_eq, Fin.val_succ, List.get_cons_succ']
    have help1 : (List.append l [Y]).length = δ.length := by simp [length_def]
    apply IHδ (δ.get (i.cast help1)) (by apply List.get_mem) (List.get (X :: l ++ [Y]) i.castSucc)
    · have : (⌈List.get δ (i.cast help1)⌉⌈⌈List.drop (i + 1) δ⌉⌉φ) = (⌈⌈List.drop (i.castSucc) δ⌉⌉φ) := by
        simp only [List.append_eq, Fin.coe_castSucc]
        have := @List.drop_eq_getElem_cons _ i δ (by rw [← length_def]; have := Fin.is_lt i; convert this; simp)
        rw [this]
        simp only [List.get_eq_getElem, Fin.coe_cast, List.append_eq, List.getElem_cons_drop]
        cases i
        simp_all only [instBot, insTop, List.zip_cons_cons, Subtype.forall, List.append_eq,
          Fin.castSucc_mk, Fin.cast_mk]
        rw [Formula.boxes_cons]
      rw [this]
      exact IH
    · simp [relate]
      -- It now remains to make lchain usable
      rw [List.chain'_iff_get] at lchain
      specialize lchain i ?_
      · rcases i with ⟨val, hyp⟩
        simp_all only [insTop, List.zip_cons_cons, List.length_cons, List.length_zip,
          List.length_append, List.length_singleton, min_self, add_tsub_cancel_right, instBot,
          List.get_eq_getElem, List.getElem_cons_succ, List.getElem_zip, Subtype.forall,
          List.append_eq, Fin.castSucc_mk]
        rw [← length_def]
        simp at hyp
        exact hyp
      simp [pairRel, instBot, insTop, List.cons_append, List.zip_cons_cons, List.length_cons, List.append_eq, List.get_cons_succ, List.getElem_zip] at lchain
      convert lchain
      apply get_eq_getzip

-- Originally MB Lemma 9, page 32, stronger version for induction loading.
-- Now also using Q relation to overwrite tests.
mutual

-- C3 in notes
theorem Q_then_relate (MG : ModelGraph Worlds) α (X Y : Worlds) :
    Q MG.val.Rel α X Y → relate MG.val α X Y := by
  cases α
  case atom_prog =>
    simp only [instBot, Q, relate, imp_self]
  case sequence α β =>
    have := Q_then_relate MG α
    have := Q_then_relate MG β
    simp only [instBot, Subtype.forall, Q, Relation.Comp, Subtype.exists,
      relate, forall_exists_index, and_imp] at *
    tauto
  case union α β =>
    have := Q_then_relate MG α
    have := Q_then_relate MG β
    simp only [instBot, Subtype.forall, Q, relate] at *
    tauto
  case star α =>
    simp only [instBot, Q, relate]
    apply Relation.ReflTransGen.lift
    intro a b Qab
    exact Q_then_relate MG α a b Qab
  case test φ =>
    have := loadedTruthLemma MG X φ
    simp [Q, relate, Relation.Comp] at *
    intro X_is_Y phi_in_X
    subst X_is_Y
    constructor
    · tauto
    · tauto
termination_by
  lengthOf α

-- C1 and C2 in notes
theorem loadedTruthLemma {Worlds} (MG : ModelGraph Worlds) X:
    ∀ P, (P ∈ X.val → evaluate MG.val X P) -- (+)
    ∧ ((~P) ∈ X.val → ¬evaluate MG.val X P) -- (-)
    :=
  by
  intro P
  cases P -- no "induction", use recursive calls!
  case bottom =>
    repeat' constructor
    · intro P_in_X
      apply absurd P_in_X
      have ⟨_,⟨i,_,_,_⟩⟩ := MG
      specialize i X
      tauto
    · simp only [instBot, evaluate, not_false_eq_true, implies_true]
  case atom_prop pp =>
    have ⟨M,⟨i,ii,_,_⟩⟩ := MG
    repeat' constructor
    · intro P_in_X
      simp only [evaluate]
      rw [ii X pp] at P_in_X
      exact P_in_X
    · intro notP_in_X
      simp only [evaluate]
      rw [← ii X pp]
      rcases i X with ⟨_, _, P_in_then_notP_not_in⟩
      specialize P_in_then_notP_not_in pp
      tauto
  case neg Q =>
    have ⟨plus,minus⟩ := loadedTruthLemma MG X Q
    repeat' constructor
    · intro notQ_in_X
      simp only [evaluate]
      exact minus notQ_in_X
    · intro notnotQ_in_X
      simp only [instBot, evaluate, not_not]
      have ⟨M,⟨i,_,_,_⟩⟩ := MG
      rcases i X with ⟨X_saturated, _, _⟩
      exact plus ((X_saturated Q Q (?'Q)).1 notnotQ_in_X)
  case and Q R =>
    have ⟨plus_Q, minus_Q⟩ := loadedTruthLemma MG X Q
    have ⟨plus_R, minus_R⟩ := loadedTruthLemma MG X R
    have ⟨M,⟨i,_,iii,_⟩⟩ := MG
    rcases i X with ⟨X_saturated, _, _⟩
    rcases X_saturated Q R (?'Q) with ⟨_, ⟨andSplit, ⟨notAndSplit, _⟩⟩⟩
    repeat' constructor
    · intro QandR_in_X
      specialize andSplit QandR_in_X
      cases' andSplit with Q_in_X R_in_X
      simp only [evaluate]
      constructor
      · exact plus_Q Q_in_X
      · exact plus_R R_in_X
    · intro notQandR_in_X
      unfold evaluate; rw [not_and_or]
      specialize notAndSplit notQandR_in_X
      cases' notAndSplit with notQ_in_X notR_in_X
      · left; exact minus_Q notQ_in_X
      · right; exact minus_R notR_in_X
  case box a P =>
    repeat' constructor
    all_goals simp
    · intro boxP_in_X
      intro Y Y_in X_rel_Y
      have ⟨plus_Y, _⟩ := loadedTruthLemma MG ⟨Y, Y_in⟩ P
      have oh_a := loadedTruthLemmaProg MG a X
      apply plus_Y
      apply oh_a P boxP_in_X ⟨Y,Y_in⟩ X_rel_Y
    · intro notBoxP_in_X
      have ⟨M,⟨i,ii,iii,iv⟩⟩ := MG
      have my_iv := iv X a P notBoxP_in_X
      rcases my_iv with ⟨⟨Y, Y_in⟩, X_a_Y, nP_in_Y⟩
      use Y, Y_in
      constructor
      · exact Q_then_relate ⟨M,⟨i,ii,iii,iv⟩⟩ a X ⟨Y,Y_in⟩ X_a_Y
      · have ⟨_, minus_Y⟩ := loadedTruthLemma ⟨M,⟨i,ii,iii,iv⟩⟩ ⟨Y, Y_in⟩ P
        simp only at minus_Y
        specialize minus_Y nP_in_Y
        convert minus_Y
termination_by
  f => lengthOf f

-- C4 in notes
theorem loadedTruthLemmaProg {Worlds} (MG : ModelGraph Worlds) α :
    ∀ X φ, ((⌈α⌉φ) ∈ X.val → (∀ (Y : Worlds), relate MG.val α X Y → φ ∈ Y.val)) -- (0)
    := by
  intro X φ boxP_in_X
  cases α_def : α <;> intro Y X_rel_Y
  -- NOTE we do `atom` and `star` but then `all_goals`
  case atom_prog a =>
    subst α_def
    simp only [instBot, relate] at X_rel_Y
    have ⟨_,⟨_,_,iii,_⟩⟩ := MG
    exact iii X Y _ _ X_rel_Y boxP_in_X
  case star β =>
    subst α_def
    simp at X_rel_Y
    rw [ReflTransGen.iff_finitelyManySteps] at X_rel_Y
    rcases X_rel_Y with ⟨n, claim⟩
    induction n generalizing X φ -- not generalizing Y, but φ to be replaced φ with ⌈∗β⌉φ below!
    · rcases claim with ⟨YS, X_def, Y_def, _⟩
      have : YS.head = YS.last := by
        have := Mathlib.Vector.exists_eq_cons YS
        aesop
      rw [this] at X_def
      subst X_def Y_def
      have := ((MG.2.1 (YS.last)).1 φ φ (∗β)).right.right.right.left boxP_in_X
      rcases this with ⟨ℓ, mysat⟩
      simp_all [Xset, F, P]
    case succ m innerIH => -- Z U X_β_Z Z_βS_U IH_φ_in_Z =>
      rcases claim with ⟨YS, X_def, Y_def, relSteps⟩
      let Z := YS.get 1
      have X_β_Z : relate MG.1 β X Z := by
        specialize relSteps 0
        unfold Z
        convert relSteps
        aesop
      have := ((MG.2.1 X).1 φ φ (∗β)).right.right.right.left boxP_in_X
      rcases this with ⟨ℓ, mysat⟩
      simp [Xset] at mysat
      have TP_eq : TP (∗β) = TP β := by simp [TP,testsOfProgram]
      -- Now we use the outer IH for C2 on all formulas in F(β,ℓ):
      have X_ConF : evaluate MG.1 X (Con $ F β ℓ) := by
        rw [conEval]
        intro ψ ψ_in
        -- termination here will need F_goes_down when moving this into the above?
        have _forTermination : lengthOfFormula ψ < lengthOfProgram (∗β) := by
          apply F_goes_down
          simp [F]
          convert ψ_in
        apply (loadedTruthLemma MG X ψ).1
        apply mysat.1; simp [F]; assumption
      -- now use Lemma 34:
      have := existsBoxFP β X_β_Z ℓ X_ConF
      rcases this with ⟨δ, δ_in_P, X_δ_Z⟩
      -- Notes use δ ≠ [] from X ≠ Z, but ReflTransGen.iff_finitelyManySteps does not provide that.
      cases em (δ = [])
      case inl hyp =>
        subst hyp
        simp only [relateSeq] at X_δ_Z
        apply innerIH X φ boxP_in_X
        -- rest here is similar to same part in all_goals below.
        refine ⟨YS.tail, ?_, ?_, ?_⟩
        · rw [← Mathlib.Vector.get_zero]
          rw [Mathlib.Vector.get_tail_succ]
          aesop
        · rw [Mathlib.Vector.last_def]
          rw [Mathlib.Vector.get_tail_succ]
          aesop
        · intro i
          clear * -relSteps
          specialize relSteps i.succ
          have : ((Mathlib.Vector.tail YS).get i.castSucc) = (YS.get ((Fin.succ i).castSucc)) := by
            aesop
          rw [this]; clear this
          have : ((Mathlib.Vector.tail YS).get i.succ) = (YS.get ((Fin.succ i).succ)) := by
            aesop
          rw [this]; clear this
          exact relSteps
      case inr δ_notEmpty =>
        have : (δ ++ [∗β]) ∈ P (∗β) ℓ := by
          simp [P]
          all_goals simp_all
        have δβSφ_in_X : (⌈⌈δ⌉⌉⌈∗β⌉φ) ∈ X.1 := by
          have := mysat.2 _ this
          simp_all [boxes_append]
        have : (⌈∗β⌉φ) ∈ Z.1 := by
          clear innerIH
          -- Now we apply IH of C4 loadedTruthLemmaProg to all elements in δ
          have IHδ : ∀ d ∈ δ, ∀ (X' Y' : Worlds),
              ∀ φ', (⌈d⌉φ') ∈ X'.val → relate MG.val d X' Y' → φ' ∈ Y'.val := by
            intro d d_in_δ X' Y' φ' dφ_in_X' X'_d_Y'
            have _forTermination : lengthOf d < lengthOf (∗β) := by
              have := P_goes_down d_in_δ δ_in_P
              cases em β.isAtomic <;> cases em β.isStar
              all_goals
                simp_all [P]
                try linarith
            exact loadedTruthLemmaProg MG d X' φ' dφ_in_X' Y' X'_d_Y'
          have := relateSeq_toChain' X_δ_Z δ_notEmpty
          rcases this with ⟨l, length_def, lchain⟩
          -- now combine lchain with IHδ
          suffices loadClaim : ∀ i : Fin (X :: l ++ [Z]).length,
              (⌈⌈δ.drop i⌉⌉⌈∗β⌉φ) ∈ ((X :: l ++ [Z]).get i).val by
            specialize loadClaim (Fin.last _)
            simp [length_def] at loadClaim
            convert loadClaim
            have := @List.get_last _ Z (X :: l) (Fin.last _)
            simp_all
          intro i
          exact loadClaimHelper length_def δβSφ_in_X lchain IHδ i
        -- lastly, apply innerIH on Z and Y:
        apply innerIH Z _ this
        clear innerIH
        simp_all
        refine ⟨YS.tail, ?_, ?_, ?_⟩
        · unfold Z
          rw [← Mathlib.Vector.get_zero]
          rw [Mathlib.Vector.get_tail_succ]
          rfl
        · rw [Mathlib.Vector.last_def, Mathlib.Vector.last_def]
          rw [Mathlib.Vector.get_tail_succ]
          rfl
        · intro i
          clear * -relSteps
          specialize relSteps i.succ
          have : ((Mathlib.Vector.tail YS).get i.castSucc) = (YS.get i.succ.castSucc) := by aesop
          rw [this]; clear this
          have : ((Mathlib.Vector.tail YS).get i.succ) = (YS.get i.succ.succ) := by aesop
          rw [this]; clear this
          exact relSteps
  -- remaining cases: sequence, union, test
  all_goals -- sic!
    have satX := (MG.prop.1 X).left
    simp only [saturated, List.all_eq_true, decide_eq_true_eq, Prod.exists] at satX
    -- use saturatedness to get a testprofile ℓ:
    rcases (satX φ φ α).right.right.right.left boxP_in_X with ⟨ℓ, Xset_sub_X⟩
    simp only [Xset, List.mem_append, List.mem_map] at Xset_sub_X
    have X_F : ∀ τ ∈ F _ (α_def ▸ ℓ), evaluate MG.val X τ := by
      intro τ τ_in
      -- Now we use IH of C2 on the tests in a
      -- NOTE: for this (in the test case, not sequence) we tweaked `lengthOfProgram (?'φ)` ;-)
      have _forTermination : lengthOfFormula τ < lengthOfProgram _ := F_goes_down τ_in
      have := loadedTruthLemma MG X τ
      subst α_def
      simp_all only [instBot, relate, Subtype.exists, lengthOfProgram, true_or, forall_true_left]
    have := existsBoxFP _ X_rel_Y (α_def ▸ ℓ)
      (by simp [modelCanSemImplyForm,conEval]; exact X_F)
    rcases this with ⟨δ, δ_in_P, X_δ_Y⟩
    have δφ_in_X : (⌈⌈δ⌉⌉φ) ∈ X.val := by
      simp_all only [instBot, relate, Subtype.exists]
      subst_eqs
      apply Xset_sub_X
      right
      use δ
    -- Now we apply IH of C4 to all elements in δ
    have IHδ : ∀ d ∈ δ, ∀ (X' Y' : Worlds), ∀ φ',
        (⌈d⌉φ') ∈ X'.val → relate MG.val d X' Y' → φ' ∈ Y'.val := by
      intro d d_in_δ X' Y' φ' dφ_in_X' X'_d_Y'
      have _forTermination : lengthOf d < lengthOf α := by
        have := P_goes_down d_in_δ δ_in_P
        simp_all [Program.isAtomic, Program.isStar]
      exact loadedTruthLemmaProg MG d X' φ' dφ_in_X' Y' X'_d_Y'
    -- NOTE: tried `induction δ` before, but that yields a too weak/annoying IH.
    -- Instead, check if δ is empty, and in non-empty case use `relateSeq_toChain'`.
    cases em (δ = [])
    · simp_all [relateSeq] -- uses δφ_in_X from above.
    case inr δ_notEmpty =>
      have := relateSeq_toChain' X_δ_Y δ_notEmpty
      rcases this with ⟨l, length_def, lchain⟩
      -- Now we prove a claim to combine `lchain` with `IHδ`.
      suffices loadClaim : ∀ i : Fin (X :: l ++ [Y]).length,
          (⌈⌈δ.drop i⌉⌉φ) ∈ ((X :: l ++ [Y]).get i).val by
        specialize loadClaim (Fin.last _)
        simp [length_def] at loadClaim
        convert loadClaim
        have := @List.get_last _ Y (X :: l) (Fin.last _)
        simp_all
      intro i
      exact loadClaimHelper length_def δφ_in_X lchain IHδ i

termination_by
  _ _ _ => lengthOf α

end

theorem truthLemma {Worlds} (MG : ModelGraph Worlds) :
    ∀ X : Worlds, ∀ P, P ∈ X.val → evaluate MG.val X P :=
  by
  intro X P
  have ⟨claim, _⟩ := loadedTruthLemma MG X P
  exact claim

/-! ## Additional Q relations for the completeness proof -/

/-- Q_F - for a list `F` of tests (instead of a set in the notes). -/
def Qtests {W : Finset (Finset Formula)} (R : Nat → W → W → Prop) (F : List Formula) : W → W → Prop
| v, w => v == w ∧ ∀ τ ∈ F, Q R (?' τ) v w

/-- Q_δ for a list `δ` of programs. -/
def Qsteps {W : Finset (Finset Formula)} (R : Nat → W → W → Prop) : List Program → W → W → Prop
| [], v, w => v == w
| (α :: δ), v, w => Relation.Comp (Q R α) (Qsteps R δ) v w

@[simp]
theorem Qsteps_single : Qsteps R [α] v w ↔ Q R α v w := by
  simp [Qsteps, Relation.Comp]

theorem Qsteps_append : Qsteps R (δ1 ++ δ2) v w ↔ ∃ u, Qsteps R δ1 v u ∧ Qsteps R δ2 u w := by
  induction δ1 generalizing v w
  case nil =>
    simp [Qsteps]
  case cons α δ IH =>
    simp [Qsteps, Relation.Comp]
    constructor <;> rintro ⟨z, z_in, hyp⟩
    · rw [IH] at hyp
      aesop
    · aesop

/-- Q_Fδ for a list of tests F and a list or programs δ. -/
def Qcombo {W : Finset (Finset Formula)} (R : Nat → W → W → Prop)
    (F : List Formula) (δ : List Program) : W → W → Prop
  := Relation.Comp (Qtests R F) (Qsteps R δ)

/-- Q_Fδ v w implies Q v w. -/
theorem cp3a {W : Finset (Finset Formula)} (R : Nat → W → W → Prop) (α : Program) :
    ∀ Fδ ∈ H α, ∀ v w, Qcombo R Fδ.1 Fδ.2 v w → Q R α v w := by
  rintro ⟨F,δ⟩ in_H v w
  cases α
  case atom_prog =>
    simp_all [Qtests, Qsteps, Qcombo, Relation.Comp, H]
  case test =>
    simp_all [Qtests, Qsteps, Qcombo, Relation.Comp, H]
  case union α β =>
    intro v_combo_w
    simp only [Q]
    simp only [H, List.mem_union_iff] at in_H
    rcases in_H with hyp|hyp
    · left; exact cp3a R α (F, δ) hyp _ _ v_combo_w
    · right; exact cp3a R β (F, δ) hyp _ _ v_combo_w
  case sequence α β =>
    have IHα := cp3a R α
    have IHβ := cp3a R β
    intro v_combo_w
    simp only [H, List.mem_flatten, List.mem_map, Prod.exists] at in_H
    rcases in_H with ⟨L, ⟨F, δ, in_Hα, def_l⟩, in_L⟩
    simp only [Q, Relation.Comp]
    subst def_l
    by_cases δ = []
    · subst_eqs
      simp only [reduceIte, List.mem_flatten, List.mem_map, Prod.exists] at in_L
      rcases in_L with ⟨l, ⟨F', δ', F'δ'_in_Hβ, def_l⟩, in_l⟩
      subst def_l
      simp only [List.mem_singleton, Prod.mk.injEq] at in_l
      cases in_l
      subst_eqs
      simp_all only [Qcombo, Relation.Comp, Qtests, beq_iff_eq, List.mem_union_iff, Qsteps,
        exists_eq_right, and_imp, forall_exists_index]
      rcases v_combo_w with ⟨z, ⟨def_z, F_hyp⟩, z_w⟩
      subst def_z
      use v
      constructor
      · apply IHα _ in_Hα _ _ _ rfl (fun τ _ => by apply F_hyp; tauto)
        simp [Qsteps]
      · apply IHβ _ F'δ'_in_Hβ v w _ rfl (fun τ _ => by apply F_hyp; tauto) z_w
    case neg hyp =>
      simp only [hyp, reduceIte, List.mem_singleton, Prod.mk.injEq] at in_L
      cases in_L
      subst_eqs
      simp only [Qcombo, Relation.Comp, Qtests] at v_combo_w
      rcases v_combo_w with ⟨z, ⟨v_eq_z, F_hyp⟩, z_w⟩
      simp only [beq_iff_eq] at v_eq_z
      subst v_eq_z
      simp only [Q, true_and] at F_hyp
      rw [Qsteps_append] at z_w
      rcases z_w with ⟨u, v_u, u_w⟩
      use u
      constructor
      · apply IHα _ in_Hα
        simp only [Qcombo, Relation.Comp]
        use v
        constructor
        · simp only [Qtests, beq_self_eq_true, Q, true_and]
          intro τ _
          apply F_hyp
          assumption
        · exact v_u
      · rw [Qsteps_single] at u_w
        exact u_w
  case star α =>
    have IHα := cp3a R α
    intro v_combo_w
    simp [H, List.mem_flatten, List.mem_map, Prod.exists] at in_H
    rcases in_H with ⟨F_nil, δ_nil⟩ | ⟨L, ⟨F, δ, in_Hα, def_l⟩, in_L⟩
    · subst_eqs
      simp [Qcombo, Relation.Comp, Qtests, Qsteps] at v_combo_w
      subst v_combo_w
      simp [Q]
      exact Relation.ReflTransGen.refl
    · simp only [Q]
      subst def_l
      by_cases δ = []
      · subst_eqs
        simp only [reduceIte, List.mem_flatten, List.mem_map, Prod.exists] at in_L
        absurd in_L
        exact List.not_mem_nil _
      case neg hyp =>
        simp only [hyp, reduceIte, List.mem_singleton, Prod.mk.injEq] at in_L
        cases in_L
        subst_eqs
        simp only [Qcombo, Relation.Comp, Qtests] at v_combo_w
        rcases v_combo_w with ⟨z, ⟨v_eq_z, F_hyp⟩, z_w⟩
        simp only [beq_iff_eq] at v_eq_z
        subst v_eq_z
        simp only [Q, true_and] at F_hyp
        rw [Qsteps_append] at z_w
        rcases z_w with ⟨u, v_u, u_w⟩
        apply @Relation.ReflTransGen.head _ _ _ u
        · apply IHα _ in_Hα
          simp only [Qcombo, Relation.Comp]
          use v
          constructor
          · simp only [Qtests, beq_self_eq_true, Q, true_and]
            intro τ _
            apply F_hyp
            assumption
          · exact v_u
        · rw [Qsteps_single] at u_w
          exact u_w
