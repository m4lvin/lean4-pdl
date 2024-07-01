-- MODELGRAPHS
import Mathlib.Tactic.ClearExcept
import Mathlib.Data.Vector.Basic

import Pdl.Semantics
import Pdl.Star
import Pdl.Unfold

open Formula

open HasLength

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

-- TODO: it seems default 200000 is not enough for mutual theorems below?!
set_option maxHeartbeats 2000000
-- set_option trace.profiler true

theorem get_eq_getzip {X Y : α} {i : Fin ((List.length (l ++ [Y])))} {h} :
  List.get (X :: (l ++ [Y])) (Fin.castSucc i) = (List.get ((x, X) :: List.zip δ (l ++ [Y])) ⟨i.val, h⟩).2 := by
  -- special thanks to droplet739
  simp only [←List.zip_cons_cons]
  rw [List.get_zip]
  rfl

theorem loadClaimHelper {Worlds : Finset (Finset Formula)}
    {MG : ModelGraph Worlds}
    {X Y : { x // x ∈ Worlds }}
    {δ : List Program}
    {φ : Formula}
    {l: List { x // x ∈ Worlds }}
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
        rw [← Formula.boxes]
        have := @List.drop_eq_get_cons _ i δ (by rw [← length_def]; have := Fin.is_lt i; convert this; simp)
        rw [this]
        cases i
        simp_all only [instBot, insTop, List.zip_cons_cons, Subtype.forall, List.append_eq,
          Fin.castSucc_mk, boxes, Fin.cast_mk]
      rw [this]
      exact IH
    · simp [relate]
      -- It now remains to make lchain usable
      rw [List.chain'_iff_get] at lchain
      specialize lchain i ?_
      · rcases i with ⟨val, hyp⟩
        simp_all only [insTop, List.zip_cons_cons, List.length_cons, List.length_zip,
          List.length_append, List.length_singleton, min_self, Nat.succ_eq_add_one,
          add_tsub_cancel_right, instBot, List.get_cons_succ, List.get_zip, Subtype.forall,
          List.append_eq, Fin.castSucc_mk]
        rw [← length_def]
        simp at hyp
        exact hyp
      simp only [pairRel, instBot, insTop, List.cons_append, List.zip_cons_cons, List.length_cons, List.append_eq, List.get_cons_succ, List.get_zip] at lchain
      convert lchain
      · rw [← length_def]
        simp only [List.length_append, List.length_singleton]
      · simp only [Fin.cast, List.append_eq]
        rcases i with ⟨val, hyp⟩
        rw [Fin.heq_ext_iff]
        rw [← length_def]
        simp only [List.append_eq, List.length_append, List.length_singleton]
      · apply get_eq_getzip

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
        have := Vector.exists_eq_cons YS
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
        unfold_let Z
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
        apply mysat; left; simp [F]; assumption
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
        · unfold_let Z
          rw [← Vector.get_zero]
          rw [Vector.get_tail_succ]
          aesop
        · unfold_let Z
          rw [Vector.last_def]
          rw [Vector.get_tail_succ]
          aesop
        · intro i
          clear * -relSteps
          specialize relSteps i.succ
          have : ((Vector.tail YS).get i.castSucc) = (YS.get ((Fin.succ i).castSucc)) := by aesop
          rw [this]; clear this
          have : ((Vector.tail YS).get i.succ) = (YS.get ((Fin.succ i).succ)) := by aesop
          rw [this]; clear this
          exact relSteps
      case inr δ_notEmpty =>
        have : (δ ++ [∗β]) ∈ P (∗β) ℓ := by
          simp [P]
          apply List.mem_filter_of_mem
          all_goals simp_all
        have δβSφ_in_X : (⌈⌈δ⌉⌉⌈∗β⌉φ) ∈ X.1 := by
          apply mysat
          right
          use δ ++ [∗β]
          simp_all [boxes_append]
        have : (⌈∗β⌉φ) ∈ Z.1 := by
          clear innerIH
          -- Now we apply IH of C4 loadedTruthLemmaProg to all elements in δ
          have IHδ : ∀ d ∈ δ, ∀ (X' Y' : Worlds),
              ∀ φ', (⌈d⌉φ') ∈ X'.val → relate MG.val d X' Y' → φ' ∈ Y'.val := by
            intro d d_in_δ X' Y' φ' dφ_in_X' X'_d_Y'
            have _forTermination : lengthOf d < lengthOf (∗β) := by
              have := P_goes_down d_in_δ δ_in_P
              cases em (isAtomic β) <;> cases em (isStar β)
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
            simp_all [eq_comm]
          intro i
          exact loadClaimHelper length_def δβSφ_in_X lchain IHδ i
        -- lastly, apply innerIH on Z and Y:
        apply innerIH Z _ this
        clear innerIH
        simp_all
        refine ⟨YS.tail, ?_, ?_, ?_⟩
        · unfold_let Z
          rw [← Vector.get_zero]
          rw [Vector.get_tail_succ]
          rfl
        · unfold_let Z
          rw [Vector.last_def, Vector.last_def]
          rw [Vector.get_tail_succ]
          rfl
        · intro i
          clear * -relSteps
          specialize relSteps i.succ
          have : ((Vector.tail YS).get i.castSucc) = (YS.get i.succ.castSucc) := by aesop
          rw [this]; clear this
          have : ((Vector.tail YS).get i.succ) = (YS.get i.succ.succ) := by aesop
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
        simp_all [isAtomic, isStar]
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
        simp_all [eq_comm]
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
