-- MODELGRAPHS

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
    ∧ ((⌈α⌉P) ∈ X → ∃ l ∈ TP α, (Xset α l P).all (fun y => y ∈ X))
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
  cases α_def : α -- TODO: only partially distinguish (atom | star | all other cases)
  all_goals
    intro Y X_rel_Y
  case atom_prog a =>
    subst α_def
    simp only [instBot, relate] at X_rel_Y
    have ⟨_,⟨_,_,iii,_⟩⟩ := MG
    exact iii X Y _ _ X_rel_Y boxP_in_X
  case sequence β γ =>
    have satX := (MG.prop.1 X).left
    simp only [saturated, List.all_eq_true, decide_eq_true_eq, Prod.exists] at satX
    -- use saturatedness to get a testprofile ℓ:
    rcases (satX φ φ α).right.right.right.left boxP_in_X with ⟨ℓ, ℓ_in_TPα, Xset_sub_X⟩
    simp only [Xset, List.mem_append, List.mem_map] at Xset_sub_X
    have X_F : ∀ τ ∈ F (α, ℓ), evaluate MG.val X τ := by
      intro τ τ_in
      -- Now we use IH of C2 on the tests in a
      -- NOTE: for this (in the test case, not sequence) we tweaked `lengthOfProgram (?'φ)` ;-)
      have forTermination : lengthOfFormula τ < lengthOfProgram α := F_goes_down τ_in
      have := loadedTruthLemma MG X τ
      simp_all only [instBot, relate, Subtype.exists, lengthOfProgram, true_or, forall_true_left]
    have := existsBoxFP X_rel_Y (α_def ▸ ℓ_in_TPα) (by simp [modelCanSemImplyForm,conEval]; exact (α_def ▸ X_F))
    rcases this with ⟨δ, δ_in_P, X_δ_Y⟩
    have δφ_in_X : (⌈⌈δ⌉⌉φ) ∈ X.val := by
      simp_all only [instBot, relate, Subtype.exists]
      subst_eqs
      apply Xset_sub_X
      right
      use δ
    -- FIXME: Notes now want to apply IH of C3, but we use C4 for all elements in δ
    have IHδ : ∀ d ∈ δ, ∀ (X' Y' : Worlds), ∀ φ', (⌈d⌉φ') ∈ X'.val → relate MG.val d X' Y' → φ' ∈ Y'.val := by
      intro d d_in_δ X' Y' φ' dφ_in_X' X'_d_Y'
      have forTermination : lengthOf d < lengthOf (β;'γ) := by sorry -- lemma about P needed?
      exact loadedTruthLemmaProg MG d X' φ' dφ_in_X' Y' X'_d_Y'
    -- NOTE: tried `induction δ` before, but seems bad idea, yields too weak/annoying IH
    -- Instead, check if δ is empty, and in non-empty case use `relateSeq_toChain'`.
    cases em (δ = [])
    · simp_all [relateSeq] -- uses δφ_in_X from above.
    case inr δ_notEmpty =>
      have := relateSeq_toChain' X_δ_Y δ_notEmpty
      rcases this with ⟨l, length_def, lchain⟩
      -- Now we prove a claim to combine `lchain` with `IHδ`.
      have loadClaim : ∀ i : Fin (X :: l ++ [Y]).length,
          (⌈⌈δ.drop i⌉⌉φ) ∈ ((X :: l ++ [Y]).get i).val := by
        intro i
        induction i using Fin.inductionOn
        case zero =>
          simp_all -- uses δφ_in_X from above.
        case succ i IH =>
          simp only [List.cons_append, List.length_cons, List.append_eq, Fin.val_succ, List.get_cons_succ']
          have help1 : (List.append l [Y]).length = δ.length := by simp [length_def]
          apply IHδ (δ.get (i.cast help1)) (by apply List.get_mem) (List.get (X :: l ++ [Y]) i.castSucc)
          · have : (⌈List.get δ (i.cast help1)⌉⌈⌈List.drop (i + 1) δ⌉⌉φ) = (⌈⌈List.drop (i.castSucc) δ⌉⌉φ) := by
              simp only [List.append_eq, Fin.coe_castSucc]
              rw [← Formula.boxes]
              have := @List.drop_eq_get_cons _ i δ (by rw [← length_def]; have := Fin.is_lt i; convert this; simp)
              rw [this]
              cases i
              simp_all
            rw [this]
            exact IH
          · simp [relate]
            -- TODO: use lchain here somehow!
            rw [List.chain'_iff_get] at lchain -- hmmm
            sorry
      specialize loadClaim (Fin.last _)
      simp at loadClaim
      rw [length_def] at loadClaim
      simp at loadClaim
      convert loadClaim
      have := @List.get_last _ Y (X :: l) (Fin.last _)
      simp at this
      rw [eq_comm]
      exact this

  case union b c =>
    -- TODO: should be the same as sequence
    sorry

  case star a =>
    -- We now follow MB and do another level of induction over n. -- TODO replace with new way
    have claim : ∀ n (ys : Vector Worlds n.succ),
      (⌈∗a⌉φ) ∈ ys.head.val → (∀ i : Fin n, relate MG.val a (ys.get i.castSucc) (ys.get (i.succ))) → φ ∈ ys.last.val
      := by
      intro n
      induction n -- "inner induction"
      case zero =>
        rintro ys boxP_in_head steprel
        have : ys.last = ys.head := by
          cases ys using Vector.inductionOn
          case h_cons rest _ =>
            cases rest using Vector.inductionOn; simp only [Nat.zero_eq, Vector.head_cons]; rfl
        rw [this]
        have ⟨_,⟨i,_,_,_⟩⟩ := MG
        have := (i ys.head).left
        simp [saturated] at this
        sorry -- exact ((this φ φ a a).right.right.right.right.right.right.left boxP_in_head).left
      case succ m IH =>
        rintro ys boxP_in_head steprel
        let Z := ys.get 1
        have head_a_Z : relate MG.val a ys.head Z := by
          convert (steprel 0)
          simp
        have : (⌈a⌉⌈∗a⌉φ) ∈ ys.head.val := by
          have ⟨_,⟨i,_,_,_⟩⟩ := MG
          have := (i ys.head).left
          simp [saturated] at this
          sorry -- exact ((this φ φ a a).right.right.right.right.right.right.left boxP_in_head).right
        have boxP_in_Z : (⌈∗a⌉φ) ∈ Z.val := loadedTruthLemmaProg MG a ys.head (⌈∗a⌉φ) this Z head_a_Z
        have : ys.last = ys.tail.last := by
          cases ys using Vector.inductionOn
          case h_cons rest _ =>
            cases rest using Vector.inductionOn; simp; rfl
        rw [this]
        apply IH ys.tail
        · convert boxP_in_Z
          cases ys using Vector.inductionOn
          case h_cons _ rest _ _ =>
            cases rest using Vector.inductionOn
            · simp only [Vector.tail_cons, Vector.head_cons]
              rfl
        · intro i
          specialize steprel (i.succ).castSucc
          simp
          simp at steprel
          have : (Fin.succ (Fin.castSucc i)) = (Fin.castSucc (Fin.succ i)) := by
            rfl
          rw [this]
          exact steprel
    simp at X_rel_Y
    rcases ReflTransGen.to_finitelyManySteps X_rel_Y with ⟨n, ys, X_is_head, Y_is_last, steprel⟩
    rw [Y_is_last]
    rw [X_is_head] at boxP_in_X
    exact claim n ys (α_def ▸ boxP_in_X) steprel

  case test R =>
    -- TODO: now to be replaced with same as union and sequence ?!
    have nR_or_P_in_X : (~R) ∈ X.val ∨ φ ∈ X.val := by
      have ⟨_,⟨i,_,_,_⟩⟩ := MG
      have := (i X).left
      simp [saturated] at this
      sorry -- exact (this P R (?'⊤) (?'⊤)).right.right.right.right.right.left boxP_in_X
    simp at X_rel_Y
    rcases X_rel_Y with ⟨X_is_Y, X_R⟩
    subst X_is_Y
    cases nR_or_P_in_X
    case inl nR_in_X =>
      have := loadedTruthLemma MG X R
      have minus_X := this.right
      specialize minus_X nR_in_X
      absurd minus_X
      exact X_R
    case inr P_in_X =>
      exact P_in_X
termination_by
  _ _ _ => lengthOf α

end


-- Lemma 9, page 32
theorem truthLemma {Worlds} (MG : ModelGraph Worlds) :
    ∀ X : Worlds, ∀ P, P ∈ X.val → evaluate MG.val X P :=
  by
  intro X P
  have ⟨claim, _⟩ := loadedTruthLemma MG X P
  exact claim
