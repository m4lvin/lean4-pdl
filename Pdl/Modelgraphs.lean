-- MODELGRAPHS
import Pdl.Syntax
import Pdl.Semantics

open Formula

-- Definition 18, page 31
def Saturated : Finset Formula → Prop
  | X => ∀ (P Q : Formula) (a b : Program),
    -- propositional closure:
      ((~~P) ∈ X → P ∈ X)
    ∧ (P⋀Q ∈ X → P ∈ X ∧ Q ∈ X)
    ∧ ((~(P⋀Q)) ∈ X → (~P) ∈ X ∨ (~Q) ∈ X)
    -- programs closure:
    ∧ ((⌈a;'b⌉P) ∈ X → (⌈a⌉⌈b⌉P) ∈ X)
    ∧ ((⌈a⋓b⌉P) ∈ X → (⌈a⌉P) ∈ X ∧ (⌈b⌉P) ∈ X)
    ∧ ((⌈?'Q⌉P) ∈ X → ¬Q ∈ X ∨ P ∈ X)
    ∧ ((⌈∗a⌉P) ∈ X → P ∈ X ∧ (⌈a⌉⌈∗a⌉P) ∈ X)
    ∧ ((~⌈a;'b⌉P) ∈ X → (~⌈a⌉⌈b⌉P) ∈ X)
    ∧ ((~⌈a⋓b⌉P) ∈ X  → (~⌈a⌉P) ∈ X ∨ (~⌈b⌉P) ∈ X)
    ∧ ((~⌈?'Q⌉P) ∈ X → Q ∈ X ∧ (~P) ∈ X)
    ∧ ((~⌈∗a⌉P) ∈ X → (~P) ∈ X ∨ (~⌈a⌉⌈∗a⌉P) ∈ X)

-- Definition 19, page 31
def ModelGraph (W : Finset (Finset Formula)) :=
  let i := ∀ X : W, Saturated X.val ∧ ⊥ ∉ X.val ∧ ∀ P, P ∈ X.val → (~P) ∉ X.val
  let ii M := ∀ X p, (·p : Formula) ∈ X.val ↔ M.val X p
  -- Note: Borzechowski only has → in ii. We follow BRV, Def 4.18 and 4.84.
  let iii M := ∀ X Y A P, M.Rel A X Y → (⌈·A⌉P) ∈ X.val → P ∈ Y.val
  let iv M := ∀ X a P, (~⌈a⌉P) ∈ X.val → ∃ Y, relate M a X Y ∧ (~P) ∈ Y.val
  -- Note: In iii the A is atomic, but in iv the a is any program!
  Subtype fun M : KripkeModel W => i ∧ ii M ∧ iii M ∧ iv M

-- Lemma 9, page 32, stronger version for induction loading.
theorem loadedTruthLemma {Worlds} (MG : ModelGraph Worlds) X:
    ∀ P,     (P ∈ X.val → evaluate MG.val X P) -- (+)
        ∧ ((~P) ∈ X.val → ¬evaluate MG.val X P) -- (-)
        ∧ ∀ a, ((⌈a⌉P) ∈ X.val → (∀ (Y : Worlds), relate MG.val a X Y → P ∈ Y.val)) -- (0)
    :=
  by
  intro P
  cases P -- no "induction", use recursive calls!
  case bottom =>
    repeat' constructor
    · intro P_in_X
      apply absurd P_in_X
      have ⟨M,⟨i,_,_,_⟩⟩ := MG
      specialize i X
      tauto
    · simp
    · intro a
      simp
      intro boxBot_in_X Y Y_in X_rel_Y
      have ⟨M,⟨_,_,iii,_⟩⟩ := MG
      sorry -- exact iii X Y _ _ _ boxBot_in_X
      -- TODO cases a
  case atom_prop pp =>
    have ⟨M,⟨i,ii,_,_⟩⟩ := MG
    repeat' constructor
    · intro P_in_X
      simp
      rw [ii X pp] at P_in_X
      exact P_in_X
    · intro notP_in_X
      simp
      rw [← ii X pp]
      rcases i X with ⟨_, _, P_in_then_notP_not_in⟩
      specialize P_in_then_notP_not_in (·pp)
      tauto
    · intro boxPp_in_X Y X_rel_Y
      sorry -- exact iii X Y A (·pp) X_rel_Y boxPp_in_X
  case neg Q =>
    have ⟨plus,minus,oh⟩ := loadedTruthLemma MG X Q
    repeat' constructor
    · intro notQ_in_X
      simp
      exact minus notQ_in_X
    · intro notnotQ_in_X
      simp
      have ⟨M,⟨i,_,_,_⟩⟩ := MG
      rcases i X with ⟨X_saturated, _, _⟩
      exact plus ((X_saturated Q Q (?'Q) (?'Q)).left notnotQ_in_X)
    · intro notQ_in_X Y X_rel_Y
      have ⟨M,⟨_,_,iii,_⟩⟩ := MG
      sorry -- exact iii X Y A (~Q) X_rel_Y notQ_in_X
  case and Q R =>
    have ⟨plus_Q, minus_Q, oh_Q⟩ := loadedTruthLemma MG X Q
    have ⟨plus_R, minus_R, oh_R⟩ := loadedTruthLemma MG X R
    have ⟨M,⟨i,_,iii,_⟩⟩ := MG
    rcases i X with ⟨X_saturated, _, _⟩
    unfold Saturated at X_saturated
    rcases X_saturated Q R (?'Q) (?'Q) with ⟨_, ⟨andSplit, ⟨notAndSplit, _⟩⟩⟩
    repeat' constructor
    · intro QandR_in_X
      specialize andSplit QandR_in_X
      cases' andSplit with Q_in_X R_in_X
      simp
      constructor
      · exact plus_Q Q_in_X
      · exact plus_R R_in_X
    · intro notQandR_in_X
      unfold evaluate; rw [not_and_or]
      specialize notAndSplit notQandR_in_X
      cases' notAndSplit with notQ_in_X notR_in_X
      · left; exact minus_Q notQ_in_X
      · right; exact minus_R notR_in_X
    · intro QandR_in_X Y X_rel_Y
      sorry -- exact iii X Y A (Q⋀R) X_rel_Y QandR_in_X
  case box a P =>
    repeat' constructor
    all_goals simp
    · intro boxP_in_X
      intro Y Y_in X_rel_Y
      have ⟨plus_Y, _, _⟩ := loadedTruthLemma MG ⟨Y, Y_in⟩ P
      have ⟨_, _, oh_X⟩ := loadedTruthLemma MG X P
      apply plus_Y
      apply oh_X a boxP_in_X ⟨Y,Y_in⟩ X_rel_Y
    · intro notBoxP_in_X
      have ⟨M,⟨i,ii,iii,iv⟩⟩ := MG
      cases a
      case atom_prog A =>
        rcases iv X (·A) P notBoxP_in_X with ⟨Y, X_rel_Y, notP_in_Y⟩
        have ⟨_, minus_Y, _⟩ := loadedTruthLemma ⟨M,⟨i,ii,iii,iv⟩⟩ Y P
        use Y
        simp
        constructor
        simp at X_rel_Y
        exact X_rel_Y
        exact minus_Y notP_in_Y
      all_goals sorry
    · intro b boxBoxP_in_X Y y_in X_rel_Y
      have ⟨M,⟨_, _, iii, _⟩⟩ := MG
      sorry -- exact iii X Y b (⌈a⌉P) X_rel_Y boxBoxP_in_X

-- Lemma 9, page 32
theorem truthLemma {Worlds} (MG : ModelGraph Worlds) :
    ∀ X : Worlds, ∀ P, P ∈ X.val → evaluate MG.val X P :=
  by
  intro X P
  have := loadedTruthLemma MG X P
  tauto
