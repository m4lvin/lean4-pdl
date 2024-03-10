-- MODELGRAPHS

import Pdl.Semantics
import Pdl.Star

open Formula

open HasLength

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
    ∧ ((⌈?'Q⌉P) ∈ X → (~Q) ∈ X ∨ P ∈ X)
    ∧ ((⌈∗a⌉P) ∈ X → P ∈ X ∧ (⌈a⌉⌈∗a⌉P) ∈ X)
    ∧ ((~⌈a;'b⌉P) ∈ X → (~⌈a⌉⌈b⌉P) ∈ X)
    ∧ ((~⌈a⋓b⌉P) ∈ X  → (~⌈a⌉P) ∈ X ∨ (~⌈b⌉P) ∈ X)
    ∧ ((~⌈?'Q⌉P) ∈ X → Q ∈ X ∧ (~P) ∈ X)
    ∧ ((~⌈∗a⌉P) ∈ X → (~P) ∈ X ∨ (~⌈a⌉⌈∗a⌉P) ∈ X)

-- Definition 19, page 31
def ModelGraph (W : Finset (Finset Formula)) :=
  let i := ∀ X : W, Saturated X.val ∧ ⊥ ∉ X.val ∧ ∀ (pp : Char), (·pp : Formula) ∈ X.val → (~(·pp)) ∉ X.val
  let ii M := ∀ X p, (·p : Formula) ∈ X.val ↔ M.val X p
  -- Note: Borzechowski only has → in ii. We follow BRV, Def 4.18 and 4.84.
  let iii M := ∀ X Y A P, M.Rel A X Y → (⌈·A⌉P) ∈ X.val → P ∈ Y.val
  let iv M := ∀ X a P, (~⌈a⌉P) ∈ X.val → ∃ Y, relate M a X Y ∧ (~P) ∈ Y.val
  -- Note: In iii the A is atomic, but in iv the a is any program!
  Subtype fun M : KripkeModel W => i ∧ ii M ∧ iii M ∧ iv M

-- Lemma 9, page 32, stronger version for induction loading.
mutual

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
    · simp
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
      specialize P_in_then_notP_not_in pp
      tauto
  case neg Q =>
    have ⟨plus,minus⟩ := loadedTruthLemma MG X Q
    repeat' constructor
    · intro notQ_in_X
      simp
      exact minus notQ_in_X
    · intro notnotQ_in_X
      simp
      have ⟨M,⟨i,_,_,_⟩⟩ := MG
      rcases i X with ⟨X_saturated, _, _⟩
      exact plus ((X_saturated Q Q (?'Q) (?'Q)).left notnotQ_in_X)
  case and Q R =>
    have ⟨plus_Q, minus_Q⟩ := loadedTruthLemma MG X Q
    have ⟨plus_R, minus_R⟩ := loadedTruthLemma MG X R
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
      · exact X_a_Y
      · have ⟨_, minus_Y⟩ := loadedTruthLemma ⟨M,⟨i,ii,iii,iv⟩⟩ ⟨Y, Y_in⟩ P
        simp at minus_Y
        specialize minus_Y nP_in_Y
        convert minus_Y
termination_by
  f => lengthOf f

theorem loadedTruthLemmaProg {Worlds} (MG : ModelGraph Worlds) a :
    ∀ X P, ((⌈a⌉P) ∈ X.val → (∀ (Y : Worlds), relate MG.val a X Y → P ∈ Y.val)) -- (0)
    :=
  by -- todo: unindent all
  intro X P boxP_in_X
  cases a
  all_goals (intro Y X_rel_Y; simp at X_rel_Y)
  case atom_prog A =>
    have ⟨_,⟨_,_,iii,_⟩⟩ := MG
    exact iii X Y _ _ X_rel_Y boxP_in_X
  case sequence b c =>
    have bcP_in_X : (⌈b⌉⌈c⌉P) ∈ X.val := by
      have ⟨_,⟨i,_,_,_⟩⟩ := MG
      have := (i X).left
      simp [Saturated] at this
      exact (this P P b c).right.right.right.left boxP_in_X
    rcases X_rel_Y with ⟨Z, Z_in, X_b_Z, Z_c_Y⟩
    have cP_in_Z := (loadedTruthLemmaProg MG b X) (⌈c⌉P) bcP_in_X ⟨Z,Z_in⟩ X_b_Z
    have : lengthOf c < lengthOf (b;'c) := by simp
    exact (loadedTruthLemmaProg MG c ⟨Z, Z_in⟩) P cP_in_Z Y Z_c_Y
  case union b c =>
    have bP_and_cP_in_X : (⌈b⌉P) ∈ X.val ∧ (⌈c⌉P) ∈ X.val := by
      have ⟨_,⟨i,_,_,_⟩⟩ := MG
      have := (i X).left
      simp [Saturated] at this
      exact (this P P b c).right.right.right.right.left boxP_in_X
    cases X_rel_Y
    case inl X_b_Y =>
      exact (loadedTruthLemmaProg MG b X) P bP_and_cP_in_X.left Y X_b_Y
    case inr X_c_Y =>
      have : lengthOf c < lengthOf (b⋓c) := by simp
      exact (loadedTruthLemmaProg MG c X) P bP_and_cP_in_X.right Y X_c_Y
  case star a =>
    -- We now follow MB and do another level of induction over n.
    have claim : ∀ n (ys : Vector Worlds n.succ),
      (⌈∗a⌉P) ∈ ys.head.val → (∀ i : Fin n, relate MG.val a (ys.get i.castSucc) (ys.get (i.succ))) → P ∈ ys.last.val
      := by
      intro n
      induction n
      case zero =>
        rintro ys boxP_in_head steprel
        have : ys.last = ys.head := by
          cases ys using Vector.inductionOn
          case h_cons rest _ =>
            cases rest using Vector.inductionOn; simp only [Nat.zero_eq, Vector.head_cons]; rfl
        rw [this]
        have ⟨_,⟨i,_,_,_⟩⟩ := MG
        have := (i ys.head).left
        simp [Saturated] at this
        exact ((this P P a a).right.right.right.right.right.right.left boxP_in_head).left
      case succ m IH =>
        rintro ys boxP_in_head steprel
        let Z := ys.get 1
        have head_a_Z : relate MG.val a ys.head Z := by
          convert (steprel 0)
          simp
        have : (⌈a⌉⌈∗a⌉P) ∈ ys.head.val := by
          have ⟨_,⟨i,_,_,_⟩⟩ := MG
          have := (i ys.head).left
          simp [Saturated] at this
          exact ((this P P a a).right.right.right.right.right.right.left boxP_in_head).right
        have boxP_in_Z : (⌈∗a⌉P) ∈ Z.val := loadedTruthLemmaProg MG a ys.head (⌈∗a⌉P) this Z head_a_Z
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
    rcases starIsFinitelyManySteps _ X Y X_rel_Y with ⟨n, ys, X_is_head, Y_is_last, steprel⟩
    rw [Y_is_last]
    rw [X_is_head] at boxP_in_X
    exact claim n ys boxP_in_X steprel
  case test R =>
    have nR_or_P_in_X : (~R) ∈ X.val ∨ P ∈ X.val := by
      have ⟨_,⟨i,_,_,_⟩⟩ := MG
      have := (i X).left
      simp [Saturated] at this
      exact (this P R (?'⊤) (?'⊤)).right.right.right.right.right.left boxP_in_X
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
  _ _ _ => lengthOf a

end


-- Lemma 9, page 32
theorem truthLemma {Worlds} (MG : ModelGraph Worlds) :
    ∀ X : Worlds, ∀ P, P ∈ X.val → evaluate MG.val X P :=
  by
  intro X P
  have ⟨claim, _⟩ := loadedTruthLemma MG X P
  exact claim
