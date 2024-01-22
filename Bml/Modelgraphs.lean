-- MODELGRAPHS
import Bml.Syntax
import Bml.Semantics

open Formula

-- Definition 18, page 31
def Saturated : Finset Formula → Prop
  | X =>
    ∀ P Q : Formula, (~~P ∈ X → P ∈ X) ∧ (P⋀Q ∈ X → P ∈ X ∧ Q ∈ X) ∧ (~(P⋀Q) ∈ X → ~P ∈ X ∨ ~Q ∈ X)

-- Definition 19, page 31
@[simp]
def ModelGraph (Worlds : Set (Finset Formula)) :=
  let W := Subtype fun x => x ∈ Worlds
  let i := ∀ X : W, Saturated X.val ∧ ⊥ ∉ X.val ∧ ∀ P, P ∈ X.val → ~P ∉ X.val
  let ii := fun M : KripkeModel W => ∀ (X : W) (pp), (·pp) ∈ X.val ↔ M.val X pp
  let iii :=-- Note: Borzechowski only has → in ii. We follow BRV, Def 4.18 and 4.84.
  fun M : KripkeModel W => ∀ (X Y : W) (P), M.Rel X Y → □P ∈ X.val → P ∈ Y.val
  let iv := fun M : KripkeModel W => ∀ (X : W) (P), ~(□P) ∈ X.val → ∃ Y, M.Rel X Y ∧ ~P ∈ Y.val
  Subtype fun M : KripkeModel W => i ∧ ii M ∧ iii M ∧ iv M

-- Lemma 9, page 32
theorem truthLemma {Worlds : Set (Finset Formula)} (MG : ModelGraph Worlds) :
    ∀ X : Worlds, ∀ P, P ∈ X.val → Evaluate (MG.val, X) P :=
  by
  intro X P
  cases' MG with M M_prop
  rcases M_prop with ⟨i, ii, iii, iv⟩
  -- induction loading!!
  let plus P (X : Worlds) := P ∈ X.val → Evaluate (M, X) P
  let minus P (X : Worlds) := ~P ∈ X.val → ¬Evaluate (M, X) P
  let oh P (X : Worlds) := □P ∈ X.val → ∀ Y, M.Rel X Y → P ∈ Y.val
  have claim : ∀ P X, plus P X ∧ minus P X ∧ oh P X :=
    by
    intro P
    induction P; all_goals intro X
    case bottom =>
      specialize i X
      rcases i with ⟨_, bot_not_in_X, _⟩
      repeat' constructor
      · intro P_in_X; apply absurd P_in_X bot_not_in_X
      · tauto
      · intro boxBot_in_X Y X_rel_Y; exact iii X Y ⊥ X_rel_Y boxBot_in_X
    case atom_prop pp =>
      repeat' constructor
      · intro P_in_X; unfold Evaluate; rw [ii X pp] at P_in_X ; exact P_in_X
      · intro notP_in_X; unfold Evaluate; rw [← ii X pp]
        rcases i X with ⟨_, _, P_in_then_notP_not_in⟩
        specialize P_in_then_notP_not_in (·pp); tauto
      · intro boxPp_in_X Y X_rel_Y; exact iii X Y (·pp) X_rel_Y boxPp_in_X
    case neg P IH =>
      rcases IH X with ⟨plus_IH, minus_IH, _⟩
      repeat' constructor
      · intro notP_in_X; unfold Evaluate
        exact minus_IH notP_in_X
      · intro notnotP_in_X
        rcases i X with ⟨X_saturated, _, _⟩
        cases' X_saturated P ⊥ with doubleNeg
        -- ⊥ is unused!
        unfold Evaluate;
        simp
        exact plus_IH (doubleNeg notnotP_in_X)
      · intro notPp_in_X Y X_rel_Y; exact iii X Y (~P) X_rel_Y notPp_in_X
    case And P Q IH_P IH_Q =>
      rcases IH_P X with ⟨plus_IH_P, minus_IH_P, _⟩
      rcases IH_Q X with ⟨plus_IH_Q, minus_IH_Q, _⟩
      rcases i X with ⟨X_saturated, _, _⟩
      unfold Saturated at X_saturated
      rcases X_saturated P Q with ⟨_, andSplit, notAndSplit⟩
      repeat' constructor
      · intro PandQ_in_X
        specialize andSplit PandQ_in_X; cases' andSplit with P_in_X Q_in_X
        unfold Evaluate
        constructor
        · exact plus_IH_P P_in_X
        · exact plus_IH_Q Q_in_X
      · intro notPandQ_in_X
        unfold Evaluate; rw [not_and_or]
        specialize notAndSplit notPandQ_in_X
        cases' notAndSplit with notP_in_X notQ_in_X
        · left; exact minus_IH_P notP_in_X
        · right; exact minus_IH_Q notQ_in_X
      · intro PandQ_in_X Y X_rel_Y; exact iii X Y (P⋀Q) X_rel_Y PandQ_in_X
    case box P IH =>
      repeat' constructor
      · intro boxP_in_X; unfold Evaluate
        intro Y X_rel_Y
        rcases IH Y with ⟨plus_IH_Y, _, _⟩
        apply plus_IH_Y
        rcases IH X with ⟨_, _, oh_IH_X⟩
        exact oh_IH_X boxP_in_X Y X_rel_Y
      · intro notBoxP_in_X; unfold Evaluate
        push_neg
        rcases iv X P notBoxP_in_X with ⟨Y, X_rel_Y, notP_in_Y⟩
        use Y; constructor; exact X_rel_Y
        rcases IH Y with ⟨_, minus_IH_Y, _⟩
        exact minus_IH_Y notP_in_Y
      · intro boxBoxP_in_X Y X_rel_Y; exact iii X Y (□P) X_rel_Y boxBoxP_in_X
  apply (claim P X).left
