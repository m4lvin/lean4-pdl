import Pdl.Syntax
import Pdl.Semantics
import Pdl.Discon
import Pdl.Unravel

-- NOTE: Much here should be replaced with extended versions of
-- https://github.com/m4lvin/tablean/blob/main/src/tableau.lean
-- but maybe we should mathport that project to Lean 4 first?

-- LOCAL TABLEAU

-- TODO: Can we use variables below without making them arguments of localRule?
-- variable (X : Finset Formula) (f g : Formula) (a b : Program)

@[simp]
def listsToSets : List (List Formula) → Finset (Finset Formula)
| LS => (LS.map List.toFinset).toFinset

-- Local rules: given this set, we get these sets as child nodes
inductive localRule : Finset Formula → Finset (Finset Formula) → Type
  -- PROP LOGIC
  -- closing rules:
  | bot {X    } (h : (⊥ : Formula) ∈ X) : localRule X ∅
  | not {X φ  } (h : φ ∈ X ∧ (~φ) ∈ X) : localRule X ∅
  -- one-child rules:
  | neg {X φ  } (h : (~~φ)      ∈ X) : localRule X { X \ {~~φ}    ∪ {φ}   }
  | con {X φ ψ} (h : φ ⋀ ψ      ∈ X) : localRule X { X \ {φ⋀ψ}    ∪ {φ,ψ} }
  -- splitting rule:
  | nCo {X φ ψ} (h : (~(φ ⋀ ψ)) ∈ X) : localRule X { X \ {~(φ⋀ψ)} ∪ {~φ}
                                                   , X \ {~(φ⋀ψ)} ∪ {~ψ}  }
  -- PROGRAMS
  -- Single-branch rules:
  | nTe {X φ ψ} (h : (~⌈✓φ⌉ψ) ∈ X) : localRule X { X \ {~⌈✓φ⌉ψ} ∪ {φ, ~ψ}} -- TODO should remove marking ?
  | nSe {X a b f} (h : (~⌈a;b⌉f) ∈ X) : localRule X { X \ {~⌈a;b⌉f} ∪ {~⌈a⌉⌈b⌉f}}
  | uni {X a b f} (h : (⌈a⋓b⌉f) ∈ X) : localRule X { X \ {⌈a⋓b⌉f} ∪ {⌈a⌉ f, ⌈b⌉ f}}
  | seq {X a b f} (h : (⌈a;b⌉f) ∈ X) : localRule X { X \ {⌈a⌉⌈b⌉f}}
  -- Splitting rules:
  | tes {X f g} (h : (⌈✓f⌉g) ∈ X) : localRule X { X \ {⌈✓f⌉g} ∪ {~f}
                                                 , X \ {⌈✓f⌉g} ∪ {g} }
  | nUn {a b f} (h : (~⌈a ⋓ b⌉f) ∈ X) : localRule X { X \ {~⌈a ⋓ b⌉f} ∪ {~⌈a⌉f}
                                                    , X \ {~⌈a ⋓ b⌉f} ∪ {~⌈b⌉f} }
  -- STAR
  | sta {X a f} (h : (⌈∗a⌉f) ∈ X) : localRule X ({ X \ {⌈∗a⌉f} } ⊎ (listsToSets (unravel (inject (⌈∗a⌉f)))))
  | nSt {a f} (h : (~⌈∗a⌉f) ∈ X) : localRule X ({ X \ {~⌈∗a⌉f} } ⊎ (listsToSets (unravel (inject (~⌈∗a⌉f)))))

  -- TODO which rules need and modify markings?
  -- TODO only apply * if there is a marking.

-- Like Lemma 5 of MB
lemma localRuleTruth {W} {M : KripkeModel W} {w : W} {X B} :
  localRule X B → ((∃ Y ∈ B, (M,w) ⊨ Y) ↔ (M,w) ⊨ X) :=
  by
  intro locR
  cases locR
  all_goals try simp only [Finset.mem_singleton, Finset.union_insert, Finset.mem_union, Finset.mem_sdiff, Finset.not_mem_empty]
  -- PROPOSITIONAL LOGIC
  case bot bot_in_a =>
    constructor
    · intro ⟨Y,Y_in,w_Y⟩; simp at Y_in
    · intro w_sat_a
      by_contra
      let w_sat_bot := w_sat_a ⊥ bot_in_a
      simp at w_sat_bot
  case not f hyp =>
    constructor
    · sorry
    · intro w_sat_a
      by_contra
      have w_sat_f : evaluate M w f := by
        apply w_sat_a
        exact hyp.left
      have w_sat_not_f : evaluate M w (~f) :=
        by
        apply w_sat_a (~f)
        exact hyp.right
      simp at *
      exact absurd w_sat_f w_sat_not_f
  case neg f hyp =>
    constructor
    · sorry
    · intro w_sat_a
      have w_sat_f : evaluate M w f :=
        by
        specialize w_sat_a (~~f) hyp
        aesop
      use X \ {~~f} ∪ {f}
      simp
      intro g
      simp
      intro g_in
      cases g_in
      case inl hyp =>
        apply w_sat_a
        exact hyp.left
      case inr g_is_f => subst g_is_f; exact w_sat_f
  case con f g hyp =>
    constructor
    · sorry
    · intro w_sat_a
      use X \ {f⋀g} ∪ {f, g}
      simp
      intro h
      simp
      intro h_in
      cases h_in
      case inl h_is_f =>
        rw [h_is_f]
        specialize w_sat_a (f⋀g) hyp
        simp at *
        exact w_sat_a.left
      case inr whatever =>
        cases whatever
        case inr h_is_g =>
          rw [h_is_g]
          specialize w_sat_a (f⋀g) hyp
          simp at *
          exact w_sat_a.right
        case inl h_in_X =>
          exact w_sat_a h h_in_X.left
  case nCo f g notfandg_in_a =>
    constructor
    · sorry
    · intro w_sat_a
      let w_sat_phi := w_sat_a (~(f⋀g)) notfandg_in_a
      simp at w_sat_phi
      rw [imp_iff_not_or] at w_sat_phi
      cases' w_sat_phi with not_w_f not_w_g
      · use X \ {~(f⋀g)} ∪ {~f}
        simp
        intro h h_in
        simp at h_in
        cases h_in
        case inl h_in_X =>
          apply w_sat_a
          exact h_in_X.left
        case inr h_is_notf =>
          rw [h_is_notf]
          simp
          exact not_w_f
      · use X \ {~(f⋀g)} ∪ {~g}
        simp
        intro h h_in
        simp at h_in
        cases h_in
        case inl h_in_X =>
          apply w_sat_a
          exact h_in_X.left
        case inr h_is_notf =>
          rw [h_is_notf]
          simp
          exact not_w_g
  -- STAR RULES
  case nSt a f aSf_in_X =>
    constructor
    · rintro ⟨Y, Y_in, MwY⟩ -- invertibility
      simp at Y_in
      rcases Y_in with ⟨FS,FS_in,Y_def⟩
      subst Y_def
      intro g g_in_X
      -- TODO distinguish cases whether g = ~[∗]f
      cases FS_in
      case inl FS_is_nF =>
        sorry
      case inr FS_in_unrav =>
        sorry
    · intro Mw_X -- soundness
      have w_adiamond_f := Mw_X (~⌈∗a⌉f) aSf_in_X
      simp at w_adiamond_f
      rcases w_adiamond_f with ⟨v, w_aS_v, v_nF⟩
      -- NOTE: Borze also makes a distinction whether a is atomic. Not needed?
      -- We still distinguish cases whether v = w
      have : w = v ∨ w ≠ v := by tauto
      cases this
      case inl w_is_v =>
        -- Same world, we can use the left branch.
        subst w_is_v
        use (X \ {~⌈∗a⌉f} ∪ {~f})
        constructor
        · apply union_elem_uplus
          simp
          unfold unravel
          simp
          use {~f}
          constructor
          · left
            exact List.mem_of_mem_head? rfl
          · rfl
        · intro g g_in
          simp at g_in
          cases g_in
          · tauto
          case h.right.inr hyp =>
            subst hyp
            unfold evaluate
            assumption
      case inr w_neq_v =>
        -- Different world, we use the right branch and Lemma 4 here:
        have lemFour := likeLemmaFour M (∗ a)
        specialize lemFour w v X.toList (inject f) w_neq_v
        unfold vDash.SemImplies modelCanSemImplyForm modelCanSemImplyList at lemFour -- mwah, why simp not do this?
        simp at lemFour
        specialize lemFour _ w_aS_v v_nF
        · intro g g_in
          apply Mw_X
          cases g_in
          case a.inl => assumption
          case a.inr h =>
            convert aSf_in_X
        rcases lemFour with ⟨Z, Z_in, Mw_ZX, ⟨as, nBasf_in, w_as_v⟩⟩
        use (X \ {~⌈∗a⌉f}) ∪ Z.toFinset
        constructor
        · apply union_elem_uplus
          · simp
          · simp
            use Z
        · intro g g_in
          apply Mw_ZX
          simp at g_in
          tauto
  case sta =>  -- TODO
    have := lemmaFourAndThreeQuarters M -- use here
    sorry

  -- OTHER PDL RULES
  case nTe φ ψ in_X =>
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      cases Classical.em (f = (~⌈✓φ⌉ψ))
      case inl f_def =>
        subst f_def
        simp
        constructor
        · apply w_Y
          simp
        · specialize w_Y (~ψ)
          simp at w_Y
          exact w_Y
      case inr f_not =>
        apply w_Y
        simp
        tauto
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      rcases f_in with f_is_phi | ⟨f_in_X, not_f⟩ | f_is_notPsi
      · subst f_is_phi
        specialize w_X _ in_X
        simp at w_X
        tauto
      · exact w_X _ f_in_X
      · subst f_is_notPsi
        specialize w_X _ in_X
        simp at *
        tauto
  case nSe => -- {X a b f} (h : (~⌈a;b⌉f) ∈ X) : localRule X { X \ {~⌈a;b⌉f} ∪ {~⌈a⌉⌈b⌉f}}
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      sorry
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      sorry
  case uni => -- {X a b f} (h : (⌈a⋓b⌉f) ∈ X) : localRule X { X \ {⌈a⋓b⌉f} ∪ {⌈a⌉ f, ⌈b⌉ f}}
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      sorry
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      sorry
  case seq => -- {X a b f} (h : (⌈a;b⌉f) ∈ X) : localRule X { X \ {⌈a⌉⌈b⌉f}}
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      subst Y_in
      intro f f_inX
      sorry
    · intro w_X
      simp
      intro f f_in
      simp at f_in
      sorry
  -- Splitting rules:
  case tes => -- {X f g} (h : (⌈✓f⌉g) ∈ X) : localRule X { X \ {⌈✓f⌉g} ∪ {~f} , X \ {⌈✓f⌉g} ∪ {g} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      simp at Y_in
      intro f f_inX
      cases Y_in
      · sorry
      · sorry
    · intro w_X
      simp
      -- split TODO!
      sorry
  case nUn => -- {a b f} (h : (~⌈a ⋓ b⌉f) ∈ X) : localRule X { X \ {~⌈a ⋓ b⌉f} ∪ {~⌈a⌉f}, X \ {~⌈a ⋓ b⌉f} ∪ {~⌈b⌉f} }
    constructor
    · rintro ⟨Y, Y_in, w_Y⟩
      simp at Y_in
      intro f f_inX
      cases Y_in
      · sorry
      · sorry
    · intro w_X
      simp
      -- split TODO
      sorry


-- TODO inductive LocalTableau


-- TABLEAUX

inductive Tableau -- to be rewritten as in tablean?
  | leaf : Set Formula → Tableau
  | Rule : Rule → List (Set Formula) → Tableau

def projection : Char → Formula → Option Formula
  | a, ⌈·b⌉ f => if a = b then some f else none
  | _, _ => none

-- TODO inductive globalRule : ...
--  | nSt {a f} (h : (~⌈·a⌉f) ∈ X) : localRule X { X \ {~⌈·a⌉f} ∪ {~f} } -- TODO projection!!
