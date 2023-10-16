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
  | sta {X a f} (h : (⌈∗a⌉f) ∈ X) : localRule X ({ X \ {⌈∗a⌉f} } ⊎ (listsToSets (unravel (⌈∗a⌉f))))
  | nSt {a f} (h : (~⌈∗a⌉f) ∈ X) : localRule X ({ X \ {~⌈∗a⌉f} } ⊎ (listsToSets (unravel (~⌈∗a⌉f))))

  -- TODO which rules need and modify markings?
  -- TODO only apply * if there is a marking.

-- Like Lemma 5 of MB
lemma localRuleTruth {W} {M : KripkeModel W} {w : W} {X B} :
  localRule X B → ((∃ Y ∈ B, (M,w) ⊨ Y) ↔ (M,w) ⊨ X) :=
  by
  intro locR
  cases locR
  case nSt a f aSf_in_X =>
    have lemFour := likeLemmaFour M (∗ a)
    constructor
    · intro lhs -- invertibility
      sorry
    · intro Mw_X -- soundness
      have w_adiamond_f := Mw_X (~⌈∗a⌉f) aSf_in_X
      simp at w_adiamond_f lemFour
      rcases w_adiamond_f with ⟨v, w_aS_v, v_nF⟩
      -- TODO: update the below when Lemma 4 is updated to demand v ≠ w.
      -- a atomic, then done?
      -- a not atomic, disitnguish cases if v = w
      -- Now we use Lemma 4 here:
      specialize lemFour w v X.toList (X.toList ++ {~⌈∗a⌉f}) f rfl
      unfold vDash.SemImplies modelCanSemImplyForm at lemFour -- mwah, why simp not do this?
      simp at lemFour
      specialize lemFour _ w_aS_v v_nF
      · rw [conEval]
        intro g g_in
        simp at g_in
        apply Mw_X
        cases g_in
        case inl => assumption
        case inr h =>
          convert aSf_in_X
          cases h
          · rfl
          · exfalso
            tauto
      rcases lemFour with ⟨Z, Z_in, Mw_ZX, ⟨as, nBasf_in, w_as_v⟩⟩
      use (X \ {~⌈∗a⌉f}) ∪ Z.toFinset -- hmmm, good guess?
      constructor
      · apply union_elem_uplus
        · simp
        · simp
          use Z
      · rw [conEval] at Mw_ZX
        intro g g_in
        apply Mw_ZX
        simp
        simp at g_in
        tauto
  -- TODO
  all_goals { sorry }


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
