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
  | uni {X a b f} (h : (⌈a∪b⌉f) ∈ X) : localRule X { X \ {⌈a∪b⌉f} ∪ {⌈a⌉ f, ⌈b⌉ f}}
  | seq {X a b f} (h : (⌈a;b⌉f) ∈ X) : localRule X { X \ {⌈a⌉⌈b⌉f}}
  -- Splitting rules:
  | tes {X f g} (h : (⌈✓f⌉g) ∈ X) : localRule X { X \ {⌈✓f⌉g} ∪ {~f}
                                                 , X \ {⌈✓f⌉g} ∪ {g} }
  | nUn {a b f} (h : (~⌈a ∪ b⌉f) ∈ X) : localRule X { X \ {~⌈a ∪ b⌉f} ∪ {~⌈a⌉f}
                                                    , X \ {~⌈a ∪ b⌉f} ∪ {~⌈b⌉f} }
  -- STAR
  | sta {X a f} (h : (⌈∗a⌉f) ∈ X) : localRule X ({ X \ {⌈∗a⌉f} } ⊎ (listsToSets (unravel (⌈∗a⌉f))))
  | nSt {a f} (h : (~⌈∗a⌉f) ∈ X) : localRule X ({ X \ {~⌈∗a⌉f} } ⊎ (listsToSets (unravel (~⌈∗a⌉f))))

  -- TODO which rules need and modify markings?
  -- TODO only apply * if there is a marking.


-- TODO: rephrase this like Lemma 5 of MB with both directions / invertible?
lemma localRuleTruth {W} {M : KripkeModel W} {w : W} {X B} :
  localRule X B → ((∃ Y ∈ B, (M,w) ⊨ Y) ↔ (M,w) ⊨ X) :=
  by
  intro locR
  cases locR
  case nSt a f aSf_in_X =>
    have := likeLemmaFour M (∗ a)
    simp at *
    -- TODO
    sorry
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
