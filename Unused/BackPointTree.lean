-- Both `Tableau` and `BuildTree` are trees with back pointers.
-- Unifying them would be a major refactoring, using something like the following.

class BPTreeAble α where        -- Tableau    -- BuildTree
  leafAble : α → Prop           -- ∅          -- ??
  stepAble : α → List α → Prop  -- rules      -- moves
  backAble : α → α → Prop       -- lpr        -- rep

open BPTreeAble

inductive BPTree {α} [BPTreeAble α] : (List α) → α → Type
| leaf : leafAble x → BPTree L x
| step : stepAble x ys → (next : ∀ y ∈ ys, BPTree (x :: L) y) → BPTree L x
| back (L : List α) (k : Fin L.length) (h2 : L[k] = x) : BPTree L x

-- now define paths in this, generically?
-- inspiration from TableauPath.lean etc?
