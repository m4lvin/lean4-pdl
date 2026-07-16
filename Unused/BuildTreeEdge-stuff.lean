import Pdl.BuildTree

/-- Given a match and previous match, give all formulas since then.
Still TODO: actually ensure that `n` is a submatch of `m`. Without this we may loop ∞.
ALTERNATIVE: isntead of `n`, provide rewind index, see `getFormulasFromSteps`. -/
def Match.getFormulasSince {H X} {bt : BuildTree H X} (m : Match bt) (n : Match bt) :
    List Formula :=
  if m = n then
    m.getFormulasAtEnd
  else
   m.getFormulasAtEnd ++ getFormulasSince (Match.rewind m 1) n
termination_by
  m.length
decreasing_by
  apply @Match.rewind_length_lt_length_of_pos H X bt m 1
  -- Oops: 0 < 1 Only holds in Fin 2 and larger, not in in Fin 1 (i.e. here when m = .nil)
  apply Fin.pos_iff_ne_zero.mpr
  sorry

-- TODO revive "Edge" here?
def Match.edge : Match bt → Match bt → Prop := sorry

/-- Extend m towards n until (M) rule. -/
def Match.extendUntilModal :
  (m : Match bt) → (n : Match bt) → Relation.TransGen Match.edge m n → Match bt := sorry

def Match.getFormulasUntilModal {bt : BuildTree H X} :
  (m : Match bt) → (n : Match bt) → Relation.TransGen Match.edge m n → List Formula := sorry

/-- Given a free-repeat, how many staps after companion lead to (M) rule?
TODO This implies (needs a proof?) similar to Fact 4.4 in the paper! -/
def Match.getCompToModalLength {X} {bt : BuildTree [] X} (m : Match bt)
    (h : m.isFreeRepeat) : Fin (m.length - (m.getFreeRepeat h).1) :=
  sorry






/-! ## Steps between Sequents obtained from Pre-states -/

/-- The relation that should hold between sequents from the same pre-state, based on local rules.
We can never have PDL steps inside a PreState because they end there! -/
inductive Step (X : Sequent) (Y : Sequent) : Prop
  | loc (nbas : ¬ X.basic) (lt : LocalTableau X) (Y_in : Y ∈ endNodesOf lt) : Step X Y

-- TODO NEXT ?
lemma BuildTree.collect_IsChain_Step {bt : BuildTree [] X} :
    ∀ π ∈ bt.collect, π.IsChain Step := by
  sorry -- tricky?
