import Pdl.Syntax
import Mathlib.Tactic.Use

-- TODO: move all this into Pdl.Syntax

/-! ## Spliting of loaded formulas -/

mutual
/-- Split any formula into the list of loaded boxes and the free formula. -/
@[simp]
def AnyFormula.split : (af : AnyFormula) → List Program × Formula
| .loaded lf => lf.split
| .normal f => ([], f)

/-- Split a loaded formula into the list of loaded boxes and the free formula. -/
@[simp]
def LoadFormula.split : (lf : LoadFormula) → List Program × Formula
| .box α af => (fun (δ,f) => (α :: δ, f)) af.split
end

@[simp]
theorem AnyFormula.split_normal (φ : Formula): (AnyFormula.normal φ).split = ([],φ) := by
  simp [AnyFormula.split]

theorem AnyFormula.box_split (af : AnyFormula) :
  (⌊α⌋af).split = (α :: af.split.1, af.split.2) := by
  cases af <;> simp

@[simp]
theorem LoadFormula.split_list_not_empty (lf : LoadFormula): lf.split.1 ≠ [] := by
  cases lf
  simp [LoadFormula.split]

@[simp]
def loadMulti_nonEmpty : (δ : List Program) → (h : δ ≠ []) → Formula → LoadFormula
| [ ],           h, _ => by exfalso; simp at *
| (α :: []),     _, φ => LoadFormula.box α φ
| (α :: d :: δ), _, φ => LoadFormula.box α (loadMulti_nonEmpty (d :: δ) (by simp) φ)

@[simp]
theorem loadMulti_nonEmpty_box (h : δ ≠ []) :
    loadMulti_nonEmpty (α :: δ) h' φ = ⌊α⌋(loadMulti_nonEmpty δ h φ) := by
  cases δ
  · absurd h; rfl
  · simp at *

theorem LoadFormula.split_eq_loadMulti_nonEmpty {δ φ} (lf : LoadFormula) :
    (h : lf.split = (δ,φ)) → lf = loadMulti_nonEmpty δ (by have := split_list_not_empty lf; simp_all) φ := by
  induction δ generalizing φ lf
  all_goals
    rcases lf_def : lf with ⟨α,af⟩
    intro h
  · simp [LoadFormula.split] at h
  case cons β δ IH =>
    cases af
    · unfold LoadFormula.split at h
      simp at h
      rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
      subst_eqs
      simp_all
    case loaded lf2 =>
      specialize @IH φ lf2 ?_
      · rw [AnyFormula.box_split] at h
        simp at *
        rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
        subst_eqs
        simp
      · rw [loadMulti_nonEmpty_box ?_]
        · simp
          rw [AnyFormula.box_split] at h
          simp at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp
          convert IH
        · simp
          rw [AnyFormula.box_split] at h
          simp at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp

theorem LoadFormula.split_eq_loadMulti_nonEmpty' {δ φ} (lf : LoadFormula)
    (h : δ ≠ []) (h2 : lf.split = (δ,φ)):
    lf = loadMulti_nonEmpty δ h φ := by
  have := LoadFormula.split_eq_loadMulti_nonEmpty lf h2
  rw [this]

theorem loadMulti_nonEmpty_eq_loadMulti :
    loadMulti_nonEmpty (δ ++ [α]) h φ = loadMulti δ α φ := by
  induction δ
  · simp
  case cons IH =>
    simp
    rw [IH]

theorem LoadFormula.split_eq_loadMulti (lf : LoadFormula) {δ α φ}
    (h : lf.split = (δ ++ [α], φ)) : lf = loadMulti δ α φ := by
  rw [LoadFormula.split_eq_loadMulti_nonEmpty' lf (by simp) h]
  apply loadMulti_nonEmpty_eq_loadMulti

theorem LoadFormula.exists_splitLast (lf : LoadFormula) :
    ∃ δ α, lf.split.1 = δ ++ [α] := by
  rcases lf with ⟨α, af⟩
  cases af
  case normal =>
    use [], α
    simp
  case loaded lf =>
    rcases LoadFormula.exists_splitLast lf with ⟨δ', α', IH⟩
    simp
    rw [IH]
    use α :: δ', α'
    simp

theorem LoadFormula.exists_loadMulti (lf : LoadFormula) :
    ∃ δ α φ, lf = loadMulti δ α φ := by
  rcases LoadFormula.exists_splitLast lf with ⟨δ, α, split1_def⟩
  use δ, α
  use lf.split.2
  apply LoadFormula.split_eq_loadMulti lf
  cases lfs_def : lf.split
  rw [lfs_def] at split1_def
  simp_all
