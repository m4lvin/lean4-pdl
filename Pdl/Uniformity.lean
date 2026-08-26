import Pdl.ClusterSatDown

def Tableau.isUniform (tab : Tableau .nil X) : Prop :=
  sorry

/-- If there is any tableau, then there is a uniform one. -/
lemma Tableau.toUniform (tab : Tableau .nil X) :
    ∃ u_tab : Tableau .nil X, u_tab.isUniform := by
  sorry

def LoadedCluster.uniformOfUniTab {tab : Tableau .nil X}
    (C : LoadedCluster tab) (uni_tab : tab.isUniform)
    : C.HasUniformSteps :=
  sorry
