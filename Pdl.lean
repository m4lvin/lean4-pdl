import Pdl.AllPdlRule
import Pdl.Beth
import Pdl.Completeness.BuildTree
import Pdl.Completeness.BuildTreeExistence
import Pdl.Completeness.BuildTreeModel
import Pdl.Completeness.Modelgraphs
import Pdl.Completeness.TableauGame
import Pdl.Completeness.Theorem
import Pdl.Discon
import Pdl.Distance
import Pdl.Examples
import Pdl.FischerLadner
import Pdl.Flip
import Pdl.General.AxiomBlame
import Pdl.General.FinReach
import Pdl.General.Game
import Pdl.Interpolation.Basic
import Pdl.Interpolation.Cluster
import Pdl.Interpolation.ClusterCorrection
import Pdl.Interpolation.ClusterInterpolation
import Pdl.Interpolation.ClusterItp
import Pdl.Interpolation.ClusterRho
import Pdl.Interpolation.ClusterSatDown
import Pdl.Interpolation.ClusterSatDownFacts
import Pdl.Interpolation.Def
import Pdl.Interpolation.EvalQ
import Pdl.Interpolation.FinePathDescent
import Pdl.Interpolation.Local
import Pdl.Interpolation.PreInterpolant
import Pdl.Interpolation.QFormula
import Pdl.Interpolation.SingletonCluster
import Pdl.Interpolation.Theorem
import Pdl.KeepRight
import Pdl.Kleene
import Pdl.Local.AllLocalTab
import Pdl.Local.Path
import Pdl.Local.PathIn
import Pdl.Local.Rules
import Pdl.Local.Soundness
import Pdl.Local.Tableau
import Pdl.Local.UnfoldBox
import Pdl.Local.UnfoldDia
import Pdl.PdlSteps
import Pdl.Semantics
import Pdl.SemQuot
import Pdl.Sequent
import Pdl.Soundness
import Pdl.Star
import Pdl.StayingInFL
import Pdl.Substitution
import Pdl.Syntax
import Pdl.Tableau
import Pdl.TableauExamples
import Pdl.TableauPath
import Pdl.Uniformity
import Pdl.Vocab

/-! # Propositional Dynamic Logic

This module serves as the root of the `Pdl` library, importing all its modules.

Source repository: <https://github.com/m4lvin/lean4-pdl>

Dependency graph:

![Dependency graph](https://m4lvin.github.io/lean4-pdl/docs/dependencies.svg)

(This shows the status of the `main` branch at the last successful CI run.)

-/
