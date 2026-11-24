module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfIndexEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStepStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.ExItY

theorem ex_ItY_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G]
    [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW →
    R.ex_ItY := by
  intro hDS hHC D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hH hW
  have hθ : IsInfFam R.θ := hM.inf
  exact GlobalTheory.Chain.innerIntertwiners_of_pair D G Pl0 T A Ks R (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep hDS hHC D)
    (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hθ
    (GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX)

end GlobalTheory.Chain.ExItY
