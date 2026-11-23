module

public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDivisorCompare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableAbsFibreSumOfIsCxVar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIdentityAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceReducedAwayZariski
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.Development
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

namespace PositivityTheory.Tls2.Pl

theorem poincareLelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

theorem poincareLelongInv : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv :=
  poincareLelongInv_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

end PositivityTheory.Tls2.Pl
