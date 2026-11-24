module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TopAvoid
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsRightStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelClauseHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.InputsOfUse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.NineFreeOfUse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.ProvHSOfUse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem good_tower_volume_theorem_bis :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
    GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections →
    GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement →
    Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hAI hU hBig hResK hSA hFHT hGaga hLine hQ hZ
  exact GlobalTheory.T.final_theorem_of_inputs_right
    GlobalTheory.CompanionTheory.Ar.Top.modelClause_holds GlobalTheory.KeyFam.keyFormula_holds hSA
    GlobalTheory.CompanionTheory.Segre.numericalSegre_closed hResK hFHT hGaga hLine
    (GlobalTheory.CompanionTheory.Ar.Giv.inputs_of_use hAI hU hBig hResK)
    (provHS_of_use hAI hU hBig hResK) GlobalTheory.T.analytic_provision_holds
    (nineFree_of_use hAI hU hBig hResK)
    (GlobalTheory.T.points_integrable_of_resolution_statement hResK)
    GlobalTheory.CompanionTheory.Ar.Giv.topAvoid hQ hZ GlobalTheory.thetaUnifAV_closed

end GlobalTheory.CompanionTheory.Ar.Link
