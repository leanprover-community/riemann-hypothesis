module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionAnyDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistMetric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUnitApprox
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfIntegralMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem smallSections_upper_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArithmeticHilbertSamuelUpperBoundNumberField := by
  intro hAIS hU hRes
  have hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement :=
    degreeGeneric_of_degree (degree_of_system hAIS)
  have a0 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionAnyDegree.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hAIS hRes) hDG
  have a1 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistMetric.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof a0
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNefDual.proof hU.g7p GlobalTheory.T.packing'
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.full a1

end GlobalTheory.CompanionTheory.Ar.Giv
