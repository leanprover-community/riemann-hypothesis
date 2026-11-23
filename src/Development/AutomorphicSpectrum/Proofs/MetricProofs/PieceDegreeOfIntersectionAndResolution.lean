module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstantStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetricStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvarianceStatement
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

def fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) A.a

theorem fsOfDegree_a {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    (fsOfDegree A).a = A.a := rfl

theorem isSmoothHerm_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsSmoothHerm (fsOfDegree A) :=
  GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs A.a

theorem isConjInvariantH_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsConjInvariantH (fsOfDegree A) := by
  intro z
  simp only [fsOfDegree, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

theorem pieceDegree : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement →
    GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  intro hAr hRes hPts K _ ι _ Ω _ F _ _ _ y D L sg sg' har hbir hsm hone
  have hsm₀ : ∀ j, IsSmoothHerm (fsOfDegree (L j)) := fun j => isSmoothHerm_fsOfDegree _
  have hcj₀ : ∀ j, IsConjInvariantH (fsOfDegree (L j)) := fun j => isConjInvariantH_fsOfDegree _
  have hind : ∀ s : F →+* ℂ,
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) =
        ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
          ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) := fun s =>
    GlobalTheory.T.points_integral_independent_of_metric hAr hPts K ι Ω F y D L (fun j => fsOfDegree (L j)) s har hsm hsm₀
      (fun j => (fsOfDegree_a (L j)).symm) hone
  rw [hind sg, hind sg']
  exact GlobalTheory.T.unit_log_orthogonal_weight_constant F
    (fun s => ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
      ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)))
    (fun s => GlobalTheory.T.points_integral_unique_embedding hRes K ι Ω F y D _ s har hsm₀ hcj₀ hone)
    (fun θ => GlobalTheory.T.sum_over_embeddings_unit_invariance hAr hPts K ι Ω F y D _ θ har hbir hsm₀ hone) sg sg'

end

end GlobalTheory.CompanionTheory.Ar.Giv
