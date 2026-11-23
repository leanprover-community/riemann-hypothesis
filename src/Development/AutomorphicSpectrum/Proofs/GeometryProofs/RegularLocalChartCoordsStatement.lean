module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoords
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

theorem _root_.GlobalTheory.T.regular_local_chart_coords : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (c : (k : K) → J k)
    (w : (Σ k, J k) → ℂ), w ∈ mcPts P → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    ∀ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      [IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)))],
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n → a ≤ n →
    Ideal.span (Set.range fun i => algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
      Ideal.map (algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
        (ReciprocityTheory.AnForm.R.ptIdeal (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) →
    (∀ i, eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) →
    eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 →
    (∀ v ∈ ReciprocityTheory.AnForm.R.zeroSet (Cmp.SncRes.ideal (pC P) c), eval v h ≠ 0 →
      ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0)) →
    ∃ (χ : SncChart P n Bd) (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ w ∈ O ∧
      ∀ z ∈ O ∩ mcPts P, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
  exact @GlobalTheory.CompanionTheory.Ar.ChartParams.sncChart_of_regular_parameters
