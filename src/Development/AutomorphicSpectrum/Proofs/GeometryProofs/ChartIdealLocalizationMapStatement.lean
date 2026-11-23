module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMap
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

theorem _root_.GlobalTheory.T.chart_ideal_localization_map : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R),
    (∀ g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c, θ g = 0) →
    ∀ (F : MvPolynomial (Σ k, J k) ℚ), IsUnit (θ (map (algebraMap ℚ ℂ) F)) →
    ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) F : Ω)⁻¹
        (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) →
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
      (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | exact GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart <;> assumption)
