module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupport
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_cone_exists_maximal_support : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)), K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) → ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical <;> assumption)
