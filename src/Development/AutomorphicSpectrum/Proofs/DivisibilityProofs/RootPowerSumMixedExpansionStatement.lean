module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootPowerSumMixedExpansion
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.root_power_sum_mixed_expansion : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ), Q.IsHomogeneous (d + 1 - k) → ∃ Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ, (∀ i, (Hs i).IsHomogeneous (d - k)) ∧ (k = d + 1 → ∀ i, Hs i = 0) ∧ IsMixExpansion d (mixDiff (rootPs τ k * Q)) (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion | exact GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion <;> assumption)
