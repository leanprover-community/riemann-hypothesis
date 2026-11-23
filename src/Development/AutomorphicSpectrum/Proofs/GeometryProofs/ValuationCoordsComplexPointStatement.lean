module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPoint
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.valuation_coords_complex_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → ℂ), w ∈ Small.ptsOver ℂ (mCoordIdeal y) → ∃ (W : Subring Ω) (φ : W →+* ℂ), (∀ a : W, φ a ≠ 0 → IsUnit a) ∧ (∀ (k : K) (c e : ι k), w ⟨k, c⟩ ≠ 0 → ∃ h : y ⟨k, e⟩ / y ⟨k, c⟩ ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) ∧ ∀ (a : K → ℤ) (s : Ω) (v : ℂ) (C : ∀ k, ι k), Small.HasVal y a s w v → (∀ k, w ⟨k, C k⟩ ≠ 0) → ∃ h : s * ∏ k, y ⟨k, C k⟩ ^ (-a k) ∈ W, φ ⟨_, h⟩ * ∏ k, w ⟨k, C k⟩ ^ a k = v := by
  exact @GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val
