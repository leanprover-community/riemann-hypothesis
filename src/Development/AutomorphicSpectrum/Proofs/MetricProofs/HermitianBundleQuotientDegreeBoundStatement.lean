module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBound
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

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.hermitian_bundle_quotient_degree_bound : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  exact @GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log
