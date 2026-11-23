module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniform
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

theorem _root_.GlobalTheory.T.kernel_sum_bound_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (δ : ℝ) (α : GA E N → ℂ) (F Ω : Set (GA E N)),
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ → IsCompact Ω →
  ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ (n : ℕ) (ψ : Fin n → GA E N → ℂ), (∀ i, Continuous (ψ i)) →
    (∀ i, ∀ γ ∈ latticeGL E N, ∀ x, ψ i (γ * x) = ψ i x) →
    (∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ i (x * y) ∂μ = s * ψ i x) →
    (∀ i, (∫⁻ x in F, ‖ψ i x‖ₑ ^ 2 ∂μ) = 1) →
    (∀ i j, i ≠ j → ∫ x in F, ψ i x * (starRingEnd ℂ) (ψ j x) ∂μ = 0) →
    ∑ i, ∫⁻ x in Ω, ‖ψ i x‖ₑ ^ 2 ∂μ ≤ B := by
  exact @GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le
