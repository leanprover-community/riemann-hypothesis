module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.HsTrace
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.IsFdAbs
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.ReflEx
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem g0 : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2 := standard_stabiliser_bound stab boost

end PositivityTheory.UnitaryDecomposition.X4
