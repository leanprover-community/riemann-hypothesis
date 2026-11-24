module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightTraceFormula
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

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
theorem _root_.GlobalTheory.T.dual_weight_trace_formula : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G → ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧ ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = ∑ ν ∈ F, trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) * weylChar ν z :=
  @GlobalTheory.CompanionTheory.RealCountG.CharDec.main
