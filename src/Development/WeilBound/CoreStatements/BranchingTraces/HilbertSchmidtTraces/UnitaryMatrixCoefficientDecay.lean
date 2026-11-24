module

public import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

section

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {σ : Γ → (A →L[ℂ] A)}

theorem uRep_of (h : IsU σ) : URep σ := by
  have hm : ∀ g k x, σ (g * k) x = σ g (σ k x) := fun g k x => by rw [h.mul]; rfl
  refine ⟨hm, fun g x y => ?_, h.norm, h.cont⟩
  have hy : y = σ g (σ g⁻¹ y) := by rw [← hm, mul_inv_cancel, h.one]; rfl
  conv_lhs => rw [hy]
  exact (LinearIsometry.mk (σ g : A →ₗ[ℂ] A) (h.norm g)).inner_map_map x _

variable [MeasurableSpace Γ] {ν : Measure Γ} {d : ℝ}

theorem eq_zero_of_orth (hd : IsFd ν σ d) {w u : A} (hw : w ≠ 0) (hu : ∀ g, ⟪u, σ g w⟫_ℂ = 0) : u = 0 := by
  have h := (hd.2 w u w u).2
  simp only [hu, zero_mul, integral_zero] at h
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  rcases mul_eq_zero.1 ((div_eq_zero_iff.1 h.symm).resolve_right hd0) with h | h
  · exact absurd (inner_self_eq_zero.1 h) hw
  · exact inner_self_eq_zero.1 h

end

end PositivityTheory.UnitaryDecomposition.X4
