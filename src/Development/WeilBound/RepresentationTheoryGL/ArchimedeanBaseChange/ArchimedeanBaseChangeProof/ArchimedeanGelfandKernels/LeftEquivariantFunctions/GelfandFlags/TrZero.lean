module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
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

@[expose] public section

noncomputable section

namespace PositivityTheory.RgBcC.VC

theorem trZero : TrZero := by
  intro V _ _ _ B T e i c hc hei heB hTe
  let t : (V →L[ℂ] V) → ℂ := fun A => LinearMap.trace ℂ V (A : V →ₗ[ℂ] V)
  have tadd : ∀ A A' : V →L[ℂ] V, t (A + A') = t A + t A' := fun A A' => by
    simp only [t, ContinuousLinearMap.coe_add, map_add (f := _)]
  have tneg : ∀ A : V →L[ℂ] V, t (-A) = -t A := fun A => by
    simp only [t, ContinuousLinearMap.coe_neg, map_neg]
  have tsmul : ∀ (a : ℂ) (A : V →L[ℂ] V), t (a • A) = a * t A := fun a A => by
    simp only [t, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul]
  have tcomm : ∀ A A' : V →L[ℂ] V, t (A * A') = t (A' * A) := fun A A' =>
    LinearMap.trace_mul_comm ℂ (A : V →ₗ[ℂ] V) (A' : V →ₗ[ℂ] V)
  set X := B * T with hXdef
  have hX : e * X = -(X * e) := by
    calc e * X = (e * B) * T := (mul_assoc _ _ _).symm
      _ = -(B * e) * T := by rw [heB]
      _ = -(B * (e * T)) := by rw [neg_mul, mul_assoc]
      _ = -(B * (T * e)) := by rw [hTe]
      _ = -(X * e) := by rw [hXdef, mul_assoc]
  have h1 : X * (e * i + i * e) = c • X := by rw [hei, mul_smul_comm, mul_one]
  have key : c * t X = 0 := by
    rw [← tsmul, ← h1, mul_add, tadd, ← mul_assoc, ← mul_assoc, tcomm (X * i) e, ← mul_assoc, hX,
      neg_mul, tneg, add_neg_cancel]
  exact (mul_eq_zero.mp key).resolve_left hc

end PositivityTheory.RgBcC.VC
