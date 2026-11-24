module

public import Formalism.HermitianCurvature.StatementB
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul
import Formalism.HermitianCurvature.StatementQ

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_add_left (A A' C : Wq →L[ℂ] Wp) : B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_right]

theorem hs_add_right (A C C' : Wq →L[ℂ] Wp) : B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_left]

theorem hs_smul_left (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner (a • A) C = a * B.hsInner A C := by
  have h : B.hsVec (a • A) = a • B.hsVec A := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_right]

theorem hs_smul_right (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  have h : B.hsVec (a • C) = a • B.hsVec C := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_left]

end HS

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Lim

end Formalism.FourierDecayAlt.P5.HerB
