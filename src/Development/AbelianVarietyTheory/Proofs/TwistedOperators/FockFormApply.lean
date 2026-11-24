module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def blockB (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

def blockD (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

theorem blockB_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockB J q = (J (0, q)).1 := rfl

theorem blockD_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockD J q = (J (0, q)).2 := rfl

def fockForm (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ))
    (fun x x' y => by simp only [map_add (f := _), LinearMap.add_apply]; push_cast; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]; push_cast; ring)
    (fun x y y' => by simp only [map_add (f := _)]; push_cast; ring)
    (fun c x y => by simp only [map_smul, smul_eq_mul, Complex.real_smul]; push_cast; ring)

theorem fockForm_apply (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (x y : V) :
    fockForm β J x y = ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ) := rfl

end GlobalTheory.FockFamily

end
