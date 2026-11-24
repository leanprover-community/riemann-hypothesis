module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
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

@[expose] public section

noncomputable section

namespace GlobalTheory.DefPt.Model

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial GlobalTheory.DefPt
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]


end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

theorem rhoMat_one (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : rhoMat la (1 : Matrix _ _ K) = 1 := by
  simp [rhoMat, ← Module.End.one_eq_id, LinearMap.toMatrix_one]

theorem rhoMat_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la (g * h) = rhoMat la h * rhoMat la g := by
  simp [rhoMat, Matrix.transpose_mul, LinearMap.toMatrix_mul]

theorem rhoMat_scalar (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (t : K) :
    rhoMat la (t • (1 : Matrix _ _ K)) = t ^ size la • 1 := by
  have : rho la K (t • 1) = t ^ size la • LinearMap.id := LinearMap.ext fun f => rho_scalar t f
  simp [rhoMat, this]

end Tensor

end GlobalTheory.DefPt.Model

end
