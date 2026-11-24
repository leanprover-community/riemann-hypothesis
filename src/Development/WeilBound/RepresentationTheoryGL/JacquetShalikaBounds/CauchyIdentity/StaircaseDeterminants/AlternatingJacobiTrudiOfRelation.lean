module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

open Finset Matrix

namespace PositivityTheory.RgJS

namespace SkewJacobiTrudiStaircase

variable {m : ℕ}

def eM (α : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i k => (-1 : ℂ) ^ (k.rev : ℕ) * eEx α i (k.rev : ℕ)

def hM (α : Fin m → ℂ) (μ : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun k j => hZ ((μ j : ℤ) - (k.rev : ℕ)) α

theorem factor (hE : ERel) (α : Fin m → ℂ) (μ : Fin m → ℕ) :
    (Matrix.of fun i j => α i ^ μ j) = eM α * hM α μ := by
  ext i j
  rw [Matrix.of_apply, hE m α i (μ j), Matrix.mul_apply]
  simp only [eM, hM, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun r => (-1 : ℂ) ^ r * eEx α i r * hZ ((μ j : ℤ) - (r : ℤ)) α)]
  exact (Fintype.sum_equiv Fin.revPerm _ _ (fun k => rfl)).symm

theorem hZ_neg (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

theorem hZ_zero (α : Fin m → ℂ) : hZ 0 α = 1 := by
  simp only [hZ, hN, lt_irrefl, if_false, Int.toNat_zero]
  rw [Nat.antidiagonalTuple_zero_right]
  simp

theorem det_hM_stair (α : Fin m → ℂ) : (hM α (stair m)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro k _
    simp only [hM, Matrix.of_apply]
    have hk : ((stair m k : ℕ) : ℤ) - ((k.rev : ℕ) : ℤ) = 0 := by
      simp only [stair, Fin.val_rev]
      have := k.isLt
      omega
    rw [hk]
    exact hZ_zero α
  · intro i j hij
    simp only [hM, Matrix.of_apply]
    apply hZ_neg
    have hlt : (i : ℕ) < j := hij
    simp only [stair, Fin.val_rev]
    have := j.isLt
    omega

theorem hM_add_stair (α : Fin m → ℂ) (l : Fin m → ℕ) :
    hM α (l + stair m) = Matrix.of fun i j : Fin m => hZ ((l j : ℤ) - j + i) α := by
  ext k j
  simp only [hM, Matrix.of_apply, Pi.add_apply, stair, Fin.val_rev]
  congr 1
  have hj := j.isLt
  have hk := k.isLt
  push_cast
  omega

end SkewJacobiTrudiStaircase

open SkewJacobiTrudiStaircase in
theorem alternating_jacobi_trudi_of_relation : ERel → AltJT := by
  intro hE m α l
  unfold altN jt
  rw [factor hE α, factor hE α, det_mul, det_mul, det_hM_stair, mul_one, hM_add_stair]

end PositivityTheory.RgJS
