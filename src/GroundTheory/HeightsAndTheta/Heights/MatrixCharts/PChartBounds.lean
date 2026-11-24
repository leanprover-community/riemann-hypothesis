module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.BoundsY

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MCBounds
open scoped ComplexOrder

noncomputable section

theorem MCBounds.map_sub_smul_one {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (A - s • (1 : Matrix (Fin g) (Fin g) ℝ)).map (fun x : ℝ => (x : ℂ)) =
      A.map (fun x : ℝ => (x : ℂ)) - (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  ext j k
  by_cases h : j = k <;> simp [h]

theorem MCBounds.conj_sub_smul_one {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (Z - s • (1 : Matrix (Fin g) (Fin g) ℂ)) * F = Fᴴ * Z * F - s • (Fᴴ * F) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem MCBounds.re_det_ofReal_smul {k : ℕ} (s : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    ((s : ℂ) • H).det.re = s ^ k * H.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

end

end GroundTheory.Heights₂.Heights
