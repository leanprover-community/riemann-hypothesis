module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem FsLogPointOf.proof : FsLogPointOf.Statement := by
  intro n h v y
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hd : h.dualNorm (h.pointOf y) = (HermNorm.std n).dualNorm (fun i => y i) := by
    simp only [HermNorm.dualNorm, HermNorm.pointOf, HermNorm.std, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.transpose_one, inv_one]
  have hn : (HermNorm.std n).norm (h.mat *ᵥ v) = h.norm v := by
    simp only [HermNorm.norm, HermNorm.std, Matrix.one_mulVec]
  have hs : ∑ j, v j * h.pointOf y j = ∑ i, (h.mat *ᵥ v) i * y i := by
    have := Matrix.dotProduct_mulVec v h.matᵀ (fun i => y i)
    rw [Matrix.vecMul_transpose] at this
    simpa [dotProduct, HermNorm.pointOf] using this
  unfold fsLog nrmv
  rw [hd, hn]
  simp only [mul_assoc, ← Finset.mul_sum, hs]

end GroundTheory.Heights₂.Heights
