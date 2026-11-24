module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
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
public import Mathlib.RingTheory.Localization.NormTrace

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem NormFormLocalization.proof : NormFormLocalization.Statement := by
  intro R F A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n x
  classical
  let b := Module.Free.chooseBasis R A
  let b' := b.localizationLocalization F (nonZeroDivisors R) A'
  have hM : ∀ j, Algebra.leftMulMatrix b' (algebraMap A A' (x j)) =
      (algebraMap R F).mapMatrix (Algebra.leftMulMatrix b (x j)) := fun j =>
    (Algebra.map_leftMulMatrix_localization R (nonZeroDivisors R) b (x j)).symm
  rw [normForm_eq_det b, normForm_eq_det b', RingHom.map_det]
  congr 1
  ext i k

  simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
  smul_eq_mul, map_sum, map_mul, map_X, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
