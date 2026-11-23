module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplBoxVolume

theorem set_eq_preimage {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      (Matrix.toLin' A) ⁻¹' (Set.pi Set.univ fun i => Set.Ioo (-a i) (a i)) := by
  ext x
  simp [abs_lt]

end PSymplBoxVolume


open PSymplBoxVolume in
theorem SymplBoxVolume.proof : SymplBoxVolume.Statement := by
  intro ι _ _ A a hA ha
  rw [set_eq_preimage, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin'])
    , Real.volume_pi_Ioo, LinearMap.det_toLin',
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [ha i]),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, div_eq_mul_inv, mul_comm]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GroundTheory.Heights₂.Heights
