module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussLatticeCoords

theorem toLp_mulVec_intVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (k : Fin g → ℤ) :
    WithLp.toLp 2 (B *ᵥ intVec k) = ∑ i, k i • WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  have h : intVec k = ∑ i, (k i : ℝ) • (Pi.single i 1 : Fin g → ℝ) := by
    ext j
    simp [intVec, Finset.sum_apply, Pi.single_apply]
  rw [h, Matrix.mulVec_sum, WithLp.toLp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, Int.cast_smul_eq_zsmul]

end PGaussLatticeCoords


open PGaussLatticeCoords in
theorem GaussLatticeCoords.proof : GaussLatticeCoords.Statement := by
  intro g B hB
  refine ⟨fun k => ?_, fun x hx => ?_, fun k k' hkk' => ?_⟩
  · rw [toLp_mulVec_intVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    exact ⟨c, by rw [toLp_mulVec_intVec, hc]⟩
  · have hk : B *ᵥ intVec k = B *ᵥ intVec k' := hkk'
    have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
    have hv : intVec k = intVec k' := by
      have := congrArg (fun v => B⁻¹ *ᵥ v) hk
      simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec] using this
    funext i
    exact Int.cast_injective (congrFun hv i)

end GroundTheory.Heights₂.Heights
