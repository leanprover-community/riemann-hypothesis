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

namespace PGaussDualMin

theorem inner_toLp_eq_dotProduct {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

theorem qf_inv_transpose_mulVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (m : Fin g → ℝ) : qf (Bᵀ * B)⁻¹ (Bᵀ *ᵥ m) = m ⬝ᵥ m := by
  have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
  have hBu : IsUnit B.det := hB.isUnit
  have h1 : (Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ m) = B⁻¹ *ᵥ m := by
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBt,
      Matrix.mul_one]
  unfold qf
  rw [h1, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hBu,
    one_mulVec]

end PGaussDualMin


open PGaussDualMin in
theorem GaussDualMin.proof : GaussDualMin.Statement := by
  intro g B hB μ hμ hμ0
  classical
  obtain ⟨m, rfl⟩ : ∃ m : Fin g → ℝ, μ = WithLp.toLp 2 m := ⟨WithLp.ofLp μ, (WithLp.toLp_ofLp _ μ).symm⟩
  have hdual := GroundTheory.Global.mem_dualLattice.1 hμ
  have hex : ∀ i : Fin g, ∃ k : ℤ, inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g))
      (WithLp.toLp 2 (B *ᵥ Pi.single i 1)) = k :=
    fun i => hdual _ (Submodule.subset_span ⟨i, rfl⟩)
  choose l hl using hex
  have hlm : intVec l = Bᵀ *ᵥ m := by
    funext i
    change ((l i : ℤ) : ℝ) = _
    rw [← hl i, inner_toLp_eq_dotProduct, dotProduct_mulVec, dotProduct_single_one,
      mulVec_transpose]
  refine ⟨l, ?_, ?_⟩
  · intro hl0
    apply hμ0
    have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
    have h0 : Bᵀ *ᵥ m = 0 := by
      rw [← hlm, hl0]; funext i; simp [intVec]
    have hm0 : m = 0 := by
      calc m = (Bᵀ)⁻¹ *ᵥ (Bᵀ *ᵥ m) := by
            rw [mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
        _ = 0 := by rw [h0, mulVec_zero]
    rw [hm0]; rfl
  · rw [hlm, qf_inv_transpose_mulVec B hB, ← real_inner_self_eq_norm_sq,
      inner_toLp_eq_dotProduct]

end GroundTheory.Heights₂.Heights
