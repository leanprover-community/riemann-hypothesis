import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ThetaGauss
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

theorem sq_coord_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (hY : Y.PosDef)
    (i : ι) (v : ι → ℝ) : v i ^ 2 ≤ Y⁻¹ i i * qf Y v := by
  have hU : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hsymm : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set w : ι → ℝ := Y⁻¹ *ᵥ Pi.single i 1 with hw
  have hYw : Y *ᵥ w = Pi.single i 1 := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hwY : ∀ x : ι → ℝ, w ⬝ᵥ (Y *ᵥ x) = x i := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hYw]
    simp [dotProduct, Pi.single_apply]
  have hxY : ∀ x : ι → ℝ, x ⬝ᵥ (Y *ᵥ w) = x i := by
    intro x
    rw [hYw]
    simp [dotProduct, Pi.single_apply]
  have hwi : w i = Y⁻¹ i i := by
    rw [hw]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hpos : 0 < Y⁻¹ i i := hY.inv.diag_pos
  have hnn : ∀ t : ℝ, 0 ≤ qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
    intro t
    have h0 : 0 ≤ (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) := by
      have := hY.posSemidef.dotProduct_mulVec_nonneg (v - t • w)
      simpa using this
    have hexp : (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) =
        qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hwY, hwY, hxY, hwi]
      simp only [qf]
      ring
    linarith
  have h := hnn (v i / Y⁻¹ i i)
  have hne : Y⁻¹ i i ≠ 0 := ne_of_gt hpos
  have e : qf Y v - 2 * (v i / Y⁻¹ i i) * v i + (v i / Y⁻¹ i i) ^ 2 * Y⁻¹ i i =
      qf Y v - v i ^ 2 / Y⁻¹ i i := by
    field_simp
    ring
  rw [e] at h
  have h2 : v i ^ 2 / Y⁻¹ i i ≤ qf Y v := by linarith
  rwa [div_le_iff₀ hpos, mul_comm] at h2

end KCoord

theorem FirstCoordinateBound.intersectionNumber_baseChange : FirstCoordinateBound.Statement := by
  intro g _ Y hY v
  have h := KCoord.sq_coord_le Y hY 0 v
  rw [div_le_iff₀ hY.inv.diag_pos, mul_comm]
  exact h

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaFirstCoordSplit

theorem term_le {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ)
    (hY : Y.PosDef) (hρ : 0 < ρ) (hρY : Y⁻¹ 0 0 = ρ ^ 2) (k : Fin g → ℤ) :
    exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := by
  set v := intVec k + (a + u₁) with hv
  have hassoc : intVec k + a + u₁ = v := add_assoc _ _ _
  rw [hassoc]
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  have hv0 : v 0 = (k 0 : ℝ) + (a 0 + u₁ 0) := by simp [hv, intVec]
  have hδle : δ ≤ |v 0| := by
    have h := Metric.infDist_le_dist_of_mem (x := u₁ 0 + a 0)
      (Set.mem_range_self (f := ((↑) : ℤ → ℝ)) (-(k 0)))
    refine h.trans (le_of_eq ?_)
    rw [Real.dist_eq, hv0]
    congr 1
    push_cast
    ring
  have hδsq : δ ^ 2 ≤ v 0 ^ 2 := by
    rw [← sq_abs (v 0)]
    exact pow_le_pow_left₀ hδ0 hδle 2
  have hcoord : v 0 ^ 2 ≤ ρ ^ 2 * qf Y v := by
    have := KCoord.sq_coord_le Y hY 0 v
    rwa [hρY] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : δ ^ 2 / ρ ^ 2 ≤ qf Y v := by
    rw [div_le_iff₀ hρ2]
    linarith [mul_comm (ρ ^ 2) (qf Y v)]
  have hexp : exp (-(π / 2) * qf Y v) ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := by
    apply exp_le_exp.2
    have h1 : (π / (2 * ρ ^ 2)) * δ ^ 2 = (π / 2) * (δ ^ 2 / ρ ^ 2) := by
      field_simp
    have h2 : (π / 2) * (δ ^ 2 / ρ ^ 2) ≤ (π / 2) * qf Y v :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith
  have hsplit : exp (-π * qf Y v) = exp (-(π / 2) * qf Y v) * exp (-(π / 2) * qf Y v) := by
    rw [← exp_add]
    ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hexp (exp_pos _).le

end KThetaFirstCoordSplit

theorem ThetaFirstCoordSplit.proof : ThetaFirstCoordSplit.Statement := by
  intro g _ Y ρ a u₁ hY hρ hρY
  have hs1 : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hs2 : Summable fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + (a + u₁))) :=
    KTheta.summable_exp_qf Y hY (π / 2) (by positivity) (a + u₁)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun k => KThetaFirstCoordSplit.term_le Y ρ a u₁ hY hρ hρY k) hs1 (hs2.mul_left _)

end GroundTheory.Heights₂.Heights
end
