import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction

section
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BoxMove

theorem inBox_image_mul : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  intro D V n Q hQ K hK
  have hmt : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n) :=
    (hmt.comp continuous_fst).matrix_mul continuous_snd
  refine ⟨(fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n)) '' (Q ×ˢ K), (hQ.prod hK).image hf, ?_⟩
  rintro y hy x ⟨k, hk, h0⟩
  refine ⟨(HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n), ⟨(y, k), ⟨hy, hk⟩, rfl⟩, ?_⟩
  have hyy : Formalism.L2.Theta.mt V y * Formalism.L2.Theta.mt V y⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hx : x - (HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n) = (HMul.hMul (Formalism.L2.Theta.mt V y) ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) - k) : Mx D V.rank n) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  rw [hx, Matrix.map_mul, h0, Matrix.mul_zero]

end GlobalTheory.BoxMove
end

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactBox_of_unitaryTranslate_compact : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  atlas_forward_decl GlobalTheory.BoxMove.inBox_image_mul
end

section
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.RealMove

open GlobalTheory.Unf GlobalTheory.Unf.MajMeas

theorem realSize_mul_le_mul {D : D7} (θ : InfFam D) {m r n : ℕ} (Y : Mx D m r) (a : Mx D r n) :
    realSize θ (Y * a) ≤ n * realSize θ Y * realSize θ a := by
  calc realSize θ (Y * a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = n * realSize θ Y * realSize θ a := by
        have h : ∀ τ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a =
            n * (∑ l, ‖compAt θ τ Y i l‖) * realSize θ a := by
          intro τ i
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, mul_assoc]
        simp_rw [h, ← Finset.sum_mul, ← Finset.mul_sum]
        rfl

theorem realSize_le_of_isCompact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.realSize θ x ≤ C * GlobalTheory.Unf.realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := by
  intro D θ hθ V n Q hQ
  have hc : Continuous (fun y : GA D V => realSize θ (Formalism.L2.Theta.mt V y)) :=
    (continuous_realSize hθ).comp (GlobalTheory.Core.Rk.Level.continuous_mt' V)
  obtain ⟨M, hM⟩ := (hQ.image hc).bddAbove
  refine ⟨max 1 (n * M), le_max_left _ _, fun y hy x => ?_⟩
  set a : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with ha
  have e : x = (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by
    rw [ha]
    rw [← Matrix.mul_assoc, ← GlobalTheory.Core.Rk.Level.mt_mul', mul_inv_cancel, GlobalTheory.Core.Rk.Level.mt_one',
      Matrix.one_mul]
  have hyM : realSize θ (Formalism.L2.Theta.mt V y) ≤ M := hM ⟨y, hy, rfl⟩
  have h0 := realSize_nonneg θ a
  have h1 := realSize_nonneg θ (Formalism.L2.Theta.mt V y)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc realSize θ x = realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by rw [← e]
    _ ≤ n * realSize θ (Formalism.L2.Theta.mt V y) * realSize θ a :=
        realSize_mul_le_mul θ _ _
    _ ≤ (n * M) * realSize θ a := by gcongr
    _ ≤ max 1 (n * M) * realSize θ a := by gcongr; exact le_max_right _ _

end GlobalTheory.Unf.RealMove
end

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixRealSize_le_const_mul_of_compact_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.realSize θ x ≤ C * GlobalTheory.Unf.realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := by
  atlas_forward_decl GlobalTheory.Unf.RealMove.realSize_le_of_isCompact
end

section
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MajMul

theorem maj_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  intro D θ hθ V n Q hQ K hK
  obtain ⟨K', hK', hbox⟩ := GlobalTheory.T.exists_compactBox_of_unitaryTranslate_compact D V n Q hQ K hK
  obtain ⟨C₀, hC₀, hreal⟩ := GlobalTheory.T.adelicMatrixRealSize_le_const_mul_of_compact_translate D θ hθ V n Q hQ
  refine ⟨K', hK', fun N => ⟨C₀ ^ N, by positivity, fun y hy x => ?_⟩⟩
  set z : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with hz
  unfold GlobalTheory.Unf.maj
  by_cases hin : GlobalTheory.Unf.InBox K z
  · rw [if_pos hin, if_pos (hbox y hy x hin)]
    have h0 := GlobalTheory.Unf.realSize_nonneg θ z
    have h1 := GlobalTheory.Unf.realSize_nonneg θ x
    have h2 := hreal y hy x
    have h3 : 1 + GlobalTheory.Unf.realSize θ x ≤ C₀ * (1 + GlobalTheory.Unf.realSize θ z) := by nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ z) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ (C₀ * (1 + GlobalTheory.Unf.realSize θ z)) ^ N := by gcongr
      _ = C₀ ^ N * (1 + GlobalTheory.Unf.realSize θ z) ^ N := by rw [mul_pow]
  · rw [if_neg hin]
    have := GlobalTheory.Unf.maj_nonneg θ K' N x
    unfold GlobalTheory.Unf.maj at this
    have hC : (0:ℝ) ≤ C₀ ^ N := by positivity
    exact mul_nonneg hC this

end GlobalTheory.MajMul
end

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  atlas_forward_decl GlobalTheory.MajMul.maj_mul_le
end
