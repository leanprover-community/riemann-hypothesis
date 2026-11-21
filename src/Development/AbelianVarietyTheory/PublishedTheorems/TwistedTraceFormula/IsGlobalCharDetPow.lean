import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.UnitaryOneOneChambers

open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.FormalDegree.Model
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open GlobalTheory.FlagMeas.Model (e2 W2)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar.Model

theorem isGlobalChar_detPow {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (m : ℤ)
    (h : IsURepOn (UJset ε) (detPow n m)) : IsGlobalChar μ (ujRep h) fun g => (ujMat ε g).det ^ m := by
  have hc : Continuous fun g : UJ ε => (ujMat ε g).det ^ m :=
    continuous_ujMat.matrix_det.zpow₀ m fun g => .inl (det_ujMat_ne_zero g)
  refine ⟨⟨hc.locallyIntegrable, fun _ _ => hc.continuousAt, fun f hf => ?_⟩, fun s _ => ⟨⟨fun x => (Matrix.of x).det ^ m,
    ?_, .of_forall fun _ => rfl⟩, fun x => ?_⟩⟩
  · have hf' := continuous_of_mem_ccSmooth isInducing_matCoord.continuous hf
    have hi : Integrable (fun g => f g * (ujMat ε g).det ^ m) μ :=
      (hf'.mul hc).integrable_of_hasCompactSupport hf.1.mul_right
    have e : repOp (ujRep h) μ f = (∫ g, f g * (ujMat ε g).det ^ m ∂μ) • ContinuousLinearMap.id ℂ ℂ := by
      refine IsRepOp.repOp_eq fun v => ?_
      have : (fun g => f g • ujRep h g v) = fun g => f g * (ujMat ε g).det ^ m * v := by
        funext g
        change f g * detPow n m (ujMat ε g) v = _
        rw [detPow_apply, mul_assoc]
      rw [this]
      exact ⟨hi.mul_const v, by simp [integral_mul_const]⟩
    rw [e]
    exact ⟨isTraceClass_of_finiteDimensional _, by simp [trace_eq_linearMap_trace]⟩
  · refine AnalyticAt.zpow ?_ (det_ujMat_ne_zero s)
    simp only [Matrix.det_apply']
    refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) (σ i))).analyticAt _
  · have h1 : (ujMat ε x⁻¹).det * (ujMat ε x).det = 1 := by rw [← det_mul, ← map_mul, inv_mul_cancel, map_one, det_one]
    simp only [map_mul, det_mul]
    rw [mul_right_comm, h1, one_mul]

theorem dsChar_lamDet (n : ℕ) (s : Bool) (m : ℤ) (θ : Fin n → ℝ)
    (hθ : IsRegSS (ujMat (fun _ : Fin n => s) (torusPt _ θ))) :
    dsChar (fun _ : Fin n => s) (lamDet n m) θ = (ujMat (fun _ : Fin n => s) (torusPt _ θ)).det ^ m := by
  have hd := weylDenom_ne_zero hθ
  have hv : (∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I))) ≠ 0 := by
    rw [← weylDenom_mul]; exact mul_ne_zero hd (Complex.exp_ne_zero _)
  rw [dsChar_eq _ (m := fun a => m + ((Fin.rev a : ℕ) : ℤ)) (fun a => by
    have := a.isLt
    simp only [lamDet, Formalism.QuantumDeterminants.rhoStd, Fin.val_rev]
    push_cast [Nat.cast_sub (show (a : ℕ) + 1 ≤ n by omega)]
    ring)]
  have h1 : halfDim (fun _ : Fin n => s) = 0 := by cases s <;> simp [halfDim]
  have h2 : compactWeyl (fun _ : Fin n => s) = Finset.univ := by
    ext w; simp [compactWeyl, Function.comp_def]
  rw [h1, h2, pow_zero, one_mul, div_eq_iff hv, ujMat_torusPt, det_diagonal]
  have h3 := Matrix.det_projVandermonde (fun _ : Fin n => (1 : ℂ)) fun a => Complex.exp (θ a * Complex.I)
  simp only [one_mul] at h3
  rw [← h3, ← det_transpose, det_apply', Finset.mul_sum, ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [zpow_add₀ (Complex.exp_ne_zero _), Finset.prod_mul_distrib, Finset.prod_zpow, zpow_natCast,
    Equiv.inv_apply, Equiv.Perm.sign_inv, transpose_apply, projVandermonde_apply, one_pow, one_mul]
  rw [mul_left_comm]
  rfl

theorem ds_case (n : ℕ) (s : Bool) (m : ℤ) (μ : Measure (UJ fun _ : Fin n => s)) [μ.IsHaarMeasure] :
    IsHCParam (lamDet n m) ∧ IsDS (fun _ : Fin n => s) (lamDet n m) (detPow n m) ∧
      ∀ h : IsURepOn (UJset fun _ : Fin n => s) (detPow n m), ∃ Θ, IsGlobalChar μ (ujRep h) Θ ∧
        ∀ θ : Fin n → ℝ, IsRegSS (ujMat (fun _ : Fin n => s) (torusPt _ θ)) →
          Θ (torusPt _ θ) = dsChar (fun _ : Fin n => s) (lamDet n m) θ :=
  ⟨lamDet_hc n m, isDS_detPow n s m, fun h => ⟨_, isGlobalChar_detPow _ μ m h,
    fun θ hθ => (dsChar_lamDet n s m θ hθ).symm⟩⟩




end GlobalTheory.HCChar.Model
