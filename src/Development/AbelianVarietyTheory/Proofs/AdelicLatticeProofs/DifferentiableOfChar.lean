import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

section
namespace GlobalTheory.ContinuousHomDifferentiable

open intervalIntegral

theorem exists_integral_ne_zero (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) :
    ∃ δ : ℝ, (∫ x in (0:ℝ)..δ, χ x) ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, χ x) (χ 0) 0 :=
    (hc.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hfun : (fun u => ∫ x in (0:ℝ)..u, χ x) = fun _ => (0:ℂ) := funext h
  rw [hfun] at h1
  have h2 : HasDerivAt (fun _ : ℝ => (0:ℂ)) 0 0 := hasDerivAt_const _ _
  have := h1.unique h2
  rw [h0] at this
  exact one_ne_zero this

theorem continuous_hom_differentiable :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ (0 : ℝ) = (1 : ℂ) →
      (∀ (s t : ℝ), χ (s + t) = χ s * χ t) → Differentiable ℝ χ := by
  intro χ hc h0 hmul
  obtain ⟨δ, hδ⟩ := exists_integral_ne_zero χ hc h0
  set c : ℂ := ∫ x in (0:ℝ)..δ, χ x with hcdef
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, χ x with hF
  have hFd : Differentiable ℝ F := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have key : ∀ s, χ s = c⁻¹ * (F (s + δ) - F s) := by
    intro s
    have e1 : χ s * c = ∫ x in (0:ℝ)..δ, χ (s + x) := by
      rw [hcdef, ← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      rw [hmul]
    have e2 : (∫ x in (0:ℝ)..δ, χ (s + x)) = ∫ x in s..s + δ, χ x := by
      rw [intervalIntegral.integral_comp_add_left (fun x => χ x) s]
      simp
    have e3 : F (s + δ) - F s = ∫ x in s..s + δ, χ x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    rw [e3, ← e2, ← e1]
    field_simp
  have hfun : χ = fun s => c⁻¹ * (F (s + δ) - F s) := funext key
  rw [hfun]
  fun_prop

end GlobalTheory.ContinuousHomDifferentiable
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockTranslate

open GlobalTheory.SplitScalar GlobalTheory.LatVac

theorem differentiable_of_char (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1)
    (hm : ∀ s t, χ (s + t) = χ s * χ t) : Differentiable ℝ χ := by
  first
  | exact @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
  | (apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable ..)

variable {D : D7}

theorem differentiable_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (L : ℝ →+ WO S T) (hL : Continuous L) (hfin : ∀ t, (L t).map (finPart D) = 0)
    (w : WO S T) : Differentiable ℝ fun t : ℝ => heisO ψ S T (L t) f w := by
  have h1 : Differentiable ℝ fun t : ℝ => ψ (symplOH S T w (L t)) := by
    refine differentiable_of_char _ (hψ.comp (continuous_const.mul (continuous_symplO S T continuous_const hL))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add, symplOH_add_right, AddChar.map_add_eq_mul]
  have h2 := hf.smooth 1 (L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)) (hL.comp (continuous_apply 0))
    (fun t => hfin _) w
  have h3 : Differentiable ℝ fun t : ℝ => f (w + L t) :=
    (h2.differentiable (by simp)).comp (differentiable_pi.2 fun _ : Fin 1 => differentiable_id)
  exact h1.mul h3

theorem dRho_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {ι : Type} (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ) (ha : ∀ i ∈ s, (a i).map (infPart D) = 0) :
    dRho (heisO ψ S T) θ τ z (∑ i ∈ s, c i • heisO ψ S T (a i) f) =
      ∑ i ∈ s, c i • heisO ψ S T (a i) (dRho (heisO ψ S T) θ τ z f) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ z)
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) =
      fun t : ℝ => ∑ i ∈ s, (c i * ψ (symplOH S T x (a i))) * heisO ψ S T (lineAt θ τ z t) f (x + a i) := by
    funext t
    rw [heisO_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [heisO_smul, heisO_comm, symplO_real_fin S T (hL.2.1 t) (ha i hi), AddChar.map_zero_eq_one, one_smul,
      mul_assoc]
    rfl
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (∑ i ∈ s, c i • heisO ψ S T (a i) f) x) 0 = _
  rw [e, deriv_fun_sum fun i _ => ((differentiable_heisO hψ hf _ hL.1 hL.2.1 (x + a i)).const_mul _) 0,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deriv_const_mul_field, mul_assoc]
  rfl

theorem isFockVacAt_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsCharAF D.host.F ψ → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ), IsFockVacAt (heisO ψ S T) θ τ J f → ∀ (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ), (∀ i ∈ s, (a i).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ i ∈ s, c i • heisO ψ S T (a i) f) := by
  intro D ψ θ S T hψ hθ f hf τ J hv ι s a c ha z
  have hc : Continuous ψ := hψ.1
  have h0 : dRho (heisO ψ S T) θ τ z f + Complex.I • dRho (heisO ψ S T) θ τ (J z) f = 0 := hv z
  rw [annih, dRho_sum hc hθ hf τ z s a c ha, dRho_sum hc hθ hf τ (J z) s a c ha, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_comm, ← smul_add, ← heisO_smul, ← heisL_apply, ← heisL_apply, ← map_add, h0, map_zero, smul_zero]

end GlobalTheory.FockTranslate

end
end
