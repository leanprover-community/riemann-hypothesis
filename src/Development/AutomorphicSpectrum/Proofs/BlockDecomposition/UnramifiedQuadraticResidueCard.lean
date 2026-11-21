import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEntryLeMRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuadCharUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdChEOfOrdUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorHalfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticUniformizerOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSubst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RamifiedQuadraticExtensionUniformizer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticExtensionUniformizerValuation

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_uniformizer_order : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ), Ad3.IsStd χ → Ad3.IsStd (Ad3.K.GL2LocalData.chE E χ) → ((∀ a, ((η a : ℂˣ) : ℂ) = Ad3.K.GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ Ad3.K.GL2LocalData.nsg E (-1 : F) = 1) → ∀ (δ : F) (y : E), (δ ∈ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂selfDualMeasure (Ad3.K.GL2LocalData.chE E χ) = intInd y) ∧ (δ ∉ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂selfDualMeasure (Ad3.K.GL2LocalData.chE E χ) = Ad3.K.GL2LocalData.nsg E δ * (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) * (χ (-(Algebra.norm F y) / δ) : ℂ) * intInd (y * algebraMap F E δ⁻¹)) := by
  first | exact @GlobalTheory.CompanionTheory.NormGauss.gauss_main | exact GlobalTheory.CompanionTheory.NormGauss.gauss_main | (intros; apply GlobalTheory.CompanionTheory.NormGauss.gauss_main <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SphTheta.UnramQuad

theorem ord_unifUnit_of_residueCard_eq_sq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin _ hcard
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hq : 1 < residueCard F := one_lt_residueCard (K := F)
  have hf : residueDegree F E = 2 := by
    have h : residueCard E = residueCard F ^ residueDegree F E :=
      card_residueField_eq_pow_residueDegree F E
    rw [hcard] at h
    exact (Nat.pow_right_injective hq h).symm
  have he : ramificationIndex F E = 1 := by
    have h := ramificationIndex_mul_residueDegree F E
    rw [hf, hfin] at h
    omega
  have h := ord_algebraMap (K := F) (L := E) (unifUnit F : F)
  rw [he, ord_unifUnit] at h
  simpa using h

end GlobalTheory.CompanionTheory.SphTheta.UnramQuad
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_extension_valuation : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SphTheta.UnramQuad.ord_unifUnit_of_residueCard_eq_sq
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WinertRn

variable {F : Type} [Field F]

theorem det_mul_right_unipotent (x : F) (g : GL (Fin 2) F) : ((g * uni2 x).val).det = (g.val).det := by
  simp [uni2, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_upper_left (x : F) (g : GL (Fin 2) F) : (g * uni2 x).val 0 0 = g.val 0 0 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_lower_left (x : F) (g : GL (Fin 2) F) : (g * uni2 x).val 1 0 = g.val 1 0 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_upper_right (x : F) (g : GL (Fin 2) F) :
    (g * uni2 x).val 0 1 = g.val 0 0 * x + g.val 0 1 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_lower_right (x : F) (g : GL (Fin 2) F) :
    (g * uni2 x).val 1 1 = g.val 1 0 * x + g.val 1 1 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem rW_shift {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {E : Type} [Field E] [TopologicalSpace E] [MeasurableSpace E] [Algebra F E]
    (hE : Module.finrank F E = 2) (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ)
    (Φ : E → ℂ) (x A B C D Δ : F) (hΔ : Δ ≠ 0) (t : E) (ht : Algebra.norm F t = Δ) :
    GL2LocalData.rW χ σ μ lam (A / Δ) (A * x + B) (C / Δ) (C * x + D) (fun y => Φ (y * t)) 1 =
      GL2LocalData.rW χ σ μ lam (A / Δ) B (C / Δ) D
        (fun y => (χ (x * Algebra.norm F (y * t)) : ℂ) * Φ (y * t)) 1 := by
  unfold GL2LocalData.rW
  by_cases hc : C / Δ = 0
  · rw [if_pos hc, if_pos hc]
    have hN : Algebra.norm F (algebraMap F E (A / Δ) * 1 * t) = (A / Δ) ^ 2 * Δ := by
      rw [mul_one, map_mul, Algebra.norm_algebraMap, hE, ht]
    have hadd : A / Δ * (A * x + B) * Algebra.norm F (1 : E) =
        A / Δ * B * Algebra.norm F (1 : E) + x * Algebra.norm F (algebraMap F E (A / Δ) * 1 * t) := by
      rw [hN, map_one]
      field_simp
      ring
    rw [hadd, AddChar.map_add_eq_mul]
    simp only [Circle.coe_mul]
    ring
  · rw [if_neg hc, if_neg hc]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hC : C ≠ 0 := fun h => hc (by simp [h])
    have hN : Algebra.norm F (u * t) = Algebra.norm F u * Δ := by rw [map_mul, ht]
    have hadd : (A / Δ * Algebra.norm F (1 : E) + (C * x + D) * Algebra.norm F u -
          Algebra.trace F E (σ 1 * u)) / (C / Δ) =
        (A / Δ * Algebra.norm F (1 : E) + D * Algebra.norm F u -
          Algebra.trace F E (σ 1 * u)) / (C / Δ) + x * Algebra.norm F (u * t) := by
      rw [hN]
      field_simp
      ring
    simp only []
    rw [hadd, AddChar.map_add_eq_mul]
    simp only [Circle.coe_mul]
    ring

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → ∀ (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F), GL2LocalData.Wc χ σ μ lam c Φ (g * uni2 x) = GL2LocalData.Wc χ σ μ lam c (fun z => (χ (x * Algebra.norm F z) : ℂ) * Φ z) g := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hE χ σ μ lam c Φ x g
  unfold GL2LocalData.Wc
  rw [det_mul_right_unipotent, mul_right_unipotent_upper_left, mul_right_unipotent_lower_left, mul_right_unipotent_upper_right, mul_right_unipotent_lower_right]
  split_ifs with h
  · have hΔ : (g.val).det ≠ 0 := by
      have := g.isUnit.map (Matrix.detMonoidHom (n := Fin 2) (R := F))
      exact this.ne_zero
    rw [rW_shift hE χ σ μ lam Φ x _ _ _ _ _ hΔ (h.choose : E) h.choose_spec]
  · rfl

end GlobalTheory.CompanionTheory.WinertRn
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_right_unipotent_formula : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → ∀ (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F), GL2LocalData.Wc χ σ μ lam c Φ (g * uni2 x) = GL2LocalData.Wc χ σ μ lam c (fun z => (χ (x * Algebra.norm F z) : ℂ) * Φ z) g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WinertRn.main
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilRd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rW_const_mul (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d : F)
    (k : ℂ) (Φ : E → ℂ) (z : E) :
    GL2LocalData.rW χ σ μE lam a b c d (fun x => k * Φ x) z = k * GL2LocalData.rW χ σ μE lam a b c d Φ z := by
  unfold GL2LocalData.rW
  split_ifs with h
  · ring
  · have : (fun u => (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * (k * Φ u))
        = fun u => k * ((χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * Φ u) := by
      funext u; ring
    rw [this, MeasureTheory.integral_const_mul]
    ring

end GlobalTheory.CompanionTheory.WeilRd

open GlobalTheory.CompanionTheory.WeilRd in

theorem GlobalTheory.CompanionTheory.WeilRd.main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → ∀ (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ (s : Eˣ) (g : GL (Fin 2) F), GL2LocalData.Wc χ σ μ lam c Φ (g * dg2 (Units.map (Algebra.norm F : E →* F) s) 1) = ((c s : ℂˣ) : ℂ) * (((modulus (Algebra.norm F (s : E)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * GL2LocalData.Wc χ σ μ lam c (fun z => Φ (z * (s : E))) g := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hΦ s g
  set m : Fˣ := Units.map (Algebra.norm F : E →* F) s with hm
  have hmv : (m : F) = Algebra.norm F (s : E) := rfl
  have hm0 : (m : F) ≠ 0 := m.ne_zero
  have e00 : (g * dg2 m 1).val 0 0 = g.val 0 0 * m := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * dg2 m 1).val 0 1 = g.val 0 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * dg2 m 1).val 1 0 = g.val 1 0 * m := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * dg2 m 1).val 1 1 = g.val 1 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have edet : ((g * dg2 m 1).val).det = (g.val).det * m := by
    simp [dg2, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hΔ : (g.val).det ≠ 0 := by
    have := g.isUnit.map (Matrix.detMonoidHom)
    exact this.ne_zero
  have hiff : (∃ t : Eˣ, Algebra.norm F (t : E) = ((g * dg2 m 1).val).det) ↔
      ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := by
    rw [edet]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t * s⁻¹, ?_⟩
      have h1 : Algebra.norm F ((s⁻¹ : Eˣ) : E) * m = 1 := by
        rw [hmv, ← map_mul, Units.inv_mul, map_one]
      rw [Units.val_mul, map_mul, ht, mul_assoc, mul_comm (m : F), h1, mul_one]
    · rintro ⟨t, ht⟩
      exact ⟨t * s, by rw [Units.val_mul, map_mul, ht, hmv]⟩
  unfold GL2LocalData.Wc
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · have h' := hiff.2 h
    rw [dif_pos h', dif_pos h]
    set t := h.choose with ht
    set t' := h'.choose with ht'
    have nt : Algebra.norm F (t : E) = (g.val).det := h.choose_spec
    have nt' : Algebra.norm F (t' : E) = (g.val).det * m := by
      rw [← edet]; exact h'.choose_spec
    set u : Eˣ := t' * (t * s)⁻¹ with hu
    have hts : t' = (t * s) * u := by rw [hu, mul_comm, inv_mul_cancel_right]
    have nts : Algebra.norm F ((t * s : Eˣ) : E) = (g.val).det * m := by
      rw [Units.val_mul, map_mul, nt, hmv]
    have nu : Algebra.norm F (u : E) = 1 := by
      have h2 : Algebra.norm F (t' : E) = Algebra.norm F ((t * s : Eˣ) : E) * Algebra.norm F (u : E) := by
        conv_lhs => rw [hts]
        rw [Units.val_mul, map_mul]
      rw [nt', nts] at h2
      have hne : (g.val).det * (m : F) ≠ 0 := mul_ne_zero hΔ hm0
      exact (mul_eq_left₀ hne).1 h2.symm
    have hfun : (fun x => Φ (x * (t' : E))) =
        fun x => (((c u)⁻¹ : ℂˣ) : ℂ) * (fun z => Φ (z * (s : E))) (x * (t : E)) := by
      funext x
      have := hΦ.2.2 u nu (x * (t : E) * (s : E))
      rw [hts]
      simp only [Units.val_mul]
      rw [← this]
      congr 1
      ring
    have a1 : (g * dg2 m 1).val 0 0 / ((g * dg2 m 1).val).det = g.val 0 0 / (g.val).det := by
      rw [e00, edet]; field_simp
    have a2 : (g * dg2 m 1).val 1 0 / ((g * dg2 m 1).val).det = g.val 1 0 / (g.val).det := by
      rw [e10, edet]; field_simp
    rw [a1, a2, e01, e11, edet, hfun, rW_const_mul]
    have hc : ((c t' : ℂˣ) : ℂ) = ((c t : ℂˣ) : ℂ) * ((c s : ℂˣ) : ℂ) * ((c u : ℂˣ) : ℂ) := by
      rw [hts]; simp [map_mul]
    have hmod : (((modulus ((g.val).det * (m : F)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
        ((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((modulus (m : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
      rw [modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [hc, hmod, ← hmv]
    have hcu : ((c u : ℂˣ) : ℂ) * (((c u)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    linear_combination (((c t : ℂˣ) : ℂ) * ((c s : ℂˣ) : ℂ) * ((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((modulus (m : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) * GL2LocalData.rW χ σ μ lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => (fun z => Φ (z * (s : E))) (x * (t : E))) 1) * hcu
  · have h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * dg2 m 1).val).det := fun q => h (hiff.1 q)
    rw [dif_neg h', dif_neg h, mul_zero]
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_schwartz_compact_support : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → ∀ (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ (s : Eˣ) (g : GL (Fin 2) F), GL2LocalData.Wc χ σ μ lam c Φ (g * dg2 (Units.map (Algebra.norm F : E →* F) s) 1) = ((c s : ℂˣ) : ℂ) * (((modulus (Algebra.norm F (s : E)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * GL2LocalData.Wc χ σ μ lam c (fun z => Φ (z * (s : E))) g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilRd.main
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WinertLin

theorem Wc_sum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ (χ : AddChar F Circle), Continuous χ → ∀ (σ : E ≃ₐ[F] E) (lam : ℂ) (c : Eˣ →* ℂˣ) (n : ℕ) (a : Fin n → ℂ) (Ψ : Fin n → E → ℂ), (∀ j, Continuous (Ψ j)) → (∀ j, HasCompactSupport (Ψ j)) → ∀ g : GL (Fin 2) F, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (fun z => ∑ j, a j * Ψ j z) g = ∑ j, a j * GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (Ψ j) g := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin hcont χ hχ σ lam c n a Ψ hΨc hΨs g
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI := isModuleTopology F E
  have hN : Continuous (Algebra.norm F : E → F) := continuous_algebraNorm F E
  have hT : Continuous (Algebra.trace F E) := IsModuleTopology.continuous_of_linearMap _
  set μ := selfDualMeasure (GL2LocalData.chE E χ) with hμ
  have hint : ∀ (p q r : F) (t : Eˣ) (j : Fin n), Integrable (fun u : E =>
      (χ ((p * Algebra.norm F (1 : E) + q * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / r) : ℂ)
        * Ψ j (u * (t : E))) μ := by
    intro p q r t j
    have hcu : Continuous (fun u : E =>
        (χ ((p * Algebra.norm F (1 : E) + q * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / r) : ℂ)) := by
      have h1 : Continuous (fun u : E => Algebra.trace F E (σ 1 * u)) := by
        simp only [map_one, one_mul]
        exact hT
      have h2 : Continuous (fun u : E =>
          (p * Algebra.norm F (1 : E) + q * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / r) :=
        ((continuous_const.add (continuous_const.mul hN)).sub h1).div_const r
      exact continuous_subtype_val.comp (hχ.comp h2)
    have hcs : HasCompactSupport (fun u : E => Ψ j (u * (t : E))) :=
      (hΨs j).comp_homeomorph (Homeomorph.mulRight₀ (t : E) t.ne_zero)
    have hcj : Continuous (fun u : E => Ψ j (u * (t : E))) :=
      (hΨc j).comp (continuous_id.mul continuous_const)
    exact (hcu.mul hcj).integrable_of_hasCompactSupport hcs.mul_left
  have key : ∀ (p q r s : F) (t : Eˣ),
      GL2LocalData.rW χ σ μ lam p q r s (fun x => ∑ j, a j * Ψ j (x * (t : E))) 1 =
        ∑ j, a j * GL2LocalData.rW χ σ μ lam p q r s (fun x => Ψ j (x * (t : E))) 1 := by
    intro p q r s t
    unfold GL2LocalData.rW
    split_ifs with hr
    · rw [Finset.mul_sum, Finset.sum_congr rfl]
      intro j _
      ring
    · have : (fun u : E => (χ ((p * Algebra.norm F (1 : E) + s * Algebra.norm F u
            - Algebra.trace F E (σ 1 * u)) / r) : ℂ) * ∑ j, a j * Ψ j (u * (t : E))) =
          fun u => ∑ j, a j * ((χ ((p * Algebra.norm F (1 : E) + s * Algebra.norm F u
            - Algebra.trace F E (σ 1 * u)) / r) : ℂ) * Ψ j (u * (t : E))) := by
        funext u
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, integral_finset_sum _ fun j _ => (hint p s r t j).const_mul (a j),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      ring
  unfold GL2LocalData.Wc
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · simp only [dif_pos h]
    rw [key, Finset.mul_sum, Finset.sum_congr rfl]
    intro j _
    ring
  · simp [dif_neg h]

end GlobalTheory.CompanionTheory.WinertLin
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_smooth_vector : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ (χ : AddChar F Circle), Continuous χ → ∀ (σ : E ≃ₐ[F] E) (lam : ℂ) (c : Eˣ →* ℂˣ) (n : ℕ) (a : Fin n → ℂ) (Ψ : Fin n → E → ℂ), (∀ j, Continuous (Ψ j)) → (∀ j, HasCompactSupport (Ψ j)) → ∀ g : GL (Fin 2) F, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (fun z => ∑ j, a j * Ψ j z) g = ∑ j, a j * GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (Ψ j) g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WinertLin.Wc_sum
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.InertAsm

theorem Wc_intInd_right_invariant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ), Ad3.IsStd χ → IsUnramifiedChar c → ((∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ GL2LocalData.nsg E (-1 : F) = 1) → (∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det → GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) * intInd ((t : E) * algebraMap F E (mRow g)⁻¹)) → ∀ (g k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (g * k) = GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ _ χ η σ c hχ hc hη hform g k hk
  obtain ⟨hη1, hηu, -, -⟩ := hη
  classical
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hrow := GlobalTheory.CompanionTheory.SphTheta.RowIwasawa.iwasawa_lower_row F
  have hdk : modulus (k.val).det = 1 := by
    have h1 := (hrow 1 k hk).2.1
    simpa using h1
  obtain ⟨s, hs⟩ : ∃ s : Eˣ, Algebra.norm F (s : E) = (k.val).det := by
    have hk0 : (k.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det k).ne_zero
    have h1 := hη1 (Units.mk0 _ hk0)
    rw [char_congr η hηu (u := Units.mk0 _ hk0) (v := 1) (by simpa using hdk), map_one,
      Units.val_one, Units.val_mk0, GL2LocalData.nsg] at h1
    by_contra hn
    rw [if_neg hn] at h1
    norm_num at h1
  by_cases hg : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · obtain ⟨t, ht⟩ := hg
    have ht' : Algebra.norm F ((t * s : Eˣ) : E) = ((g * k).val).det := by
      rw [Units.val_mul, map_mul, ht, hs, Units.val_mul, Matrix.det_mul]
    rw [Wc_eq hc hform _ _ ht', Wc_eq hc hform _ _ ht]
    obtain ⟨hm0, hdet, hmm, hx⟩ := hrow g k hk
    exact val_eq hχ hη1 hηu hc ht ht' hm0 (hrow (g * k) 1 (one_mem _)).1 hdet hmm hx
  · have hg' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * k).val).det := by
      rintro ⟨t', ht'⟩
      refine hg ⟨t' * s⁻¹, ?_⟩
      have hs0 : Algebra.norm F (s : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 s.ne_zero
      have hmul : Algebra.norm F ((t' * s⁻¹ : Eˣ) : E) * Algebra.norm F (s : E) =
          Algebra.norm F (t' : E) := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right]
      have hd : ((g * k).val).det = (g.val).det * (k.val).det := by
        rw [Units.val_mul, Matrix.det_mul]
      rw [ht', hs, hd] at hmul
      exact mul_right_cancel₀ (hs ▸ hs0) hmul
    rw [GL2LocalData.Wc, GL2LocalData.Wc, dif_neg hg, dif_neg hg']

end GlobalTheory.CompanionTheory.SphTheta.InertAsm
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

theorem _root_.GlobalTheory.T.ramified_quadratic_extension_valuation : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ), Ad3.IsStd χ → IsUnramifiedChar c → ((∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ GL2LocalData.nsg E (-1 : F) = 1) → (∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det → GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) * intInd ((t : E) * algebraMap F E (mRow g)⁻¹)) → ∀ (g k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (g * k) = GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g := by
  first | exact @GlobalTheory.CompanionTheory.SphTheta.InertAsm.Wc_intInd_right_invariant | exact GlobalTheory.CompanionTheory.SphTheta.InertAsm.Wc_intInd_right_invariant | (intros; apply GlobalTheory.CompanionTheory.SphTheta.InertAsm.Wc_intInd_right_invariant <;> assumption) | exact @GlobalTheory.CompanionTheory.SphTheta.InertAsm.Wc_intInd_right_invariant | exact GlobalTheory.CompanionTheory.SphTheta.InertAsm.Wc_intInd_right_invariant | (intros; apply GlobalTheory.CompanionTheory.SphTheta.InertAsm.Wc_intInd_right_invariant <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_quadratic_extension_uniformizer : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ), Ad3.IsStd χ → IsUnramifiedChar c → ((∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ GL2LocalData.nsg E (-1 : F) = 1) → (∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det → GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) * intInd ((t : E) * algebraMap F E (mRow g)⁻¹)) → ∀ (u g : GL (Fin 2) F), u ∈ Iwasawa.unipotent F 2 → GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (u * g) = (χ (u.val 0 1) : ℂ) * GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g := by
  first | exact @GlobalTheory.CompanionTheory.SphTheta.WcLeft.Wc_unipotent_mul | exact GlobalTheory.CompanionTheory.SphTheta.WcLeft.Wc_unipotent_mul | (intros; apply GlobalTheory.CompanionTheory.SphTheta.WcLeft.Wc_unipotent_mul <;> assumption)
end

section
namespace GlobalTheory.CompanionTheory.LocConstSW

open Set Topology

variable {B : Type} [TopologicalSpace B]

theorem indicator_level_mem [CompactSpace B] (V : Submodule ℂ (B → ℂ)) (h1 : (1 : B → ℂ) ∈ V)
    (hmul : ∀ f ∈ V, ∀ g ∈ V, f * g ∈ V) {f : B → ℂ} (hf : f ∈ V)
    (hlc : IsLocallyConstant f) (v : ℂ) :
    ({x | f x = v} : Set B).indicator (1 : B → ℂ) ∈ V := by
  classical
  have hfin : (Set.range f).Finite := hlc.range_finite
  set S : Finset ℂ := hfin.toFinset with hS
  have hprod : ∀ T : Finset ℂ,
      (∏ w ∈ T, ((v - w)⁻¹ • (f - w • (1 : B → ℂ)))) ∈ V := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using h1
    | insert a T ha ih =>
      rw [Finset.prod_insert ha]
      exact hmul _ (V.smul_mem _ (V.sub_mem hf (V.smul_mem _ h1))) _ ih
  by_cases hv : v ∈ S
  · have key : ({x | f x = v} : Set B).indicator (1 : B → ℂ)
        = ∏ w ∈ S.erase v, ((v - w)⁻¹ • (f - w • (1 : B → ℂ))) := by
      funext x
      simp only [Finset.prod_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul,
        mul_one]
      by_cases hx : f x = v
      · rw [Set.indicator_of_mem (by simpa using hx)]
        simp only [Pi.one_apply]
        symm
        apply Finset.prod_eq_one
        intro w hw
        have hwv : v - w ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hw))
        rw [hx]
        exact inv_mul_cancel₀ hwv
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        symm
        apply Finset.prod_eq_zero (i := f x)
        · refine Finset.mem_erase.mpr ⟨hx, ?_⟩
          simp [hS]
        · simp
    rw [key]
    exact hprod _
  · have : ({x | f x = v} : Set B) = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hv
      simp [hS, ← hx]
    rw [this, Set.indicator_empty]
    exact V.zero_mem

theorem mem_of_separates : ∀ (B : Type) [TopologicalSpace B] [CompactSpace B]
    (V : Submodule ℂ (B → ℂ)), (1 : B → ℂ) ∈ V → (∀ f ∈ V, ∀ g ∈ V, f * g ∈ V) →
    (∀ f ∈ V, IsLocallyConstant f) → ∀ Φ : B → ℂ, IsLocallyConstant Φ →
    (∀ p q, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q) → Φ ∈ V := by
  intro B _ _ V h1 hmul hlc Φ hΦ hsep
  classical

  let P : Set B → Prop := fun C => C.indicator (1 : B → ℂ) ∈ V
  have hPinter : ∀ C D, P C → P D → P (C ∩ D) := by
    intro C D hC hD
    have : (C ∩ D).indicator (1 : B → ℂ) = C.indicator 1 * D.indicator 1 := by
      funext x
      by_cases hx : x ∈ C <;> by_cases hy : x ∈ D <;> simp [Set.indicator, hx, hy]
    show (C ∩ D).indicator (1 : B → ℂ) ∈ V
    rw [this]
    exact hmul _ hC _ hD
  have hPcompl : ∀ C, P C → P Cᶜ := by
    intro C hC
    have : (Cᶜ).indicator (1 : B → ℂ) = 1 - C.indicator 1 := by
      funext x
      by_cases hx : x ∈ C <;> simp [Set.indicator, hx]
    show (Cᶜ).indicator (1 : B → ℂ) ∈ V
    rw [this]
    exact V.sub_mem h1 hC
  have hPunion : ∀ C D, P C → P D → P (C ∪ D) := by
    intro C D hC hD
    have := hPcompl _ (hPinter _ _ (hPcompl C hC) (hPcompl D hD))
    rwa [Set.compl_inter, compl_compl, compl_compl] at this
  have hPuniv : P Set.univ := by
    show (Set.univ : Set B).indicator (1 : B → ℂ) ∈ V
    rw [Set.indicator_univ]
    exact h1
  have hPempty : P ∅ := by
    show (∅ : Set B).indicator (1 : B → ℂ) ∈ V
    rw [Set.indicator_empty]
    exact V.zero_mem

  have hPopen : ∀ C, P C → IsOpen C := by
    intro C hC
    have := (hlc _ hC).isOpen_fiber (1 : ℂ)
    convert this using 1
    ext x
    by_cases hx : x ∈ C <;> simp [Set.indicator, hx]
  have hlevel : ∀ v : ℂ, P (Φ ⁻¹' {v}) := by
    intro v
    set K : Set B := Φ ⁻¹' {v} with hK
    have hKopen : IsOpen K := hΦ.isOpen_fiber v
    have hKclosed : IsClosed K := hΦ.isClosed_fiber v

    have hstep : ∀ p ∈ K, ∃ C, P C ∧ p ∈ C ∧ C ∩ Kᶜ = ∅ := by
      intro p hp
      have hcomp : IsCompact (Kᶜ) := hKopen.isClosed_compl.isCompact
      have : ∃ C, P C ∧ p ∈ C ∧ C ∩ Kᶜ = ∅ := by
        refine hcomp.induction_on (p := fun s => ∃ C, P C ∧ p ∈ C ∧ C ∩ s = ∅) ?_ ?_ ?_ ?_
        · exact ⟨Set.univ, hPuniv, trivial, by simp⟩
        · rintro s t hst ⟨C, hC, hpC, hCt⟩
          refine ⟨C, hC, hpC, ?_⟩
          exact Set.subset_empty_iff.mp (hCt ▸ Set.inter_subset_inter_right C hst)
        · rintro s t ⟨C, hC, hpC, hCs⟩ ⟨D, hD, hpD, hDt⟩
          refine ⟨C ∩ D, hPinter _ _ hC hD, ⟨hpC, hpD⟩, ?_⟩
          ext x
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false, iff_false]
          rintro ⟨⟨hxC, hxD⟩, hxs | hxt⟩
          · exact (Set.eq_empty_iff_forall_notMem.mp hCs x) ⟨hxC, hxs⟩
          · exact (Set.eq_empty_iff_forall_notMem.mp hDt x) ⟨hxD, hxt⟩
        · intro q hq
          have hne : Φ p ≠ Φ q := by
            have hp' : Φ p = v := hp
            have hq' : Φ q ≠ v := hq
            rw [hp']
            exact Ne.symm hq'
          obtain ⟨f, hfV, hfpq⟩ := hsep p q hne
          have hC : P {x | f x = f p} := indicator_level_mem V h1 hmul hfV (hlc f hfV) (f p)
          have hopen : IsOpen ({x | f x = f p}ᶜ : Set B) := (hlc f hfV).isClosed_fiber (f p) |>.isOpen_compl
          refine ⟨{x | f x = f p}ᶜ, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds ?_), _, hC, rfl, ?_⟩
          · exact fun h => hfpq h.symm
          · simp
      exact this
    have hKcomp : IsCompact K := hKclosed.isCompact
    have : ∃ C, P C ∧ K ⊆ C ∧ C ⊆ K := by
      refine hKcomp.induction_on (p := fun s => ∃ C, P C ∧ s ⊆ C ∧ C ⊆ K) ?_ ?_ ?_ ?_
      · exact ⟨∅, hPempty, subset_rfl, Set.empty_subset _⟩
      · rintro s t hst ⟨C, hC, htC, hCK⟩
        exact ⟨C, hC, hst.trans htC, hCK⟩
      · rintro s t ⟨C, hC, hsC, hCK⟩ ⟨D, hD, htD, hDK⟩
        exact ⟨C ∪ D, hPunion _ _ hC hD, Set.union_subset_union hsC htD,
          Set.union_subset hCK hDK⟩
      · intro p hp
        obtain ⟨C, hC, hpC, hCK⟩ := hstep p hp
        refine ⟨C, mem_nhdsWithin_of_mem_nhds ((hPopen C hC).mem_nhds hpC), C, hC, subset_rfl, ?_⟩
        intro x hx
        by_contra hxK
        exact (Set.eq_empty_iff_forall_notMem.mp hCK x) ⟨hx, hxK⟩
    obtain ⟨C, hC, hKC, hCK⟩ := this
    have : C = K := Set.Subset.antisymm hCK hKC
    rw [← this]
    exact hC

  have hfin : (Set.range Φ).Finite := hΦ.range_finite
  have hsum : Φ = ∑ v ∈ hfin.toFinset, v • (Φ ⁻¹' {v}).indicator (1 : B → ℂ) := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single (Φ x)]
    · simp [Set.indicator]
    · intro b _ hb
      have : x ∉ Φ ⁻¹' {b} := fun h => hb (by simpa using h.symm)
      simp [Set.indicator_of_notMem this]
    · intro h
      exact absurd (by simp) h
  rw [hsum]
  exact V.sum_mem fun v _ => V.smul_mem _ (hlevel v)

end GlobalTheory.CompanionTheory.LocConstSW
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_separating_subalgebra : ∀ (B : Type) [TopologicalSpace B] [CompactSpace B] (V : Submodule ℂ (B → ℂ)), (1 : B → ℂ) ∈ V → (∀ f ∈ V, ∀ g ∈ V, f * g ∈ V) → (∀ f ∈ V, IsLocallyConstant f) → ∀ Φ : B → ℂ, IsLocallyConstant Φ → (∀ p q, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q) → Φ ∈ V := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocConstSW.mem_of_separates
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp

section Gen

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem exists_scale {S : Set K} (hS : IsCompact S) : ∃ s : Kˣ, ∀ x ∈ S, x * (s : K) ∈ 𝒪[K] := by
  set π : K := (unifUnit K : K) with hπ
  have hm : modulus π < 1 := by
    rw [hπ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit, _root_.zpow_neg, zpow_one]
    exact inv_lt_one_of_one_lt₀ (one_lt_residueCard_nnreal (K := K))
  have hπO : π ∈ 𝒪[K] := modulus_le_one_iff.1 hm.le
  have hpow : ∀ n : ℕ, modulus (π ^ n) = modulus π ^ n := by
    intro n
    induction n with
    | zero => simp [modulus_one]
    | succ n ih => rw [pow_succ, modulus_mul, ih, pow_succ]
  let U : ℕ → Set K := fun n => {x | x * π ^ n ∈ 𝒪[K]}
  have ho : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer
  have hUo : ∀ n, IsOpen (U n) := fun n => ho.preimage (continuous_mul_right _)
  have hcov : S ⊆ ⋃ n, U n := by
    intro x _
    refine Set.mem_iUnion.2 ?_
    by_cases hx : x = 0
    · exact ⟨0, by simp [U, hx, zero_mem]⟩
    have hmx : 0 < modulus x := pos_iff_ne_zero.2 (modulus_ne_zero hx)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hmx) hm
    refine ⟨n, modulus_le_one_iff.1 ?_⟩
    rw [modulus_mul, hpow]
    calc modulus x * modulus π ^ n ≤ modulus x * (modulus x)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hmx.ne'
  have hmono : Monotone U := monotone_nat_of_le_succ fun n x hx => by
    have h : x * π ^ (n + 1) = (x * π ^ n) * π := by rw [pow_succ, mul_assoc]
    show x * π ^ (n + 1) ∈ 𝒪[K]
    rw [h]
    exact mul_mem hx hπO
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo hcov hmono.directed_le
  refine ⟨unifUnit K ^ n, fun x hx => ?_⟩
  rw [Units.val_pow_eq_pow_val]
  exact hn hx

theorem isLocallyConstant_char {χ : AddChar K Circle} (hχ : IsStd χ) :
    IsLocallyConstant (χ : K → Circle) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun a => ?_
  have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
  have ho : IsOpen {y : K | y - a ∈ valBall K (addCharConductor χ)} :=
    (isOpen_valBall (addCharConductor χ)).preimage (continuous_id.sub continuous_const)
  filter_upwards [ho.mem_nhds (show a - a ∈ valBall K (addCharConductor χ) by
    rw [sub_self]; exact zero_mem _)] with y hy
  have h1 : χ (y - a) = 1 := h _ hy
  calc χ y = χ ((y - a) + a) := by rw [sub_add_cancel]
    _ = χ a := by rw [AddChar.map_add_eq_mul, h1, one_mul]

end Gen

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)]

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep (modulus_norm)

theorem eq_of_norm_eq {c : Eˣ →* ℂˣ} (hc : IsUnramifiedChar c) {Φ : E → ℂ}
    (hΦ : Φ ∈ GL2LocalData.SBc F E c) {p q : E} (h : Algebra.norm F p = Algebra.norm F q) : Φ p = Φ q := by
  have hz : ∀ {x : E}, Algebra.norm F x = 0 → x = 0 := fun hx => Algebra.norm_eq_zero_iff.1 hx
  have hz0 : Algebra.norm F (0 : E) = 0 := Algebra.norm_eq_zero_iff.2 rfl
  by_cases hp : p = 0
  · subst hp
    rw [hz (h.symm.trans hz0)]
  have hq : q ≠ 0 := fun hq => hp (hz (by rw [h, hq, hz0]))
  have hNp : Algebra.norm F p ≠ 0 := Algebra.norm_ne_zero_iff.2 hp
  let u : Eˣ := Units.mk0 (q / p) (div_ne_zero hq hp)
  have hu : Algebra.norm F (u : E) = 1 := by
    refine mul_right_cancel₀ hNp ?_
    rw [one_mul, ← map_mul, h]
    simp only [u, Units.val_mk0, div_mul_cancel₀ q hp]
  have hm : modulus (u : E) = 1 := by
    rw [← modulus_norm (K := F), hu, modulus_one]
  have h1 : c u = 1 := by
    have := char_congr c hc (u := u) (v := 1) (by simpa using hm)
    simpa using this
  have h2 := hΦ.2.2 u hu p
  rw [h1, inv_one, Units.val_one, one_mul] at h2
  rw [← h2]
  simp only [u, Units.val_mk0, mul_div_cancel₀ q hp]

theorem sub_eq_neg_smul_add_of_sub_smul_eq (χ : AddChar F Circle) (hχ : IsStd χ) (c : Eˣ →* ℂˣ) (hc : IsUnramifiedChar c)
    (Φ : E → ℂ) (hΦ : Φ ∈ GL2LocalData.SBc F E c) :
    ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x =
      ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  obtain ⟨s, hs⟩ := exists_scale (K := E) hΦ.2.1
  let Bs : Set E := {x | x * (s : E) ∈ 𝒪[E]}
  have hO : IsCompact (𝒪[E] : Set E) := IsNonarchimedeanLocalField.isCompact_closedBall E 1
  have hBc : IsCompact Bs :=
    (Homeomorph.mulRight₀ (s : E) s.ne_zero).isCompact_preimage.2 hO
  haveI : CompactSpace Bs := isCompact_iff_compactSpace.1 hBc
  let e : F → Bs → ℂ := fun y x => (χ (y * Algebra.norm F (x : E)) : ℂ)
  let V : Submodule ℂ (Bs → ℂ) := Submodule.span ℂ (Set.range e)
  have hone : (1 : Bs → ℂ) ∈ V := Submodule.subset_span ⟨0, by funext x; simp [e]⟩
  have hemul : ∀ y y', e y * e y' = e (y + y') := fun y y' => by
    funext x
    simp [e, add_mul, AddChar.map_add_eq_mul]
  have hmul : ∀ f ∈ V, ∀ g ∈ V, f * g ∈ V := by
    intro f hf g hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨y, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨y', rfl⟩ := hg
        rw [hemul]
        exact Submodule.subset_span ⟨_, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact V.add_mem ha hb
      | smul t a _ ha => rw [mul_smul_comm]; exact V.smul_mem _ ha
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact V.add_mem ha hb
    | smul t a _ ha => rw [smul_mul_assoc]; exact V.smul_mem _ ha
  have hNc : Continuous (Algebra.norm F : E → F) := GroundTheory.LocalField.continuous_algebraNorm F E
  have hlc : ∀ f ∈ V, IsLocallyConstant f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨y, rfl⟩ := hf
      have hcont : Continuous fun x : Bs => y * Algebra.norm F (x : E) :=
        continuous_const.mul (hNc.comp continuous_subtype_val)
      exact ((isLocallyConstant_char hχ).comp_continuous hcont).comp (fun z : Circle => (z : ℂ))
    | zero => exact IsLocallyConstant.const 0
    | add a b _ _ ha hb => exact ha.add hb
    | smul t a _ ha => exact (IsLocallyConstant.const t).mul ha
  have hsep : ∀ p q : Bs, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q := by
    intro p q hpq
    have hd : Algebra.norm F (p : E) - Algebra.norm F (q : E) ≠ 0 := fun h =>
      hpq (eq_of_norm_eq hc hΦ (sub_eq_zero.1 h))
    obtain ⟨t, ht⟩ : ∃ t, χ t ≠ 1 := by
      by_contra hall
      push_neg at hall
      exact hχ.2.1 (by ext x; simp [hall x])
    set d := Algebra.norm F (p : E) - Algebra.norm F (q : E) with hdd
    refine ⟨e (t / d), Submodule.subset_span ⟨_, rfl⟩, fun h => ht ?_⟩
    have h1 : χ (t / d * Algebra.norm F (p : E)) = χ (t / d * Algebra.norm F (q : E)) :=
      Circle.coe_injective h
    have h2 : t / d * Algebra.norm F (p : E) = t + t / d * Algebra.norm F (q : E) := by
      have : t = t / d * d := (div_mul_cancel₀ t hd).symm
      rw [hdd] at this ⊢
      linear_combination (-1 : F) * this
    rw [h2, AddChar.map_add_eq_mul] at h1
    exact mul_right_cancel (h1.trans (one_mul _).symm)
  have hmem : (fun x : Bs => Φ x) ∈ V :=
    GlobalTheory.T.locally_constant_separating_subalgebra Bs V hone hmul hlc (fun x : Bs => Φ x)
      (hΦ.1.comp_continuous continuous_subtype_val) hsep
  obtain ⟨w, hw⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  let eq := w.support.equivFin
  refine ⟨s, w.support.card, fun j => w (eq.symm j), fun j => (eq.symm j : F), fun x => ?_⟩
  by_cases hx : x * (s : E) ∈ 𝒪[E]
  · have h1 : Φ x = (w.sum fun i a => a • e i) ⟨x, hx⟩ := by rw [hw]
    have h2 : (intInd (x * (s : E)) : ℂ) = 1 := by simp [intInd, hx]
    rw [h1, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort w.support,
      ← Equiv.sum_comp eq.symm]
    simp [e, h2]
  · have h0 : Φ x = 0 := by
      by_contra h
      exact hx (hs x (subset_tsupport _ h))
    have h2 : (intInd (x * (s : E)) : ℂ) = 0 := by simp [intInd, hx]
    simp [h0, h2]

end Main

theorem sbc_decomp : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ χ : AddChar F Circle, Ad3.IsStd χ → ∀ c : Eˣ →* ℂˣ, IsUnramifiedChar c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x = ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ _ χ hχ c hc Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact sub_eq_neg_smul_add_of_sub_smul_eq χ hχ c hc Φ hΦ

end GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_whittaker_formula : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ χ : AddChar F Circle, Ad3.IsStd χ → ∀ c : Eˣ →* ℂˣ, IsUnramifiedChar c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∃ (s : Eˣ) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → F), ∀ x, Φ x = ∑ j, a j * ((χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SphTheta.InertAsm.Decomp.sbc_decomp
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WInert

theorem winert_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → ∀ χ : AddChar F Circle, IsStd χ → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) → ∀ c : Eˣ →* ℂˣ, IsUnit1 c → IsUnramifiedChar c → ∀ b : ℂˣ, b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F)) → ∀ Φ ∈ GL2LocalData.SBc F E c, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) (GL2LocalData.lamE E χ η) c Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] (g * h)} := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 hcont hres χ hχ σ hσ η hη c hc1 hc b hb Φ hΦ
  have hord := GlobalTheory.T.unramified_quadratic_extension_valuation F E h2 hcont hres
  obtain ⟨η', hη'⟩ := GlobalTheory.CompanionTheory.SphTheta.UnramQuad.exists_quadChar_unramified F E h2 hcont hord
  have hηe : η = η' := by
    ext a
    rw [hη, hη'.1]
  subst hηe
  have hstd := GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif F E h2 hcont hord χ hχ
  have hlam := GlobalTheory.CompanionTheory.LamUnr.lamE_eq_one F E χ η hχ hstd hη'.2.1 hη'.2.2.1
  have hform := GlobalTheory.CompanionTheory.SphTheta.inert_rw F E h2 hcont hord χ η σ hσ hχ hstd hη'
    (GlobalTheory.T.unramified_quadratic_uniformizer_order F E h2 hcont hord χ η hχ hstd hη')
  rw [hlam]
  have hψ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar χ) x = 1 := by
    intro x hx
    have h1 := isTrivialOn_addCharConductor hχ.1 hχ.2.1 x
      (by rw [hχ.2.2]; exact mem_valBall_zero_iff.2 hx)
    simp [h1]
  set f₁ : GL (Fin 2) F → ℂ := Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] with hf₁
  have hW0 : ∀ g, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g = f₁ g := by
    intro g
    have hg := Spherical.eq_iwasawa g
    have hu := Spherical.iwasawaUnip_mem g
    have hk := Spherical.iwasawaInt_mem g
    set u := Spherical.iwasawaUnip g
    set k := Spherical.iwasawaInt g
    set l := Iwasawa.iwasawaExponent F 2 g
    rw [hg, hf₁, Spherical.sphericalWhittaker_apply hψ _ hu hk,
      GlobalTheory.T.ramified_quadratic_extension_valuation F E h2 hcont hord χ η σ c hχ hc hη' hform _ k hk, mul_assoc,
      GlobalTheory.T.ramified_quadratic_extension_uniformizer F E h2 hcont hord χ η σ c hχ hc hη' hform u _ hu,
      GlobalTheory.T.quadratic_extension_uniformizer_valuation F E h2 hcont hord χ η σ c hχ hc hη' hform b hb l]
    have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar χ) u = (χ (u.val 0 1) : ℂ) := by
      simp [Whittaker.psiN, Whittaker.superdiagSum, Fin.sum_univ_two]
      rfl
    rw [hpsi]
    split_ifs with hl
    · ring
    · simp
  obtain ⟨s, n, a, y, hdec⟩ := GlobalTheory.T.unramified_extension_whittaker_formula F E h2 hcont hord χ hχ c hc Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  set Ψ : Fin n → E → ℂ := fun j x => (χ (y j * Algebra.norm F x) : ℂ) * intInd (x * (s : E)) with hΨ
  have hΦe : Φ = fun z => ∑ j, a j * Ψ j z := funext hdec
  have hI0 : Continuous (fun x : E => (intInd (x * (s : E)) : ℂ)) :=
    (InertAsm.intInd_isLocallyConstant (K := E)).continuous.comp (continuous_id.mul continuous_const)
  have hI1 : HasCompactSupport (fun x : E => (intInd (x * (s : E)) : ℂ)) :=
    (InertAsm.intInd_hasCompactSupport (K := E)).comp_homeomorph (Homeomorph.mulRight₀ (s : E) s.ne_zero)
  have hPc : ∀ j, Continuous (Ψ j) := fun j => by
    have hN := GroundTheory.LocalField.continuous_algebraNorm F E
    exact (continuous_induced_dom.comp (hχ.1.comp (continuous_const.mul hN))).mul hI0
  have hPs : ∀ j, HasCompactSupport (Ψ j) := fun j => hI1.mul_left
  set κ : ℂ := ((c s : ℂˣ) : ℂ) * (((modulus (Algebra.norm F (s : E)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero _) ?_
    have h0 : ((modulus (Algebra.norm F (s : E)) : ℝ) : ℂ) ≠ 0 := by
      have := modulus_ne_zero (K := F) ((Algebra.norm_ne_zero_iff).2 s.ne_zero)
      exact_mod_cast this
    simp [Complex.cpow_eq_zero_iff, h0]
  have hstep : ∀ j g, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c (Ψ j) g =
      κ⁻¹ * f₁ (g * (uni2 (y j) * dg2 (Units.map (Algebra.norm F : E →* F) s) 1)) := by
    intro j g
    have h1 := GlobalTheory.T.weil_whittaker_right_unipotent_formula F E h2 χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c (fun z => intInd (z * (s : E))) (y j) g
    have h2' := GlobalTheory.T.weil_whittaker_schwartz_compact_support F E h2 χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd
      (InertAsm.intInd_mem_SBc c hc) s (g * uni2 (y j))
    rw [← hW0, ← mul_assoc g, h2', h1, ← hκ, inv_mul_cancel_left₀ hκ0]
  have hfun : GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c Φ =
      ∑ j, (a j * κ⁻¹) • (fun g => f₁ (g * (uni2 (y j) * dg2 (Units.map (Algebra.norm F : E →* F) s) 1))) := by
    funext g
    rw [hΦe, GlobalTheory.T.weil_whittaker_smooth_vector F E h2 hcont χ hχ.1 σ 1 c n a Ψ hPc hPs g, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hstep, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [hfun]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory.CompanionTheory.WInert
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_residue_card : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → ∀ χ : AddChar F Circle, IsStd χ → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) → ∀ c : Eˣ →* ℂˣ, IsUnit1 c → IsUnramifiedChar c → ∀ b : ℂˣ, b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F)) → ∀ Φ ∈ GL2LocalData.SBc F E c, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) (GL2LocalData.lamE E χ η) c Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] (g * h)} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WInert.winert_span
end
