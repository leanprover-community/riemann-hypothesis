import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronAdditive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

section Reduction

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  {π : 𝒪} (hπ : Irreducible π)

local notation "ι" => algebraMap 𝒪 K

instance isIntegral_map : IsIntegral 𝒪 (W.map (algebraMap 𝒪 K)) := ⟨⟨W, rfl⟩⟩

theorem integralModel_map : integralModel 𝒪 (W.map (algebraMap 𝒪 K)) = W := by
  apply WeierstrassCurve.map_injective (IsFractionRing.injective 𝒪 K)
  exact baseChange_integralModel_eq 𝒪 (W.map (algebraMap 𝒪 K))

include hπ

theorem valuation_lt_one_iff_dvd (r : 𝒪) :
    IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal 𝒪)
      (ι r) < 1 ↔ π ∣ r := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change r ∈ IsLocalRing.maximalIdeal 𝒪 ↔ _
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem not_dvd_Δ_of_hasGoodReduction (h : (W.map (algebraMap 𝒪 K)).HasGoodReduction 𝒪) :
    ¬π ∣ W.Δ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_Δ]
  exact h.goodReduction.not_lt

theorem not_dvd_c₄_of_hasMultiplicativeReduction
    (h : (W.map (algebraMap 𝒪 K)).HasMultiplicativeReduction 𝒪) : ¬π ∣ W.c₄ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_c₄]
  exact h.multiplicativeReduction.not_lt

theorem dvd_c₄_of_hasAdditiveReduction
    (h : (W.map (algebraMap 𝒪 K)).HasAdditiveReduction 𝒪) : π ∣ W.c₄ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_c₄]
  exact h.additiveReduction

theorem dvd_Δ_of_hasMultiplicativeReduction
    (h : (W.map (algebraMap 𝒪 K)).HasMultiplicativeReduction 𝒪) : π ∣ W.Δ := by
  rw [← valuation_lt_one_iff_dvd K hπ, ← map_Δ]
  exact h.badReduction

omit hπ in

theorem scale_map_eq (V : WeierstrassCurve 𝒪) (b₁ b₂ b₃ b₄ b₆ : 𝒪) (hπK : ι π ≠ 0)
    (h1 : V.a₁ = π * b₁) (h2 : V.a₂ = π ^ 2 * b₂) (h3 : V.a₃ = π ^ 3 * b₃)
    (h4 : V.a₄ = π ^ 4 * b₄) (h6 : V.a₆ = π ^ 6 * b₆) :
    (⟨Units.mk0 (ι π) hπK, 0, 0, 0⟩ : VariableChange K) • V.map (algebraMap 𝒪 K) =
      (⟨b₁, b₂, b₃, b₄, b₆⟩ : WeierstrassCurve 𝒪).map (algebraMap 𝒪 K) := by
  rw [variableChange_def]
  ext
  · simp only [WeierstrassCurve.map_a₁, h1, map_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₁, h2, map_mul, map_pow,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₁, h3, map_mul, map_pow,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₁, h4, map_mul, map_pow, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring
  · simp only [WeierstrassCurve.map_a₆, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₁, h6, map_mul, map_pow,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp; ring

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] hπ in
theorem Δ_scale (V : WeierstrassCurve 𝒪) (b₁ b₂ b₃ b₄ b₆ : 𝒪)
    (h1 : V.a₁ = π * b₁) (h2 : V.a₂ = π ^ 2 * b₂) (h3 : V.a₃ = π ^ 3 * b₃)
    (h4 : V.a₄ = π ^ 4 * b₄) (h6 : V.a₆ = π ^ 6 * b₆) :
    V.Δ = π ^ 12 * (⟨b₁, b₂, b₃, b₄, b₆⟩ : WeierstrassCurve 𝒪).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h1, h2, h3, h4, h6]
  ring


end Reduction

theorem Δ_ne_zero_of_isElliptic {𝒪 : Type*} [CommRing 𝒪] (K : Type*) [Field K] [Algebra 𝒪 K]
    (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] : W.Δ ≠ 0 := by
  intro h
  have := (W.map (algebraMap 𝒪 K)).isUnit_Δ
  rw [map_Δ, h, map_zero] at this
  exact not_isUnit_zero this

section Types

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)

local notation "ι" => algebraMap 𝒪 K

include hπ


omit [DecidableEq K] [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [(W.map (algebraMap 𝒪 K)).IsElliptic] in

theorem splitPoly_origin {x₀ y₀ : 𝒪}
    (h3 : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₃)
    (h4 : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₄)
    (h6 : π ∣ ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₆) :
    ((C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X - C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)).map
      (algebraMap 𝒪 (ResidueField 𝒪))) =
      C (residue 𝒪 W.c₄) * (X ^ 2 + C (residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₁) * X
        - C (residue 𝒪 ((⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W).a₂)) := by
  set W₁ := (⟨1, x₀, 0, y₀⟩ : VariableChange 𝒪) • W
  have e1 : W₁.a₁ = W.a₁ := by simp [W₁, variableChange_a₁]
  have e2 : W₁.a₂ = W.a₂ + 3 * x₀ := by simp [W₁, variableChange_a₂]
  have eb : 54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄ =
      (54 * W₁.b₆ - 3 * W₁.b₂ * W₁.b₄) + W₁.a₂ * W.c₄ := by
    simp only [W₁, variableChange_b₂, variableChange_b₄, variableChange_b₆, variableChange_a₂,
      inv_one, Units.val_one, one_pow, one_mul, WeierstrassCurve.c₄]
    ring
  have hb : π ∣ 54 * W₁.b₆ - 3 * W₁.b₂ * W₁.b₄ := by
    have hb4 : π ∣ W₁.b₄ := by
      rw [WeierstrassCurve.b₄]
      exact dvd_add (dvd_mul_of_dvd_right h4 2) (dvd_mul_of_dvd_right h3 _)
    have hb6 : π ∣ W₁.b₆ := by
      rw [WeierstrassCurve.b₆]
      exact dvd_add (dvd_pow h3 two_ne_zero) (dvd_mul_of_dvd_right h6 4)
    exact dvd_sub (dvd_mul_of_dvd_right hb6 54) (dvd_mul_of_dvd_right hb4 _)
  rw [(dvd_iff_residue_eq_zero hπ)] at hb
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_C, map_X, ResidueField.algebraMap_eq]
  rw [eb, map_add, hb, zero_add, ← e1]
  simp only [map_mul]
  ring



end Types

end

end GroundTheory.Arith.Abelian
