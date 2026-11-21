import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronAdditive

section
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
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsDiscreteValuationRing

def iotaN (n : ℕ) (a b : ℕ∞) : ZMod n :=
  if b ≤ a then ((b.toNat : ℕ) : ZMod n) else -((a.toNat : ℕ) : ZMod n)

theorem top_ne_three_mul (τ : ℕ) : (⊤ : ℕ∞) ≠ 3 * (τ : ℕ∞) := by
  have : (3 : ℕ∞) * (τ : ℕ∞) = ((3 * τ : ℕ) : ℕ∞) := by push_cast; rfl
  rw [this]; exact (ENat.natCast_ne_top _).symm

theorem top_ne_two_mul (τ : ℕ) : (⊤ : ℕ∞) ≠ 2 * (τ : ℕ∞) := by
  have : (2 : ℕ∞) * (τ : ℕ∞) = ((2 * τ : ℕ) : ℕ∞) := by push_cast; rfl
  rw [this]; exact (ENat.natCast_ne_top _).symm

theorem iotaN_of_le {n : ℕ} {a b : ℕ∞} (h : b ≤ a) : iotaN n a b = ((b.toNat : ℕ) : ZMod n) := by
  simp [iotaN, h]

theorem iotaN_of_lt {n : ℕ} {a b : ℕ∞} (h : a < b) : iotaN n a b = -((a.toNat : ℕ) : ZMod n) := by
  simp [iotaN, not_le.2 h]

theorem iotaN_swap {n : ℕ} {a b : ℕ∞} (htie : a = b → 2 * a = n) :
    iotaN n b a = -iotaN n a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [iotaN_of_le h.le, iotaN_of_lt h, neg_neg]
  · subst h
    rw [iotaN_of_le le_rfl, eq_neg_iff_add_eq_zero]
    have h2 := htie rfl
    have ha : a ≠ ⊤ := by rintro rfl; simp at h2
    lift a to ℕ using ha
    simp only [ENat.toNat_natCast]
    rw [← Nat.cast_add, ← two_mul]
    have : 2 * a = n := by exact_mod_cast h2
    rw [this, ZMod.natCast_self]
  · rw [iotaN_of_lt h, iotaN_of_le h.le]

theorem iotaN_two {n : ℕ} {τ aP bP aR bR : ℕ∞} (hτ : 1 ≤ τ)
    (cP : (aP = bP ∧ 2 * aP = n) ∨ (aP ≠ bP ∧ min aP bP = τ))
    (cR : (aR = bR ∧ 2 * aR = n) ∨ (aR ≠ bR ∧ min aR bR = τ))
    (sP : aP ≠ bP → (3 * τ < n → aP + bP = 3 * τ) ∧ (n < 3 * τ → aP + bP = n))
    (sR : aR ≠ bR → (3 * τ < n → aR + bR = 3 * τ) ∧ (n < 3 * τ → aR + bR = n))
    (hα : (3 * τ < n → aP + aR = 3 * τ) ∧ (n < 3 * τ → aP + aR = n) ∧ (3 * τ = n → n ≤ aP + aR))
    (hβ : (3 * τ < n → bP + bR = 3 * τ) ∧ (n < 3 * τ → bP + bR = n) ∧ (3 * τ = n → n ≤ bP + bR)) :
    iotaN n aP bP + iotaN n aR bR = 0 := by
  have fin_of_two : ∀ {a : ℕ∞}, 2 * a = (n : ℕ∞) → a ≠ ⊤ := by
    intro a h; rintro rfl; simp at h
  have min_cases : ∀ {a b : ℕ∞}, a ≠ b → min a b = τ → (a = τ ∧ τ < b) ∨ (b = τ ∧ τ < a) := by
    intro a b hab hm
    rcases le_total a b with h | h
    · rw [min_eq_left h] at hm; exact Or.inl ⟨hm, hm ▸ lt_of_le_of_ne h hab⟩
    · rw [min_eq_right h] at hm; exact Or.inr ⟨hm, hm ▸ lt_of_le_of_ne h (Ne.symm hab)⟩
  have hτ' : ∀ {a b : ℕ∞}, a ≠ b → min a b = τ → τ ≠ ⊤ := by
    intro a b hab hm hτt
    rw [hτt, min_eq_top] at hm
    exact hab (hm.1.trans hm.2.symm)
  rcases cP with ⟨tP, hP⟩ | ⟨nP, mP⟩ <;> rcases cR with ⟨tR, hR⟩ | ⟨nR, mR⟩
  · subst tP tR
    rw [iotaN_of_le le_rfl, iotaN_of_le le_rfl]
    lift aP to ℕ using fin_of_two hP
    lift aR to ℕ using fin_of_two hR
    simp only [ENat.toNat_natCast]
    have h1 : 2 * aP = n := by exact_mod_cast hP
    have h2 : 2 * aR = n := by exact_mod_cast hR
    rw [← Nat.cast_add, show aP + aR = n by omega, ZMod.natCast_self]
  · exfalso
    subst tP
    have hτf := hτ' nR mR
    lift τ to ℕ using hτf
    lift aP to ℕ using fin_of_two hP
    have h1 : 2 * aP = n := by exact_mod_cast hP
    have hτ1 : 1 ≤ τ := by exact_mod_cast hτ
    rcases lt_trichotomy (3 * τ) n with h | h | h
    · have e1 := hα.1 (by exact_mod_cast h)
      have e2 := hβ.1 (by exact_mod_cast h)
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      apply nR
      have e1' : aP + aR = 3 * τ := by exact_mod_cast e1
      have e2' : aP + bR = 3 * τ := by exact_mod_cast e2
      exact_mod_cast (show aR = bR by omega)
    · have e1 := hα.2.2 (by exact_mod_cast h)
      have e2 := hβ.2.2 (by exact_mod_cast h)
      rcases min_cases nR mR with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm] at e1
        have : n ≤ aP + τ := by exact_mod_cast e1
        omega
      · rw [hm] at e2
        have : n ≤ aP + τ := by exact_mod_cast e2
        omega
    · have e1 := hα.2.1 (by exact_mod_cast h)
      have e2 := hβ.2.1 (by exact_mod_cast h)
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      apply nR
      have e1' : aP + aR = n := by exact_mod_cast e1
      have e2' : aP + bR = n := by exact_mod_cast e2
      exact_mod_cast (show aR = bR by omega)
  · exfalso
    subst tR
    have hτf := hτ' nP mP
    lift τ to ℕ using hτf
    lift aR to ℕ using fin_of_two hR
    have h1 : 2 * aR = n := by exact_mod_cast hR
    have hτ1 : 1 ≤ τ := by exact_mod_cast hτ
    rcases lt_trichotomy (3 * τ) n with h | h | h
    · have e1 := hα.1 (by exact_mod_cast h)
      have e2 := hβ.1 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      apply nP
      have e1' : aP + aR = 3 * τ := by exact_mod_cast e1
      have e2' : bP + aR = 3 * τ := by exact_mod_cast e2
      exact_mod_cast (show aP = bP by omega)
    · have e1 := hα.2.2 (by exact_mod_cast h)
      have e2 := hβ.2.2 (by exact_mod_cast h)
      rcases min_cases nP mP with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm] at e1
        have : n ≤ τ + aR := by exact_mod_cast e1
        omega
      · rw [hm] at e2
        have : n ≤ τ + aR := by exact_mod_cast e2
        omega
    · have e1 := hα.2.1 (by exact_mod_cast h)
      have e2 := hβ.2.1 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      apply nP
      have e1' : aP + aR = n := by exact_mod_cast e1
      have e2' : bP + aR = n := by exact_mod_cast e2
      exact_mod_cast (show aP = bP by omega)
  · have hτf := hτ' nP mP
    lift τ to ℕ using hτf
    have hτ1 : 1 ≤ τ := by exact_mod_cast hτ
    rcases lt_trichotomy (3 * τ) n with h | h | h
    · have e1 := hα.1 (by exact_mod_cast h)
      have e2 := hβ.1 (by exact_mod_cast h)
      have e3 := (sP nP).1 (by exact_mod_cast h)
      have e4 := (sR nR).1 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      have e1' : aP + aR = 3 * τ := by exact_mod_cast e1
      have e3' : aP + bP = 3 * τ := by exact_mod_cast e3
      have e4' : aR + bR = 3 * τ := by exact_mod_cast e4
      rw [show aR = bP by omega, show bR = aP by omega,
        iotaN_swap (fun h => absurd h nP), add_neg_cancel]
    · rcases min_cases nP mP with ⟨hmP, hlP⟩ | ⟨hmP, hlP⟩ <;>
        rcases min_cases nR mR with ⟨hmR, hlR⟩ | ⟨hmR, hlR⟩
      · have e1 := hα.2.2 (by exact_mod_cast h)
        rw [hmP, hmR] at e1
        have : n ≤ τ + τ := by exact_mod_cast e1
        omega
      · rw [iotaN_of_lt (hmP ▸ hlP), iotaN_of_le (hmR ▸ hlR).le, hmP, hmR, neg_add_cancel]
      · rw [iotaN_of_le (hmP ▸ hlP).le, iotaN_of_lt (hmR ▸ hlR), hmP, hmR, add_neg_cancel]
      · have e2 := hβ.2.2 (by exact_mod_cast h)
        rw [hmP, hmR] at e2
        have : n ≤ τ + τ := by exact_mod_cast e2
        omega
    · have e1 := hα.2.1 (by exact_mod_cast h)
      have e2 := hβ.2.1 (by exact_mod_cast h)
      have e3 := (sP nP).2 (by exact_mod_cast h)
      have e4 := (sR nR).2 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      have e1' : aP + aR = n := by exact_mod_cast e1
      have e3' : aP + bP = n := by exact_mod_cast e3
      have e4' : aR + bR = n := by exact_mod_cast e4
      rw [show aR = bP by omega, show bR = aP by omega,
        iotaN_swap (fun h => absurd h nP), add_neg_cancel]

theorem iotaN_three {n : ℕ} {N a₁ b₁ m₁ a₂ b₂ m₂ a₃ b₃ m₃ : ℕ∞} (hN : 1 ≤ N)
    (c₁ : (a₁ < b₁ ∧ a₁ = N ∧ m₁ = N) ∨ (b₁ ≤ a₁ ∧ b₁ = min m₁ N))
    (c₂ : (a₂ < b₂ ∧ a₂ = N ∧ m₂ = N) ∨ (b₂ ≤ a₂ ∧ b₂ = min m₂ N))
    (c₃ : (a₃ < b₃ ∧ a₃ = N ∧ m₃ = N) ∨ (b₃ ≤ a₃ ∧ b₃ = min m₃ N))
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hm₃ : 1 ≤ m₃)
    (s₁ : a₁ < b₁ → (n : ℕ∞) < 3 * N → a₁ + b₁ = n)
    (s₂ : a₂ < b₂ → (n : ℕ∞) < 3 * N → a₂ + b₂ = n)
    (s₃ : a₃ < b₃ → (n : ℕ∞) < 3 * N → a₃ + b₃ = n)
    (hsm : 2 * N < n → m₁ + m₂ + m₃ = 2 * N)
    (hsb : (3 * N < n → b₁ + b₂ + b₃ = 3 * N) ∧ ((n : ℕ∞) < 3 * N → b₁ + b₂ + b₃ = n) ∧
      (3 * N = n → (n : ℕ∞) ≤ b₁ + b₂ + b₃)) :
    iotaN n a₁ b₁ + iotaN n a₂ b₂ + iotaN n a₃ b₃ = 0 := by
  rcases lt_or_ge (n : ℕ∞) (3 * N) with hlt | hge
  ·
    have e := hsb.2.1 hlt
    have hb : ∀ {b : ℕ∞}, b ≤ b₁ + b₂ + b₃ → b ≠ ⊤ := fun h ht => by
      rw [e, ht] at h; simp at h
    have key : ∀ {a b m : ℕ∞}, ((a < b ∧ a = N ∧ m = N) ∨ (b ≤ a ∧ b = min m N)) →
        (a < b → (n : ℕ∞) < 3 * N → a + b = n) → b ≠ ⊤ → iotaN n a b = ((b.toNat : ℕ) : ZMod n) := by
      intro a b m c s hbt
      rcases c with ⟨hab, ha, -⟩ | ⟨hba, -⟩
      · rw [iotaN_of_lt hab]
        have h1 := s hab hlt
        have hat : a ≠ ⊤ := hab.ne_top
        lift a to ℕ using hat
        lift b to ℕ using hbt
        simp only [ENat.toNat_natCast]
        have h2 : a + b = n := by exact_mod_cast h1
        rw [neg_eq_iff_add_eq_zero, ← Nat.cast_add, show a + b = n by omega, ZMod.natCast_self]
      · rw [iotaN_of_le hba]
    have hb₁ : b₁ ≠ ⊤ := hb (by rw [add_assoc]; exact le_self_add)
    have hb₂ : b₂ ≠ ⊤ := hb (by rw [add_comm b₁, add_assoc]; exact le_self_add)
    have hb₃ : b₃ ≠ ⊤ := hb le_add_self
    rw [key c₁ s₁ hb₁, key c₂ s₂ hb₂, key c₃ s₃ hb₃]
    lift b₁ to ℕ using hb₁
    lift b₂ to ℕ using hb₂
    lift b₃ to ℕ using hb₃
    simp only [ENat.toNat_natCast]
    have : b₁ + b₂ + b₃ = n := by exact_mod_cast e
    rw [← Nat.cast_add, ← Nat.cast_add, this, ZMod.natCast_self]
  · have hNt : N ≠ ⊤ := by rintro rfl; simp at hge
    lift N to ℕ using hNt
    have hN1 : 1 ≤ N := by exact_mod_cast hN
    have h3 : 3 * N ≤ n := by exact_mod_cast hge
    have em := hsm (by exact_mod_cast (show 2 * N < n by omega))
    have hm₁t : m₁ ≠ ⊤ := by rintro rfl; simp at em; exact absurd em (top_ne_two_mul N)
    have hm₂t : m₂ ≠ ⊤ := by rintro rfl; simp at em; exact absurd em (top_ne_two_mul N)
    have hm₃t : m₃ ≠ ⊤ := by rintro rfl; simp at em; exact absurd em (top_ne_two_mul N)
    lift m₁ to ℕ using hm₁t
    lift m₂ to ℕ using hm₂t
    lift m₃ to ℕ using hm₃t
    have em' : m₁ + m₂ + m₃ = 2 * N := by exact_mod_cast em
    have h1 : 1 ≤ m₁ := by exact_mod_cast hm₁
    have h2 : 1 ≤ m₂ := by exact_mod_cast hm₂
    have h3' : 1 ≤ m₃ := by exact_mod_cast hm₃
    have hb3 : 3 * N ≤ b₁ + b₂ + b₃ := by
      rcases lt_or_eq_of_le h3 with h | h
      · rw [hsb.1 (by exact_mod_cast h)]
      · have := hsb.2.2 (by exact_mod_cast h)
        rw [← h] at this; exact_mod_cast this
    have mincast : ∀ m : ℕ, min (m : ℕ∞) (N : ℕ∞) = ((min m N : ℕ) : ℕ∞) := fun m => by
      norm_cast
    rcases c₁ with ⟨l₁, a₁e, m₁e⟩ | ⟨l₁, b₁e⟩ <;> rcases c₂ with ⟨l₂, a₂e, m₂e⟩ | ⟨l₂, b₂e⟩ <;>
      rcases c₃ with ⟨l₃, a₃e, m₃e⟩ | ⟨l₃, b₃e⟩
    · have : m₁ = N := by exact_mod_cast m₁e
      have : m₂ = N := by exact_mod_cast m₂e
      omega
    · have : m₁ = N := by exact_mod_cast m₁e
      have : m₂ = N := by exact_mod_cast m₂e
      omega
    · have : m₁ = N := by exact_mod_cast m₁e
      have : m₃ = N := by exact_mod_cast m₃e
      omega
    · have hm1 : m₁ = N := by exact_mod_cast m₁e
      rw [iotaN_of_lt l₁, iotaN_of_le l₂, iotaN_of_le l₃, a₁e, b₂e, b₃e, mincast, mincast]
      simp only [ENat.toNat_natCast]
      rw [show min m₂ N = m₂ by omega, show min m₃ N = m₃ by omega, add_assoc, neg_add_eq_zero,
        ← Nat.cast_add, show m₂ + m₃ = N by omega]
    · have : m₂ = N := by exact_mod_cast m₂e
      have : m₃ = N := by exact_mod_cast m₃e
      omega
    · have hm2 : m₂ = N := by exact_mod_cast m₂e
      rw [iotaN_of_le l₁, iotaN_of_lt l₂, iotaN_of_le l₃, a₂e, b₁e, b₃e, mincast, mincast]
      simp only [ENat.toNat_natCast]
      rw [show min m₁ N = m₁ by omega, show min m₃ N = m₃ by omega, add_right_comm,
        add_neg_eq_zero, ← Nat.cast_add, show m₁ + m₃ = N by omega]
    · have hm3 : m₃ = N := by exact_mod_cast m₃e
      rw [iotaN_of_le l₁, iotaN_of_le l₂, iotaN_of_lt l₃, a₃e, b₁e, b₂e, mincast, mincast]
      simp only [ENat.toNat_natCast]
      rw [show min m₁ N = m₁ by omega, show min m₂ N = m₂ by omega, add_neg_eq_zero,
        ← Nat.cast_add, show m₁ + m₂ = N by omega]
    · exfalso
      rw [b₁e, b₂e, b₃e, mincast, mincast, mincast] at hb3
      have : 3 * N ≤ min m₁ N + min m₂ N + min m₃ N := by exact_mod_cast hb3
      omega

section Val

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {π : 𝒪}
  (hπ : Irreducible π)

local notation "v" => addVal 𝒪

theorem v_unit {u : 𝒪} (hu : IsUnit u) : v u = 0 := addVal_eq_zero_iff.2 hu

theorem v_mul_unit_left {u a : 𝒪} (hu : IsUnit u) : v (u * a) = v a := by
  rw [addVal_mul, v_unit hu, zero_add]

theorem v_ne_top {a : 𝒪} (ha : a ≠ 0) : v a ≠ ⊤ := fun h => ha (addVal_eq_top_iff.1 h)

theorem v_cube (a : 𝒪) : v (a ^ 3) = 3 * v a := by
  rw [addVal_pow, nsmul_eq_mul]; rfl

include hπ in
theorem one_le_v_iff {a : 𝒪} : 1 ≤ v a ↔ π ∣ a := by
  rw [← addVal_uniformizer hπ, addVal_le_iff_dvd]

theorem v_cube_add (z q : 𝒪) :
    (3 * v z < v q → v (z ^ 3 + q) = 3 * v z) ∧ (v q < 3 * v z → v (z ^ 3 + q) = v q) ∧
      (3 * v z = v q → v q ≤ v (z ^ 3 + q)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [AddValuation.map_add_eq_of_lt_left _ (by rwa [v_cube]), v_cube]
  · rw [AddValuation.map_add_eq_of_lt_right _ (by rwa [v_cube])]
  · have := AddValuation.map_add (addVal 𝒪) (z ^ 3) q
    rwa [v_cube, h, min_self] at this

variable {e q : 𝒪}

theorem v_sum_eq {x y : 𝒪} (h : y * (y + e * x) = x ^ 3 + q) : v y + v (y + e * x) = v (x ^ 3 + q) := by
  rw [← addVal_mul, h]

theorem v_x_of {x y : 𝒪} (he : IsUnit e) :
    min (v y) (v (y + e * x)) ≤ v x ∧ (v y ≠ v (y + e * x) → v x = min (v y) (v (y + e * x))) := by
  have hx : v x = v ((y + e * x) + -y) := by
    rw [show (y + e * x) + -y = e * x by ring, v_mul_unit_left he]
  refine ⟨?_, fun hne => ?_⟩
  · rw [hx, min_comm]
    have := AddValuation.map_add (addVal 𝒪) (y + e * x) (-y)
    rwa [AddValuation.map_neg] at this
  · rw [hx, AddValuation.map_add_of_distinct_val _ (by rwa [AddValuation.map_neg, ne_comm]),
      AddValuation.map_neg, min_comm]

include hπ in

theorem tie_two {x y : 𝒪} (he : IsUnit e) (hq : q ≠ 0) (h : y * (y + e * x) = x ^ 3 + q)
    (dy : π ∣ y) (ht : v y = v (y + e * x)) : 2 * v y = v q := by
  have hs := v_sum_eq h
  obtain ⟨hmin, -⟩ := v_x_of (x := x) (y := y) he
  rw [← ht, min_self] at hmin
  rw [← ht] at hs
  have hy1 : 1 ≤ v y := (one_le_v_iff hπ).2 dy
  have hqt := v_ne_top hq
  obtain ⟨c1, c2, c3⟩ := v_cube_add x q
  rcases lt_trichotomy (3 * v x) (v q) with h3 | h3 | h3
  · exfalso
    rw [c1 h3] at hs
    have hxt : v x ≠ ⊤ := by
      rintro hx; rw [hx] at h3; simp at h3
    have hyt : v y ≠ ⊤ := ne_top_of_le_ne_top hxt hmin
    lift v x to ℕ using hxt with m hm
    lift v y to ℕ using hyt with a ha
    have e1 : a + a = 3 * m := by exact_mod_cast hs
    have e2 : a ≤ m := by exact_mod_cast hmin
    have e3 : 1 ≤ a := by exact_mod_cast hy1
    omega
  · exfalso
    have hs' := c3 h3
    rw [← hs, ← h3] at hs'
    have hxt : v x ≠ ⊤ := by
      rintro hx; rw [hx] at h3; exact hqt (by rw [← h3]; simp)
    have hyt : v y ≠ ⊤ := ne_top_of_le_ne_top hxt hmin
    lift v x to ℕ using hxt with m hm
    lift v y to ℕ using hyt with a ha
    have e1 : 3 * m ≤ a + a := by exact_mod_cast hs'
    have e2 : a ≤ m := by exact_mod_cast hmin
    have e3 : 1 ≤ a := by exact_mod_cast hy1
    omega
  · rw [c2 h3] at hs
    rw [two_mul, hs]

end Val

section Alg

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {π : 𝒪}
  (hπ : Irreducible π)

local notation "v" => addVal 𝒪

variable {e q : 𝒪}

theorem v_sq (a : 𝒪) : v (a ^ 2) = v a + v a := by rw [pow_two, addVal_mul]

include hπ in

theorem iota_pair {μ l l' ρ ρ' U U' xP yP xR yR : 𝒪} (he : IsUnit e) (hq : q ≠ 0)
    (hl : IsUnit l) (hl' : IsUnit l') (hU : IsUnit U) (hU' : IsUnit U') (hμ : μ ≠ 0)
    (eP : yP * (yP + e * xP) = xP ^ 3 + q) (eR : yR * (yR + e * xR) = xR ^ 3 + q)
    (dxP : π ∣ xP) (dyP : π ∣ yP) (dyR : π ∣ yR)
    (lP : μ * yP = l * (xP + ρ)) (lP' : μ * (yP + e * xP) = l' * (xP + ρ'))
    (lR : μ * yR = l * (xR + ρ)) (lR' : μ * (yR + e * xR) = l' * (xR + ρ'))
    (pα : μ ^ 2 * (q - ρ ^ 3) = (xP + ρ) * (xR + ρ) * U)
    (pβ : μ ^ 2 * (q - ρ' ^ 3) = (xP + ρ') * (xR + ρ') * U')
    (hll : l' - l = e * μ) (hρρ : l * ρ = l' * ρ') :
    iotaN (v q).toNat (v yP) (v (yP + e * xP)) + iotaN (v q).toNat (v yR) (v (yR + e * xR)) = 0 := by
  have hn : v q = ((v q).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq)).symm
  set n := (v q).toNat
  have hf : v μ ≠ ⊤ := v_ne_top hμ
  have hD : ∀ {x y : 𝒪}, μ * y = l * (x + ρ) → v (x + ρ) = v μ + v y := fun h => by
    rw [← addVal_mul, h, v_mul_unit_left hl]
  have hD' : ∀ {x y : 𝒪}, μ * (y + e * x) = l' * (x + ρ') → v (x + ρ') = v μ + v (y + e * x) :=
    fun h => by rw [← addVal_mul, h, v_mul_unit_left hl']
  have hρ' : v ρ' = v ρ := by
    have := congrArg v hρρ
    rwa [v_mul_unit_left hl, v_mul_unit_left hl', eq_comm] at this
  have hdiff : v ((xP + ρ) + -(xP + ρ')) = v μ + v ρ := by
    have h1 : l * ((xP + ρ) + -(xP + ρ')) = e * (μ * ρ') := by linear_combination hρρ + ρ' * hll
    have := congrArg v h1
    rwa [v_mul_unit_left hl, v_mul_unit_left he, addVal_mul, hρ'] at this
  have hdiffR : v ((xR + ρ) + -(xR + ρ')) = v μ + v ρ := by
    rw [show (xR + ρ) + -(xR + ρ') = (xP + ρ) + -(xP + ρ') by ring, hdiff]
  have hτ1 : 1 ≤ v ρ := by
    rw [one_le_v_iff hπ]
    have h1 : π ∣ l * (xP + ρ) := by rw [← lP]; exact dvd_mul_of_dvd_right dyP μ
    have h2 : π ∣ xP + ρ := (hl.dvd_mul_left).1 h1
    have := dvd_sub h2 dxP
    rwa [add_sub_cancel_left] at this

  have cls : ∀ {x y : 𝒪}, y * (y + e * x) = x ^ 3 + q → π ∣ y → μ * y = l * (x + ρ) →
      μ * (y + e * x) = l' * (x + ρ') → v ((x + ρ) + -(x + ρ')) = v μ + v ρ →
      (v y = v (y + e * x) ∧ 2 * v y = n) ∨
        (v y ≠ v (y + e * x) ∧ min (v y) (v (y + e * x)) = v ρ) := by
    intro x y h dy l1 l2 hd
    by_cases ht : v y = v (y + e * x)
    · exact Or.inl ⟨ht, by rw [tie_two hπ he hq h dy ht, hn]⟩
    · refine Or.inr ⟨ht, ?_⟩
      have hne : v (x + ρ) ≠ v (-(x + ρ')) := by
        rw [AddValuation.map_neg, hD l1, hD' l2]
        exact fun h' => ht (ENat.add_right_injective_of_ne_top hf h')
      rw [AddValuation.map_add_of_distinct_val _ hne, AddValuation.map_neg, hD l1, hD' l2,
        min_add_add_left] at hd
      exact ENat.add_right_injective_of_ne_top hf hd
  have sums : ∀ {x y : 𝒪}, y * (y + e * x) = x ^ 3 + q →
      min (v y) (v (y + e * x)) = v ρ → v y ≠ v (y + e * x) →
      (3 * v ρ < n → v y + v (y + e * x) = 3 * v ρ) ∧ (n < 3 * v ρ → v y + v (y + e * x) = n) := by
    intro x y h hm hne
    have hx := (v_x_of (x := x) (y := y) he).2 hne
    rw [hm] at hx
    obtain ⟨c1, c2, -⟩ := v_cube_add x q
    rw [hn] at c1 c2
    rw [v_sum_eq h, ← hx]
    exact ⟨c1, c2⟩
  have prod : ∀ {r : 𝒪} {W : 𝒪}, IsUnit W → μ ^ 2 * (q - r ^ 3) = (xP + r) * (xR + r) * W →
      v (q - r ^ 3) + (v μ + v μ) = v (xP + r) + v (xR + r) := by
    intro r W hW h
    have := congrArg v h
    rw [addVal_mul, addVal_mul, addVal_mul, v_unit hW, add_zero, v_sq, add_comm] at this
    exact this
  have hα := prod hU pα
  have hβ := prod hU' pβ
  rw [hD lP, hD lR] at hα
  rw [hD' lP', hD' lR'] at hβ
  have h2f : v μ + v μ ≠ ⊤ := by
    rw [Ne, ENat.add_eq_top]; exact fun h => h.elim hf hf
  have hα' : v (q - ρ ^ 3) = v yP + v yR := by
    apply ENat.add_left_injective_of_ne_top h2f
    show v (q - ρ ^ 3) + (v μ + v μ) = (v yP + v yR) + (v μ + v μ)
    rw [hα]; ring
  have hβ' : v (q - ρ' ^ 3) = v (yP + e * xP) + v (yR + e * xR) := by
    apply ENat.add_left_injective_of_ne_top h2f
    show v (q - ρ' ^ 3) + (v μ + v μ) = (v (yP + e * xP) + v (yR + e * xR)) + (v μ + v μ)
    rw [hβ]; ring
  have cube : ∀ r : 𝒪, (3 * v r < n → v (q - r ^ 3) = 3 * v r) ∧ (n < 3 * v r → v (q - r ^ 3) = n) ∧
      (3 * v r = n → n ≤ v (q - r ^ 3)) := by
    intro r
    have h := v_cube_add (-r) q
    rw [AddValuation.map_neg, show (-r) ^ 3 + q = q - r ^ 3 by ring, hn] at h
    exact h
  refine iotaN_two hτ1 (cls eP dyP lP lP' hdiff) (cls eR dyR lR lR' hdiffR)
    (fun hne => sums eP (((cls eP dyP lP lP' hdiff).resolve_left fun h => hne h.1).2) hne)
    (fun hne => sums eR (((cls eR dyR lR lR' hdiffR).resolve_left fun h => hne h.1).2) hne)
    ?_ ?_
  · rw [← hα']; exact cube ρ
  · have hc := cube ρ'
    rw [hρ'] at hc
    rw [← hβ']; exact hc

include hπ in

theorem point_kind {ℓ ν x y : 𝒪} (hq : q ≠ 0) (hℓ : π ∣ ℓ) (hℓe : IsUnit (ℓ + e))
    (h : y * (y + e * x) = x ^ 3 + q) (l : y = ℓ * x + ν) :
    (v y < v (y + e * x) ∧ v y = v ν ∧ v x = v ν) ∨
      (v (y + e * x) ≤ v y ∧ v (y + e * x) = min (v x) (v ν)) := by
  have hw : y + e * x = (ℓ + e) * x + ν := by rw [l]; ring
  have hwx : v ((ℓ + e) * x) = v x := v_mul_unit_left hℓe
  have hℓx : v x + 1 ≤ v (ℓ * x) := by
    rw [addVal_mul, add_comm]; exact add_le_add_left ((one_le_v_iff hπ).2 hℓ) _
  rw [hw, l]
  rcases lt_trichotomy (v x) (v ν) with hm | hm | hm
  · have hxt : v x ≠ ⊤ := hm.ne_top
    have hb : v ((ℓ + e) * x + ν) = v x := by
      rw [AddValuation.map_add_eq_of_lt_left _ (by rwa [hwx]), hwx]
    have ha : v x < v (ℓ * x + ν) := by
      have hlt : v x < v (ℓ * x) := lt_of_lt_of_le (ENat.lt_add_one_iff hxt |>.2 le_rfl) hℓx
      exact lt_of_lt_of_le (lt_min hlt hm) (AddValuation.map_add _ _ _)
    right
    rw [hb, min_eq_left hm.le]
    exact ⟨ha.le, rfl⟩
  · have hNt : v x ≠ ⊤ := by
      intro ht
      have hx0 : x = 0 := addVal_eq_top_iff.1 ht
      have hν0 : ν = 0 := addVal_eq_top_iff.1 (hm ▸ ht)
      subst hx0 hν0
      apply hq
      rw [l] at h
      simpa [eq_comm] using h
    have ha : v (ℓ * x + ν) = v ν := by
      rw [AddValuation.map_add_eq_of_lt_right]
      rw [← hm]
      exact lt_of_lt_of_le (ENat.lt_add_one_iff hNt |>.2 le_rfl) hℓx
    have hb : v ν ≤ v ((ℓ + e) * x + ν) := by
      have := AddValuation.map_add (addVal 𝒪) ((ℓ + e) * x) ν
      rwa [hwx, hm, min_self] at this
    rcases eq_or_lt_of_le hb with hb' | hb'
    · right
      rw [← hb', ha, hm, min_self]
      exact ⟨le_rfl, rfl⟩
    · left
      rw [ha]
      exact ⟨hb', rfl, hm⟩
  · have hb : v ((ℓ + e) * x + ν) = v ν := by
      rw [AddValuation.map_add_eq_of_lt_right _ (by rwa [hwx])]
    have ha : v (ℓ * x + ν) = v ν := by
      rw [AddValuation.map_add_eq_of_lt_right]
      exact lt_of_lt_of_le hm (le_trans le_self_add hℓx)
    right
    rw [hb, ha, min_eq_right hm.le]
    exact ⟨le_rfl, rfl⟩

include hπ in

theorem iota_triple {ℓ ν x₁ y₁ x₂ y₂ x₃ y₃ : 𝒪} (hq : q ≠ 0) (hℓ : π ∣ ℓ)
    (hℓe : IsUnit (ℓ + e))
    (e₁ : y₁ * (y₁ + e * x₁) = x₁ ^ 3 + q) (e₂ : y₂ * (y₂ + e * x₂) = x₂ ^ 3 + q)
    (e₃ : y₃ * (y₃ + e * x₃) = x₃ ^ 3 + q)
    (dx₁ : π ∣ x₁) (dx₂ : π ∣ x₂) (dx₃ : π ∣ x₃) (dy₁ : π ∣ y₁)
    (l₁ : y₁ = ℓ * x₁ + ν) (l₂ : y₂ = ℓ * x₂ + ν) (l₃ : y₃ = ℓ * x₃ + ν)
    (hv3 : x₁ * x₂ * x₃ = ν ^ 2 - q)
    (hvw : (y₁ + e * x₁) * (y₂ + e * x₂) * (y₃ + e * x₃) = ν ^ 3 - (ℓ + e) ^ 3 * q) :
    iotaN (v q).toNat (v y₁) (v (y₁ + e * x₁)) + iotaN (v q).toNat (v y₂) (v (y₂ + e * x₂)) +
      iotaN (v q).toNat (v y₃) (v (y₃ + e * x₃)) = 0 := by
  have hn : v q = ((v q).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq)).symm
  set n := (v q).toNat
  have hN : 1 ≤ v ν := by
    rw [one_le_v_iff hπ]
    have : ν = y₁ - ℓ * x₁ := by rw [l₁]; ring
    rw [this]; exact dvd_sub dy₁ (dvd_mul_of_dvd_left hℓ _)
  have sA : ∀ {x y : 𝒪}, y * (y + e * x) = x ^ 3 + q →
      (v y < v (y + e * x) ∧ v y = v ν ∧ v x = v ν) ∨
        (v (y + e * x) ≤ v y ∧ v (y + e * x) = min (v x) (v ν)) →
      v y < v (y + e * x) → (n : ℕ∞) < 3 * v ν → v y + v (y + e * x) = n := by
    intro x y h c hlt hn3
    rcases c with ⟨-, -, hx⟩ | ⟨hle, -⟩
    · rw [v_sum_eq h, (v_cube_add x q).2.1 (by rw [hx, hn]; exact hn3), hn]
    · exact absurd hle (not_le.2 hlt)
  have k₁ := point_kind hπ hq hℓ hℓe e₁ l₁
  have k₂ := point_kind hπ hq hℓ hℓe e₂ l₂
  have k₃ := point_kind hπ hq hℓ hℓe e₃ l₃
  refine iotaN_three hN k₁ k₂ k₃ ((one_le_v_iff hπ).2 dx₁) ((one_le_v_iff hπ).2 dx₂)
    ((one_le_v_iff hπ).2 dx₃) (sA e₁ k₁) (sA e₂ k₂) (sA e₃ k₃) ?_ ?_
  · intro h2
    rw [← addVal_mul, ← addVal_mul, hv3, sub_eq_add_neg,
      AddValuation.map_add_eq_of_lt_left _ (by rwa [AddValuation.map_neg, v_sq, ← two_mul, hn]),
      v_sq, two_mul]
  · rw [← addVal_mul, ← addVal_mul, hvw]
    have hq3 : v ((ℓ + e) ^ 3 * q) = n := by
      rw [addVal_mul, show (ℓ + e) ^ 3 = (ℓ + e) ^ 3 by rfl, v_unit (hℓe.pow 3), zero_add, hn]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [sub_eq_add_neg, AddValuation.map_add_eq_of_lt_left _ (by rwa [AddValuation.map_neg, hq3,
        v_cube]), v_cube]
    · rw [sub_eq_add_neg, AddValuation.map_add_eq_of_lt_right _ (by rwa [AddValuation.map_neg, hq3,
        v_cube]), AddValuation.map_neg, hq3]
    · have := AddValuation.map_sub (addVal 𝒪) (ν ^ 3) ((ℓ + e) ^ 3 * q)
      rwa [v_cube, hq3, h, min_self] at this

end Alg

end

end GroundTheory.Arith.Abelian
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing IsDiscreteValuationRing

noncomputable section

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic]

local notation "ι" => algebraMap 𝒪 K
local notation "v" => addVal 𝒪

def iotaPt : (curveK K W).Point → ZMod (v W.a₆).toNat
  | 0 => 0
  | .some X Y _ => iotaN (v W.a₆).toNat (v (intPart K Y)) (v (intPart K Y + W.a₁ * intPart K X))

open Classical in

def phiT (P : (curveK K W).Point) : ZMod (v W.a₆).toNat :=
  if P ∈ E0Set K W then 0 else iotaPt K W P

theorem phiT_of_mem {P : (curveK K W).Point} (h : P ∈ E0Set K W) : phiT K W P = 0 := by
  simp [phiT, h]

theorem phiT_some {x y : 𝒪} (h : (curveK K W).Nonsingular (ι x) (ι y))
    (hP : Point.some _ _ h ∉ E0Set K W) :
    phiT K W (.some _ _ h) = iotaN (v W.a₆).toNat (v y) (v (y + W.a₁ * x)) := by
  simp only [phiT, hP, if_false, iotaPt, intPart_algebraMap]

variable {π : 𝒪} (hπ : Irreducible π)

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in
include hπ in
theorem isUnit_iff_not_dvd {a : 𝒪} : IsUnit a ↔ ¬π ∣ a := by
  rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, mem_maximalIdeal, mem_nonunits_iff,
    not_not]

theorem natCast_ne_zero_of_lt {n b : ℕ} (h1 : 1 ≤ b) (h2 : b < n) : ((b : ℕ) : ZMod n) ≠ 0 := by
  intro h
  rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
  exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

section Hensel

include hπ

theorem exists_root_cubic {α β γ δ : 𝒪} (hγ : IsUnit γ) (hδ : π ∣ δ) :
    ∃ Z, π ∣ Z ∧ α * Z ^ 3 + β * Z ^ 2 + γ * Z + δ = 0 := by
  open Polynomial in
  have hm : ∀ {a : 𝒪}, π ∣ a → a ∈ IsLocalRing.maximalIdeal 𝒪 := fun {a} h => by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]; exact h
  have hu : ∀ {a : 𝒪}, IsUnit a → ∀ {b : 𝒪}, π ∣ b → IsUnit (a + b) := fun {a} ha {b} hb => by
    rw [isUnit_iff_not_dvd hπ] at ha ⊢
    intro h; exact ha (by have := dvd_sub h hb; rwa [add_sub_cancel_right] at this)
  obtain ⟨c1, hc1⟩ : ∃ c, c = β * δ := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c, c = α * δ ^ 2 := ⟨_, rfl⟩
  set f : Polynomial 𝒪 := X ^ 3 + C γ * X ^ 2 + C c1 * X + C c0 with hfdef
  have hf : f.Monic := by rw [hfdef]; monicity!
  have hev : ∀ V : 𝒪, f.eval V = V ^ 3 + γ * V ^ 2 + β * δ * V + α * δ ^ 2 := fun V => by
    simp [hfdef, hc0, hc1]
  have hder : ∀ V : 𝒪, f.derivative.eval V = 3 * V ^ 2 + 2 * γ * V + β * δ := fun V => by
    simp [hfdef, hc1]; ring
  obtain ⟨V, hV, hVm⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal 𝒪) f hf (-γ)
    (by
      rw [hev]
      apply hm
      rw [show (-γ) ^ 3 + γ * (-γ) ^ 2 + β * δ * -γ + α * δ ^ 2 = δ * (-β * γ + α * δ) by ring]
      exact dvd_mul_of_dvd_left hδ _)
    (by
      rw [hder]
      apply IsUnit.map
      rw [show 3 * (-γ) ^ 2 + 2 * γ * -γ + β * δ = γ ^ 2 + β * δ by ring]
      exact hu (hγ.pow 2) (dvd_mul_of_dvd_right hδ β))
  have hV' : V ^ 3 + γ * V ^ 2 + β * δ * V + α * δ ^ 2 = 0 := by rw [← hev]; exact hV
  have hVu : IsUnit V := by
    have h1 : π ∣ V - -γ := by
      rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hVm
    have := hu (hγ.neg) h1
    convert this using 1; ring
  obtain ⟨Wv, hWv⟩ : ∃ Wv, V * Wv = 1 := ⟨_, hVu.mul_val_inv⟩
  refine ⟨δ * Wv, dvd_mul_of_dvd_left hδ _, ?_⟩
  linear_combination (δ * Wv ^ 3) * hV' -
    (β * δ ^ 2 * Wv ^ 2 + γ * δ * Wv * (V * Wv + 1) + δ * ((V * Wv) ^ 2 + V * Wv + 1)) * hWv

end Hensel

theorem zmod_two_eq_one {N : ℕ} (hN : N = 2) {z : ZMod N} (hz : z ≠ 0) : z = 1 := by
  subst hN
  fin_cases z
  · exact absurd rfl hz
  · rfl

section Hom

variable {W} (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (he : IsUnit W.a₁)
  (hq : π ∣ W.a₆)
include h2 h3 h4

omit [DecidableEq K] [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [(W.map (algebraMap 𝒪 K)).IsElliptic] in
theorem tate_eq {x y : 𝒪} (h : W.toAffine.Equation x y) :
    y * (y + W.a₁ * x) = x ^ 3 + W.a₆ := by
  rw [equation_iff, h2, h3, h4] at h
  linear_combination h

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
include K in
theorem a₆_ne_zero : W.a₆ ≠ 0 := by
  intro h0
  apply Δ_ne_zero_of_isElliptic K W
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h2, h3, h4, h0]
  ring

include hπ hq he

theorem phiT_neg (P : (curveK K W).Point) : phiT K W (-P) = -phiT K W P := by
  by_cases hP : P ∈ E0Set K W
  · rw [phiT_of_mem K W hP, phiT_of_mem K W (show -P ∈ E0 K W from (E0 K W).neg_mem hP),
      neg_zero]
  obtain ⟨x, y, h, rfl, e, dx, dy⟩ :=
    exists_of_notMem_E0Set K W hπ (by rw [h3]; exact dvd_zero _) (by rw [h4]; exact dvd_zero _) hq hP
  obtain ⟨hn, hneg⟩ := neg_some_integral K W h
  have hP' := neg_notMem_E0Set K W hP
  rw [hneg] at hP' ⊢
  rw [phiT_some K W h hP, phiT_some K W hn hP', h3, sub_zero,
    show -y - W.a₁ * x + W.a₁ * x = -y by ring, AddValuation.map_neg,
    show -y - W.a₁ * x = -(y + W.a₁ * x) by ring, AddValuation.map_neg]
  exact iotaN_swap fun ht => by
    rw [tie_two hπ he (a₆_ne_zero K h2 h3 h4) (tate_eq h2 h3 h4 e) dy ht,
      ENat.natCast_toNat (v_ne_top (a₆_ne_zero K h2 h3 h4))]

include K in

theorem iota_neg_data {x y : 𝒪} (e' : W.toAffine.Equation x y) (dy : π ∣ y) :
    iotaN (v W.a₆).toNat (v (-(y + W.a₁ * x))) (v (-(y + W.a₁ * x) + W.a₁ * x)) =
      -iotaN (v W.a₆).toNat (v y) (v (y + W.a₁ * x)) := by
  rw [AddValuation.map_neg, show -(y + W.a₁ * x) + W.a₁ * x = -y by ring, AddValuation.map_neg]
  exact iotaN_swap fun ht => by
    rw [tie_two hπ he (a₆_ne_zero K h2 h3 h4) (tate_eq h2 h3 h4 e') dy ht,
      ENat.natCast_toNat (v_ne_top (a₆_ne_zero K h2 h3 h4))]

theorem phiT_three {P Q R : (curveK K W).Point} (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W)
    (hR : R ∉ E0Set K W) (hs : P + Q + R = 0) : phiT K W P + phiT K W Q + phiT K W R = 0 := by
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩, ⟨g₃, rfl⟩, e₁, e₂, e₃, dx₁, dy₁, dx₂,
    dy₂, dx₃, dy₃, l1, l2, l3, v1, v2, v3⟩ := triple_origin K W hπ d3 d4 hq hP hQ hR hs
  rw [phiT_some K W g₁ hP, phiT_some K W g₂ hQ, phiT_some K W g₃ hR]
  have hq0 := a₆_ne_zero K h2 h3 h4
  rw [h2] at v1
  rw [h3, h4] at v2
  rw [h3] at v3
  have E₁ := tate_eq h2 h3 h4 e₁
  have E₂ := tate_eq h2 h3 h4 e₂
  have E₃ := tate_eq h2 h3 h4 e₃
  have hv3 : x₁ * x₂ * x₃ = ν ^ 2 - W.a₆ := by linear_combination v3
  have hσ : π ∣ ℓ * (ℓ + W.a₁) := by
    rw [show ℓ * (ℓ + W.a₁) = x₁ + x₂ + x₃ by linear_combination -v1]
    exact dvd_add (dvd_add dx₁ dx₂) dx₃
  have hne : ¬π ∣ W.a₁ := (isUnit_iff_not_dvd hπ).1 he
  rcases hπ.prime.dvd_or_dvd hσ with hℓ | hℓe
  · have hu : IsUnit (ℓ + W.a₁) := (isUnit_iff_not_dvd hπ).2 fun h => hne (by
      have := dvd_sub h hℓ; rwa [add_sub_cancel_left] at this)
    have hvw : (y₁ + W.a₁ * x₁) * (y₂ + W.a₁ * x₂) * (y₃ + W.a₁ * x₃) =
        ν ^ 3 - (ℓ + W.a₁) ^ 3 * W.a₆ := by
      rw [l1, l2, l3]
      linear_combination (ℓ + W.a₁) ^ 3 * v3 + (ℓ + W.a₁) ^ 2 * ν * v2 + (ℓ + W.a₁) * ν ^ 2 * v1
    exact iota_triple hπ hq0 hℓ hu E₁ E₂ E₃ dx₁ dx₂ dx₃ dy₁ l1 l2 l3 hv3 hvw
  · have hℓu : IsUnit (-ℓ) := (isUnit_iff_not_dvd hπ).2 fun h => hne (by
      have := dvd_add hℓe h; rwa [show ℓ + W.a₁ + -ℓ = W.a₁ by ring] at this)
    have neg_eq : ∀ {x y : 𝒪}, y * (y + W.a₁ * x) = x ^ 3 + W.a₆ →
        -(y + W.a₁ * x) * (-(y + W.a₁ * x) + W.a₁ * x) = x ^ 3 + W.a₆ := by
      intro x y h; linear_combination h
    have hvw : (-(y₁ + W.a₁ * x₁) + W.a₁ * x₁) * (-(y₂ + W.a₁ * x₂) + W.a₁ * x₂) *
        (-(y₃ + W.a₁ * x₃) + W.a₁ * x₃) = (-ν) ^ 3 - (-(ℓ + W.a₁) + W.a₁) ^ 3 * W.a₆ := by
      rw [l1, l2, l3]
      linear_combination (-ℓ ^ 3) * v3 - ℓ ^ 2 * ν * v2 - ℓ * ν ^ 2 * v1
    have := iota_triple hπ hq0 (ℓ := -(ℓ + W.a₁)) (ν := -ν) (dvd_neg.2 hℓe)
      (by rwa [show -(ℓ + W.a₁) + W.a₁ = -ℓ by ring]) (neg_eq E₁) (neg_eq E₂) (neg_eq E₃) dx₁ dx₂
      dx₃ (dvd_neg.2 (dvd_add dy₁ (dvd_mul_of_dvd_right dx₁ _))) (by rw [l1]; ring) (by rw [l2]; ring)
      (by rw [l3]; ring) (by rw [hv3]; ring) hvw
    rw [iota_neg_data K hπ h2 h3 h4 he hq (equation_of_map K W g₁.1) dy₁,
      iota_neg_data K hπ h2 h3 h4 he hq (equation_of_map K W g₂.1) dy₂,
      iota_neg_data K hπ h2 h3 h4 he hq (equation_of_map K W g₃.1) dy₃] at this
    rw [← neg_eq_zero, neg_add, neg_add]
    exact this

theorem phiT_pair_int {P Q : (curveK K W).Point} {xT yT : 𝒪}
    {hT : (curveK K W).Nonsingular (ι xT) (ι yT)} (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W)
    (hTm : Point.some _ _ hT ∈ E0Set K W) (hs : P + Q + Point.some _ _ hT = 0) :
    phiT K W P + phiT K W Q = 0 := by
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨xP, yP, gP, rfl, eP, dxP, dyP⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hP
  obtain ⟨xQ, yQ, gQ, rfl, eQ, dxQ, dyQ⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hQ
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_integral_line K W gP gQ hT hs
  rw [phiT_some K W gP hP, phiT_some K W gQ hQ]
  rw [h2] at v1
  rw [h3, h4] at v2
  rw [h3] at v3
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hTn : (curveRed W).Nonsingular (residue 𝒪 xT) (residue 𝒪 yT) := hTm xT yT hT rfl
  have hν : π ∣ ν := by
    rw [show ν = yP - ℓ * xP by rw [l1]; ring]
    exact dvd_sub dyP (dvd_mul_of_dvd_right dxP _)
  have hxT : ¬π ∣ xT := by
    intro hx
    have hy : π ∣ yT := by rw [l3]; exact dvd_add (dvd_mul_of_dvd_right hx _) hν
    exact singular_of_dvd_origin W hπ d3 d4 hx hy hTn
  have hprod : ¬π ∣ ℓ * (ℓ + W.a₁) := by
    intro h
    apply hxT
    rw [show xT = ℓ * (ℓ + W.a₁) - xP - xQ by linear_combination v1]
    exact dvd_sub (dvd_sub h dxP) dxQ
  have hℓ : IsUnit ℓ := (isUnit_iff_not_dvd hπ).2 fun h => hprod (dvd_mul_of_dvd_left h _)
  have hℓe : IsUnit (ℓ + W.a₁) := (isUnit_iff_not_dvd hπ).2 fun h => hprod (dvd_mul_of_dvd_right h _)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = ν * ↑hℓ.unit⁻¹ := ⟨_, rfl⟩
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ', ρ' = ν * ↑hℓe.unit⁻¹ := ⟨_, rfl⟩
  have hρ : ℓ * ρ = ν := by
    rw [hρdef, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have hρ' : (ℓ + W.a₁) * ρ' = ν := by
    rw [hρ'def, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have dρ : π ∣ ρ := hρdef ▸ dvd_mul_of_dvd_left hν _
  have dρ' : π ∣ ρ' := hρ'def ▸ dvd_mul_of_dvd_left hν _
  have unitU : ∀ {r : 𝒪}, π ∣ r → IsUnit (-(xT + r)) := fun {r} hr =>
    (isUnit_iff_not_dvd hπ).2 fun h => hxT (by
      have := dvd_sub (dvd_neg.1 h) hr; rwa [add_sub_cancel_right] at this)
  refine iota_pair (μ := 1) (l := ℓ) (l' := ℓ + W.a₁) (ρ := ρ) (ρ' := ρ') (U := -(xT + ρ))
    (U' := -(xT + ρ')) (xP := xP) (yP := yP) (xR := xQ) (yR := yQ)
    hπ he hq0 hℓ hℓe (unitU dρ) (unitU dρ') one_ne_zero (tate_eq h2 h3 h4 eP)
    (tate_eq h2 h3 h4 eQ) dxP dyP dyQ (by rw [l1]; linear_combination -hρ) (by
      rw [l1]; linear_combination -hρ') (by rw [l2]; linear_combination -hρ)
    (by rw [l2]; linear_combination -hρ') ?_ ?_ (by ring) (by rw [hρ, hρ'])
  · linear_combination ρ ^ 2 * v1 + ρ * v2 + v3 + (ℓ * ρ - ν + W.a₁ * ρ) * hρ
  · linear_combination ρ' ^ 2 * v1 + ρ' * v2 + v3 + (ℓ * ρ' - ν) * hρ'

theorem componentIndex_pair_nonintegral {P Q : (curveK K W).Point} {X Y : K} {hT : (curveK K W).Nonsingular X Y}
    (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W) (hX : X ∉ Set.range ι)
    (hs : P + Q + Point.some _ _ hT = 0) : phiT K W P + phiT K W Q = 0 := by
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨xP, yP, gP, rfl, eP, dxP, dyP⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hP
  obtain ⟨xQ, yQ, gQ, rfl, eQ, dxQ, dyQ⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hQ
  obtain ⟨L, N, l1, l2, -, v1, v2, v3⟩ := exists_line_of_add_eq_zero gP gQ hT hs
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, h2, h3, h4, map_zero] at v1 v2 v3
  rw [phiT_some K W gP hP, phiT_some K W gQ hQ]
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hinj := IsFractionRing.injective 𝒪 K
  have hL : L ∉ Set.range ι := by
    rintro ⟨ℓ, rfl⟩
    apply hX
    exact ⟨ℓ ^ 2 + W.a₁ * ℓ - xP - xQ, by
      simp only [map_sub, map_add, map_mul, map_pow]; linear_combination -v1⟩
  obtain ⟨μ, hμm, hμ⟩ := exists_inv_mem_of_notMem_range K hL
  have hL0 : L ≠ 0 := by rintro rfl; exact hL ⟨0, map_zero _⟩
  have hμL : ι μ * L = 1 := by rw [hμ, inv_mul_cancel₀ hL0]
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [map_zero, zero_mul] at hμL; exact zero_ne_one hμL
  have dμ : π ∣ μ := by
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hμm
  obtain ⟨ν', hν'def⟩ : ∃ ν', ν' = μ * yP - xP := ⟨_, rfl⟩
  have hνK : ι ν' = ι μ * N := by
    rw [hν'def, map_sub, map_mul]
    linear_combination (ι μ) * l1 + (ι xP) * hμL
  have lQ : μ * yQ = 1 * (xQ + ν') := by
    apply hinj
    simp only [map_mul, map_add, one_mul]
    rw [hνK]
    linear_combination (ι μ) * l2 + (ι xQ) * hμL
  obtain ⟨T', hTdef⟩ : ∃ T', T' = 1 + W.a₁ * μ - μ ^ 2 * (xP + xQ) := ⟨_, rfl⟩
  have hTK : ι T' = (ι μ) ^ 2 * X := by
    rw [hTdef]
    simp only [map_sub, map_add, map_mul, map_pow, map_one]
    linear_combination (-(ι μ * L + 1) - ι W.a₁ * ι μ) * hμL - (ι μ) ^ 2 * v1
  have S2 : μ ^ 2 * (xP * xQ) + T' * (xP + xQ) = -(2 + W.a₁ * μ) * ν' := by
    apply hinj
    simp only [map_mul, map_add, map_neg, map_pow, map_ofNat]
    rw [hTK, hνK]
    linear_combination (ι μ) ^ 2 * v2 - 2 * ι μ * N * hμL
  have S3 : xP * xQ * T' = ν' ^ 2 - μ ^ 2 * W.a₆ := by
    apply hinj
    simp only [map_mul, map_sub, map_pow]
    rw [hTK, hνK]
    linear_combination (ι μ) ^ 2 * v3
  have hl' : IsUnit (1 + W.a₁ * μ) := (isUnit_iff_not_dvd hπ).2 fun h => hπ.not_isUnit
    (isUnit_of_dvd_one (by have := dvd_sub h (dvd_mul_of_dvd_right dμ W.a₁); rwa [add_sub_cancel_right] at this))
  have dT : π ∣ T' - 1 := by
    rw [hTdef, show 1 + W.a₁ * μ - μ ^ 2 * (xP + xQ) - 1 = μ * (W.a₁ - μ * (xP + xQ)) by ring]
    exact dvd_mul_of_dvd_left dμ _
  have unitU : ∀ {r : 𝒪}, IsUnit (-(μ ^ 2 * r + T')) := fun {r} =>
    (isUnit_iff_not_dvd hπ).2 fun h => hπ.not_isUnit (isUnit_of_dvd_one (by
      have := dvd_add (dvd_add (dvd_neg.1 h) (dvd_neg.2 dT))
        (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_pow dμ two_ne_zero) r))
      convert this using 1; ring))
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ', ρ' = ν' * ↑hl'.unit⁻¹ := ⟨_, rfl⟩
  have hρ' : (1 + W.a₁ * μ) * ρ' = ν' := by
    rw [hρ'def, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  refine iota_pair (μ := μ) (l := 1) (l' := 1 + W.a₁ * μ) (ρ := ν') (ρ' := ρ')
    (U := -(μ ^ 2 * ν' + T')) (U' := -(μ ^ 2 * ρ' + T')) (xP := xP) (yP := yP) (xR := xQ)
    (yR := yQ) hπ he hq0 isUnit_one hl' unitU unitU hμ0 (tate_eq h2 h3 h4 eP)
    (tate_eq h2 h3 h4 eQ) dxP dyP dyQ (by rw [hν'def]; ring) (by linear_combination -hρ' - hν'def)
    lQ (by linear_combination lQ - hρ') ?_ ?_ (by ring) (by rw [one_mul, hρ'])
  · linear_combination ν' * S2 + S3 + ν' ^ 2 * hTdef
  · linear_combination ρ' * S2 + S3 + ρ' ^ 2 * hTdef + (ρ' - ν') * hρ'

theorem phiT_pair {P Q T : (curveK K W).Point} (hP : P ∉ E0Set K W) (hQ : Q ∉ E0Set K W)
    (hT : T ∈ E0Set K W) (hs : P + Q + T = 0) : phiT K W P + phiT K W Q = 0 := by
  rcases T with _ | ⟨X, Y, hT'⟩
  · have hQP : Q = -P := by
      change P + Q + 0 = 0 at hs
      rw [add_zero] at hs
      exact (neg_eq_of_add_eq_zero_right hs).symm
    rw [hQP, phiT_neg K hπ h2 h3 h4 he hq, add_neg_cancel]
  · by_cases hX : X ∈ Set.range ι
    · obtain ⟨xT, rfl⟩ := hX
      obtain ⟨yT, rfl⟩ := exists_y_of_equation K W hT'.1
      exact phiT_pair_int K hπ h2 h3 h4 he hq hP hQ hT hs
    · exact componentIndex_pair_nonintegral K hπ h2 h3 h4 he hq hP hQ hX hs

theorem componentIndex_sum_three {P Q R : (curveK K W).Point} (hs : P + Q + R = 0) :
    phiT K W P + phiT K W Q + phiT K W R = 0 := by
  have mem : ∀ {A B C : (curveK K W).Point}, A + B + C = 0 → B ∈ E0Set K W → C ∈ E0Set K W →
      A ∈ E0Set K W := by
    intro A B C h hB hC
    have : A = -(B + C) := by rw [← sub_eq_zero, sub_neg_eq_add, ← add_assoc]; exact h
    rw [this]
    exact (E0 K W).neg_mem ((E0 K W).add_mem hB hC)
  have hs₁ : Q + R + P = 0 := by rw [← hs]; abel
  have hs₂ : R + P + Q = 0 := by rw [← hs]; abel
  have hs₃ : P + R + Q = 0 := by rw [← hs]; abel
  by_cases hP : P ∈ E0Set K W <;> by_cases hQ : Q ∈ E0Set K W <;> by_cases hR : R ∈ E0Set K W
  · simp [phiT_of_mem K W hP, phiT_of_mem K W hQ, phiT_of_mem K W hR]
  · exact absurd (mem hs₂ hP hQ) hR
  · exact absurd (mem hs₁ hR hP) hQ
  · rw [phiT_of_mem K W hP, zero_add]
    exact phiT_pair K hπ h2 h3 h4 he hq hQ hR hP hs₁
  · exact absurd (mem hs hQ hR) hP
  · rw [phiT_of_mem K W hQ, add_zero]
    exact phiT_pair K hπ h2 h3 h4 he hq hP hR hQ hs₃
  · rw [phiT_of_mem K W hR, add_zero]
    exact phiT_pair K hπ h2 h3 h4 he hq hP hQ hR hs
  · exact phiT_three K hπ h2 h3 h4 he hq hP hQ hR hs

theorem phiT_add (P Q : (curveK K W).Point) : phiT K W (P + Q) = phiT K W P + phiT K W Q := by
  have h := componentIndex_sum_three K hπ h2 h3 h4 he hq (show P + Q + -(P + Q) = 0 by abel)
  rw [phiT_neg K hπ h2 h3 h4 he hq] at h
  linear_combination -h

def phiTHom : (curveK K W).Point →+ ZMod (v W.a₆).toNat :=
  AddMonoidHom.mk' (phiT K W) (phiT_add K hπ h2 h3 h4 he hq)

include K in
theorem one_le_n : 1 ≤ (v W.a₆).toNat := by
  have h1 := (one_le_v_iff hπ).2 hq
  have ht := v_ne_top (a₆_ne_zero K h2 h3 h4)
  lift v W.a₆ to ℕ using ht with n hn
  simp only [ENat.toNat_natCast]
  exact_mod_cast h1

theorem phiT_eq_zero_iff (P : (curveK K W).Point) : phiT K W P = 0 ↔ P ∈ E0Set K W := by
  refine ⟨fun h => ?_, phiT_of_mem K W⟩
  by_contra hP
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  obtain ⟨x, y, g, rfl, e', dx, dy⟩ := exists_of_notMem_E0Set K W hπ d3 d4 hq hP
  rw [phiT_some K W g hP] at h
  have E := tate_eq h2 h3 h4 e'
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hn : v W.a₆ = ((v W.a₆).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq0)).symm
  have hn1 := one_le_n K hπ h2 h3 h4 he hq
  set n := (v W.a₆).toNat
  have ha1 : 1 ≤ v y := (one_le_v_iff hπ).2 dy
  have hb1 : 1 ≤ v (y + W.a₁ * x) := (one_le_v_iff hπ).2 (dvd_add dy (dvd_mul_of_dvd_right dx _))
  have hsum := v_sum_eq E
  obtain ⟨hmin, -⟩ := v_x_of (x := x) (y := y) he
  obtain ⟨-, c2, -⟩ := v_cube_add x W.a₆
  rw [hn] at c2

  have key : ∀ {c : ℕ∞}, c = min (v y) (v (y + W.a₁ * x)) → (n : ℕ∞) ≤ c →
      v y + v (y + W.a₁ * x) = n := by
    intro c hc hcn
    rw [hsum]
    apply c2
    calc (n : ℕ∞) < 3 * n := by
          have : (n : ℕ∞) < 3 * (n : ℕ∞) := by
            have : n < 3 * n := by have := hn1; omega
            exact_mod_cast this
          exact this
      _ ≤ 3 * c := by gcongr
      _ ≤ 3 * v x := by gcongr; exact hc ▸ hmin
  have fin : v y + v (y + W.a₁ * x) = n → v y ≠ ⊤ ∧ v (y + W.a₁ * x) ≠ ⊤ := by
    intro hs'
    constructor <;> intro ht <;> rw [ht] at hs' <;> simp at hs'
  rcases le_or_gt (v (y + W.a₁ * x)) (v y) with hba | hab
  · rw [iotaN_of_le hba] at h
    have hbt : v (y + W.a₁ * x) ≠ ⊤ := by
      intro ht
      have hat : v y = ⊤ := top_le_iff.1 (ht ▸ hba)
      have hxt : v x = ⊤ := top_le_iff.1 (by rw [ht, hat, min_self] at hmin; exact hmin)
      have hx0 := addVal_eq_top_iff.1 hxt
      have hy0 := addVal_eq_top_iff.1 hat
      apply hq0
      rw [hx0, hy0] at E
      linear_combination -E
    have hlt : v (y + W.a₁ * x) < n := by
      by_contra hge
      push Not at hge
      have h' := key (by rw [min_eq_right hba]) hge
      obtain ⟨hat, -⟩ := fin h'
      lift v y to ℕ using hat with a ha
      lift v (y + W.a₁ * x) to ℕ using hbt with b hb
      have e1 : a + b = n := by exact_mod_cast h'
      have e2 : n ≤ b := by exact_mod_cast hge
      have e3 : b ≤ a := by exact_mod_cast hba
      omega
    lift v (y + W.a₁ * x) to ℕ using hbt with b hb
    simp only [ENat.toNat_natCast] at h
    exact natCast_ne_zero_of_lt (by exact_mod_cast hb1) (by exact_mod_cast hlt) h
  · rw [iotaN_of_lt hab, neg_eq_zero] at h
    have hat : v y ≠ ⊤ := hab.ne_top
    have hlt : v y < n := by
      by_contra hge
      push Not at hge
      have h' := key (by rw [min_eq_left hab.le]) hge
      obtain ⟨-, hbt⟩ := fin h'
      lift v y to ℕ using hat with a ha
      lift v (y + W.a₁ * x) to ℕ using hbt with b hb
      have e1 : a + b = n := by exact_mod_cast h'
      have e2 : n ≤ a := by exact_mod_cast hge
      have e3 : a < b := by exact_mod_cast hab
      omega
    lift v y to ℕ using hat with a ha
    simp only [ENat.toNat_natCast] at h
    exact natCast_ne_zero_of_lt (by exact_mod_cast ha1) (by exact_mod_cast hlt) h

theorem ker_phiTHom : (phiTHom K hπ h2 h3 h4 he hq).ker = E0 K W := by
  ext P
  rw [AddMonoidHom.mem_ker, mem_E0_iff]
  exact phiT_eq_zero_iff K hπ h2 h3 h4 he hq P

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem nonsingular_of_tate {x y : 𝒪} (h : y * (y + W.a₁ * x) = x ^ 3 + W.a₆) :
    (curveK K W).Nonsingular (ι x) (ι y) := by
  apply (equation_iff_nonsingular (W := W.map (algebraMap 𝒪 K))).1
  rw [equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, h2, h3, h4, map_zero]
  have := congrArg (algebraMap 𝒪 K) h
  simp only [map_mul, map_add, map_pow] at this
  linear_combination this

theorem exists_phiT_eq_one (hn2 : 2 ≤ (v W.a₆).toNat) : ∃ P, phiT K W P = 1 := by
  have hq0 := a₆_ne_zero K h2 h3 h4
  have hn : v W.a₆ = ((v W.a₆).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq0)).symm
  have d3 : π ∣ W.a₃ := by rw [h3]; exact dvd_zero _
  have d4 : π ∣ W.a₄ := by rw [h4]; exact dvd_zero _
  have hpow : ∀ k : ℕ, k ≤ (v W.a₆).toNat → π ^ k ∣ W.a₆ := fun k hk => by
    rw [← addVal_le_iff_dvd, hπ.addVal_pow, hn]; exact_mod_cast hk
  rcases Nat.lt_or_ge (v W.a₆).toNat 3 with h3n | h3n
  ·
    obtain ⟨q₂, hq₂⟩ := hpow 2 hn2
    obtain ⟨X₀, hX₀⟩ : ∃ X₀, W.a₁ * X₀ = q₂ - 1 := ⟨(q₂ - 1) * ↑he.unit⁻¹, by
      rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]⟩
    have hγ : IsUnit (3 * π * X₀ ^ 2 - W.a₁) := by
      rw [isUnit_iff_not_dvd hπ]
      intro h
      apply (isUnit_iff_not_dvd hπ).1 he
      have := dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl π) 3) (X₀ ^ 2)) h
      convert this using 1; ring
    obtain ⟨Z, -, hZ⟩ := exists_root_cubic hπ (α := π) (β := 3 * π * X₀) hγ
      (δ := π * X₀ ^ 3 - W.a₁ * X₀ + q₂ - 1) ⟨X₀ ^ 3, by linear_combination -hX₀⟩
    have heq : π * (π + W.a₁ * (π * (X₀ + Z))) = (π * (X₀ + Z)) ^ 3 + W.a₆ := by
      rw [hq₂]; linear_combination (-π ^ 2) * hZ
    have hpt := nonsingular_of_tate K hπ h2 h3 h4 he hq heq
    have hP := notMem_E0Set_of_dvd K W hπ d3 d4 hpt (dvd_mul_right π _) (dvd_refl π)
    refine ⟨Point.some _ _ hpt, zmod_two_eq_one (by omega) ?_⟩
    rw [Ne, phiT_eq_zero_iff K hπ h2 h3 h4 he hq]
    exact hP
  ·
    obtain ⟨q₃, hq₃⟩ := hpow 3 h3n
    obtain ⟨Y, dY, hY⟩ := exists_root_cubic hπ (α := 0) (β := 1) he
      (δ := -(π * (1 + q₃))) (dvd_neg.2 (dvd_mul_right π _))
    have heq : π * Y * (π * Y + W.a₁ * π) = π ^ 3 + W.a₆ := by
      rw [hq₃]; linear_combination π ^ 2 * hY
    have hpt := nonsingular_of_tate K hπ h2 h3 h4 he hq heq
    have hP := notMem_E0Set_of_dvd K W hπ d3 d4 hpt (dvd_refl π) (dvd_mul_right π _)
    refine ⟨Point.some _ _ hpt, ?_⟩
    rw [phiT_some K W hpt hP]
    have hw : v (π * Y + W.a₁ * π) = 1 := by
      rw [show π * Y + W.a₁ * π = π * (Y + W.a₁) by ring, addVal_mul, addVal_uniformizer hπ,
        v_unit ((isUnit_iff_not_dvd hπ).2 fun h => (isUnit_iff_not_dvd hπ).1 he (by
          have := dvd_sub h dY; rwa [add_sub_cancel_left] at this)), add_zero]
    have hy : 1 ≤ v (π * Y) := by
      rw [addVal_mul, addVal_uniformizer hπ]; exact le_self_add
    rw [iotaN_of_le (hw ▸ hy), hw]
    simp

theorem phiTHom_surjective : Function.Surjective (phiTHom K hπ h2 h3 h4 he hq) := by
  intro k
  rcases Nat.lt_or_ge (v W.a₆).toNat 2 with h1 | h2n
  · have hn1 := one_le_n K hπ h2 h3 h4 he hq
    have : (v W.a₆).toNat = 1 := by omega
    refine ⟨0, ?_⟩
    have hsub : Subsingleton (ZMod (v W.a₆).toNat) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
  · obtain ⟨P, hP⟩ := exists_phiT_eq_one K hπ h2 h3 h4 he hq h2n
    have : NeZero (v W.a₆).toNat := ⟨by omega⟩
    refine ⟨k.val • P, ?_⟩
    rw [map_nsmul]
    change k.val • phiT K W P = k
    rw [hP, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

def tateQuotientEquiv : (curveK K W).Point ⧸ E0 K W ≃+ ZMod (v W.a₆).toNat :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_phiTHom K hπ h2 h3 h4 he hq)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (phiTHom_surjective K hπ h2 h3 h4 he hq))

end Hom

end

end GroundTheory.Arith.Abelian
end
