module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormMapOfFinOrder
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ScalarModulus

theorem norm_eq_one_of_locK {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ}
    {j : Fin m} {χ : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (h : IsMu0 Ch σ₀ e j χ)
    (P : HeightOneSpectrum (𝓞 X.E)) (x : X.Eˣ) (y : X.K) (hy : σ₀ y = ((χ.locK P x : ℂˣ) : ℂ)) (σ : X.K →+* ℂ) :
    ‖σ y‖ = 1 := by
  have h0 : ((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (hPr.g_prime 0).ne_zero) (by exact_mod_cast (hPr.g_prime 1).ne_zero)
  obtain ⟨M, z, hM, -, -, hz⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E χ
    (divs (((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E))) (GlobalTheory.CharVal.productRule χ)
    (fun v hv => h.unr v fun i hi => hv ((Formalism.L2.Col.mem_divs h0 v).2 (by
      fin_cases i
      exacts [v.asIdeal.mul_mem_right _ hi, v.asIdeal.mul_mem_left _ hi]))) h.tame P x
  obtain ⟨n, -, hn⟩ := h.inf
  have hz' := congrArg Units.val hz
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hn z, ← hy, Units.val_one] at hz'
  have hsq : ∀ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ 2 =
      σ₀ (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) := by
    intro τ
    have h1 : X.embC σ₀ τ z ≠ 0 := (map_ne_zero _).2 z.ne_zero
    have h2 := hX.conjE (X.embC σ₀ τ) z
    rw [map_div₀]
    change _ = X.embC σ₀ τ z / X.embC σ₀ τ (star (z : X.E))
    rw [h2, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h1]
  have key : y ^ (M * 2) * ∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ = 1 := by
    apply σ₀.injective
    rw [map_one, map_mul, map_pow, map_prod, pow_mul]
    have h3 : ∏ τ, σ₀ ((X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ) =
        (∏ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ n τ) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, ← hsq, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [h3, ← mul_pow, hz', one_pow]
  have h4 : ‖σ (∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ)‖ = 1 := by
    rw [map_prod, norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h1 : ‖(σ.comp (X.emb τ)) z‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 z.ne_zero)
    have h2 := hX.conjE (σ.comp (X.emb τ)) z
    rw [RingHom.comp_apply] at h1
    rw [RingHom.comp_apply, RingHom.comp_apply] at h2
    rw [map_zpow₀, norm_zpow, map_div₀, norm_div, h2, Complex.norm_conj, div_self h1, one_zpow]
  have h5 := congrArg (fun t => ‖σ t‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, h4, mul_one, map_one, norm_one] at h5
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h5

end GlobalTheory.ScalarModulus
