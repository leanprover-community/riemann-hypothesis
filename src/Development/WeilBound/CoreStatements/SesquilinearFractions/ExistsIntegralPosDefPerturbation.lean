import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestMore
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem exists_integer_near_conj_vector : ∀ (E : Type) [Field E] [NumberField E], ∃ B : ℝ, ∀ c : (E →+* ℂ) → ℂ, (∀ τ, c (ComplexEmbedding.conjugate τ) = starRingEnd ℂ (c τ)) → ∃ a : 𝓞 E, ∀ τ : E →+* ℂ, ‖τ (a : E) - c τ‖ ≤ B := by
  intro E _ _
  classical
  obtain ⟨bC, hv⟩ : ∃ bC : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ ((E →+* ℂ) → ℂ),
      ∀ i (τ : E →+* ℂ), bC i τ = τ (RingOfIntegers.basis E i : E) :=
    ⟨canonicalEmbedding.latticeBasis E, fun i τ => by
      rw [canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, integralBasis_apply]⟩
  refine ⟨∑ τ : E →+* ℂ, ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖, fun c hc => ?_⟩
  have hsum : c = ∑ i, bC.repr c i • bC i := (bC.sum_repr c).symm
  have hcτ : ∀ τ : E →+* ℂ, c τ = ∑ i, bC.repr c i * τ (RingOfIntegers.basis E i : E) := by
    intro τ
    conv_lhs => rw [hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
  have hconj : ∀ τ : E →+* ℂ,
      ∑ i, starRingEnd ℂ (bC.repr c i) * τ (RingOfIntegers.basis E i : E) = c τ := by
    intro τ
    have h1 := hc τ
    rw [hcτ (ComplexEmbedding.conjugate τ)] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [Complex.conj_conj, map_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hli := Fintype.linearIndependent_iff.mp bC.linearIndependent
    (fun i => bC.repr c i - starRingEnd ℂ (bC.repr c i)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hv, sub_mul,
        Finset.sum_sub_distrib]
      rw [hconj τ, ← hcτ τ, sub_self])
  have hreal : ∀ i, (bC.repr c i).im = 0 := by
    intro i
    have h3 := congrArg Complex.im (hli i)
    rw [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at h3
    linarith
  obtain ⟨x, hx⟩ : ∃ x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ i, bC.repr c i = (x i : ℂ) :=
    ⟨fun i => (bC.repr c i).re, fun i => Complex.ext (by simp) (by simp [hreal i])⟩
  refine ⟨∑ i, round (x i) • RingOfIntegers.basis E i, fun τ => ?_⟩
  have hτa : τ ((∑ i, round (x i) • RingOfIntegers.basis E i : 𝓞 E) : E) =
      ∑ i, (round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    change (τ.comp (algebraMap (𝓞 E) E)) (∑ i, round (x i) • RingOfIntegers.basis E i) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have hcx : c τ = ∑ i, (x i : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    rw [hcτ τ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
  rw [hτa, hcx, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E))‖
      ≤ ∑ i, ‖(round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖ := Finset.sum_le_sum fun i _ => by
        rw [← sub_mul, norm_mul]
        have hr : ‖(round (x i) : ℂ) - (x i : ℂ)‖ ≤ 1 := by
          have h := abs_sub_round (x i)
          rw [show ((round (x i) : ℤ) : ℂ) - ((x i : ℝ) : ℂ) = (((round (x i) : ℝ) - x i : ℝ) : ℂ) by
            push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
          linarith
        calc ‖(round (x i) : ℂ) - (x i : ℂ)‖ * ‖τ (RingOfIntegers.basis E i : E)‖
            ≤ 1 * ‖τ (RingOfIntegers.basis E i : E)‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
          _ = ‖τ (RingOfIntegers.basis E i : E)‖ := one_mul _
    _ ≤ ∑ τ' : E →+* ℂ, ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖ :=
        Finset.single_le_sum (f := fun τ' : E →+* ℂ => ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖)
          (fun τ' _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ τ)

end PositivityTheory.Xgf

end
end

section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem complexEmbedding_conjugate_conjugate {E : Type} [Field E] (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := star_star τ

private theorem eventually_posDef_add_mul_conjTranspose {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (C : Matrix I J ℂ) (M : Matrix J J ℂ) (hM : M.IsHermitian) (h : (C * M * Cᴴ).PosDef) :
    ∀ᶠ D in nhds (0 : Matrix I J ℂ), ((C + D) * M * (C + D)ᴴ).PosDef := by
  let g : Matrix I J ℂ × (I → ℂ) → ℝ := fun p =>
    (star p.2 ⬝ᵥ (((C + p.1) * M * (C + p.1)ᴴ) *ᵥ p.2)).re
  have hg : Continuous g := by
    refine Complex.continuous_re.comp ?_
    refine Continuous.dotProduct (continuous_star.comp continuous_snd) ?_
    refine Continuous.matrix_mulVec ?_ continuous_snd
    refine Continuous.matrix_mul ?_ ?_
    · exact (continuous_const.add continuous_fst).matrix_mul continuous_const
    · exact (continuous_const.add continuous_fst).matrix_conjTranspose
  have hK : IsCompact (Metric.sphere (0 : I → ℂ) 1) := isCompact_sphere 0 1
  have key : ∀ᶠ D in nhds (0 : Matrix I J ℂ), ∀ u ∈ Metric.sphere (0 : I → ℂ) 1, 0 < g (D, u) := by
    apply hK.eventually_forall_of_forall_eventually
    intro u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have h0 : 0 < g (0, u) := by
      have hp := h.dotProduct_mulVec_pos hu0
      have hp' := (Complex.lt_def.mp hp).1
      simpa [g] using hp'
    exact hg.continuousAt.eventually (lt_mem_nhds h0)
  filter_upwards [key] with D hD
  have hH : ((C + D) * M * (C + D)ᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose _ hM
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : I → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def
  have hu : u ∈ Metric.sphere (0 : I → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hu_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hx' : x = ((‖x‖ : ℝ) : ℂ) • u := by
    rw [hu_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  have hpos := hD u hu
  rw [Complex.lt_def]
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  rw [hx', star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, Complex.zero_re]
  exact mul_pos hr (mul_pos hr hpos)

theorem exists_integral_posDef_perturbation : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef := by
  intro E _ _ Ψ I J _ _ _ _ M C X₀ n hn hΨ hpos
  classical
  obtain ⟨B, hB⟩ := exists_integer_near_conj_vector E
  let f : ℕ → I → J → (E →+* ℂ) → ℂ := fun k i j τ => ((k : ℂ) * C τ i j - τ (X₀ i j : E)) / n
  let c : ℕ → I → J → (E →+* ℂ) → ℂ := fun k i j σ =>
    if σ ∈ Ψ then f k i j σ
    else if ComplexEmbedding.conjugate σ ∈ Ψ then starRingEnd ℂ (f k i j (ComplexEmbedding.conjugate σ))
    else 0
  have hc : ∀ k i j σ, c k i j (ComplexEmbedding.conjugate σ) = starRingEnd ℂ (c k i j σ) := by
    intro k i j σ
    by_cases h1 : σ ∈ Ψ
    · have h2 : ComplexEmbedding.conjugate σ ∉ Ψ := hΨ σ h1
      simp [c, h1, h2, complexEmbedding_conjugate_conjugate]
    · by_cases h2 : ComplexEmbedding.conjugate σ ∈ Ψ
      · simp [c, h1, h2]
      · simp [c, h1, h2, complexEmbedding_conjugate_conjugate]
  choose a ha using fun (k : ℕ) (i : I) (j : J) => hB (c k i j) (hc k i j)
  let D : ℕ → (E →+* ℂ) → Matrix I J ℂ := fun k τ =>
    Matrix.of fun i j => ((n : ℂ) / k) * (τ (a k i j : E) - c k i j τ)
  have hX : ∀ k : ℕ, k ≠ 0 → ∀ τ ∈ Ψ,
      ((X₀ + n • Matrix.of (a k)).map fun x => τ (x : E)) = (k : ℂ) • (C τ + D k τ) := by
    intro k hk τ hτ
    ext i j
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, D, c, f,
      if_pos hτ, smul_eq_mul]
    push_cast
    simp only [map_add, map_nsmul, nsmul_eq_mul, map_mul, map_natCast]
    field_simp
    ring
  have hD : ∀ τ, Filter.Tendsto (fun k : ℕ => D k τ) Filter.atTop (nhds 0) := by
    intro τ
    refine tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => ?_))
    have hb : Filter.Tendsto (fun k : ℕ => (n : ℝ) * B / k) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' (Filter.Eventually.of_forall fun k => ?_) hb
    calc ‖D k τ i j‖ = ((n : ℝ) / k) * ‖τ (a k i j : E) - c k i j τ‖ := by
          simp only [D, Matrix.of_apply, norm_mul, norm_div, Complex.norm_natCast]
      _ ≤ ((n : ℝ) / k) * B := mul_le_mul_of_nonneg_left (ha k i j τ) (by positivity)
      _ = (n : ℝ) * B / k := by ring
  have hev : ∀ τ ∈ Ψ, ∀ᶠ k in Filter.atTop,
      ((C τ + D k τ) * M τ * (C τ + D k τ)ᴴ).PosDef := fun τ hτ =>
    (hD τ).eventually (eventually_posDef_add_mul_conjTranspose (C τ) (M τ) (hpos τ hτ).1 (hpos τ hτ).2)
  have hall : ∀ᶠ k in Filter.atTop, ∀ τ ∈ Ψ,
      ((C τ + D k τ) * M τ * (C τ + D k τ)ᴴ).PosDef :=
    (Filter.eventually_all_finite (Set.toFinite Ψ)).mpr hev
  obtain ⟨k, hk1, hk2⟩ := (hall.and (Filter.eventually_ne_atTop 0)).exists
  refine ⟨Matrix.of (a k), fun τ hτ => ?_⟩
  rw [hX k hk2 τ hτ]
  have hkpos : (0 : ℂ) < (k : ℂ) := by exact_mod_cast Nat.pos_of_ne_zero hk2
  have h2 := (hk1 τ hτ).smul (mul_pos hkpos hkpos)
  convert h2 using 1
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_natCast]

end PositivityTheory.Xgf

end
end
