import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LidxAntisymm

section
noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem length_quot_pow (P : HeightOneSpectrum R) (k : ℕ) :
    Module.length R (R ⧸ P.asIdeal ^ k) = k := by
  haveI := P.isMaximal
  let Rₚ := Localization.AtPrime P.asIdeal
  haveI : IsDiscreteValuationRing Rₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rₚ
  let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow P.asIdeal Rₚ k
  rw [e.toLinearEquiv.length_eq]
  have hs1 : Function.Surjective (algebraMap R (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ k)) := by
    intro q
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e.symm q)
    refine ⟨r, ?_⟩
    have h1 : e (Ideal.Quotient.mk _ r) = q := by rw [hr]; simp
    rw [← h1, IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
    rfl
  have hs2 : Function.Surjective (algebraMap Rₚ (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ k)) :=
    Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hs1, ← Module.length_eq_of_surjective hs2,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

variable (K) in

abbrev cI (J : Ideal R) : Submodule R K := ((J : FractionalIdeal (nonZeroDivisors R) K) : Submodule R K)

theorem mem_cI {J : Ideal R} {x : K} : x ∈ cI K J ↔ ∃ y ∈ J, algebraMap R K y = x := by
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]

theorem algebraMap_mem_cI {J : Ideal R} {y : R} : algebraMap R K y ∈ cI K J ↔ y ∈ J := by
  rw [mem_cI]
  constructor
  · rintro ⟨z, hz, he⟩
    rwa [← (IsFractionRing.injective R K) he]
  · intro h; exact ⟨y, h, rfl⟩

theorem smul_algebraMap (s y : R) : s • algebraMap R K y = algebraMap R K (s * y) := by
  rw [Algebra.smul_def, map_mul]

theorem relativeLength_localized_pow (P : HeightOneSpectrum R) (k : ℕ) :
    relative₂ (localization₂ P.asIdeal (cI K (P.asIdeal ^ k))) (localization₂ P.asIdeal (1 : Submodule R K)) = k := by
  haveI := P.isMaximal
  set p := P.asIdeal
  set Z := localization₂ p (1 : Submodule R K)
  set X := localization₂ p (cI K (p ^ k))
  have hZ : ∀ r : R, Algebra.linearMap R K r ∈ Z := fun r =>
    le_locP p _ (Submodule.mem_one.mpr ⟨r, rfl⟩)
  let φ : R →ₗ[R] Z := LinearMap.codRestrict Z (Algebra.linearMap R K) hZ
  let ψ : R →ₗ[R] (Z ⧸ X.comap Z.subtype) := (X.comap Z.subtype).mkQ.comp φ

  have hunit : ∀ t : R, t ∉ p → ∃ t' : R, t * t' - 1 ∈ p ^ k := by
    intro t ht
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (Ideal.Quotient.isUnit_mk_pow_of_notMem p (n := k) ht)
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨t', ?_⟩
    rw [← Ideal.Quotient.eq, map_mul, hb, map_one]
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨y, hy⟩ := z
      obtain ⟨t, ht, hty⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hty
      obtain ⟨t', ht'⟩ := hunit t ht
      refine ⟨r * t', ?_⟩
      simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, φ,
        LinearMap.codRestrict_apply, Algebra.linearMap_apply]
      refine ⟨t, ht, ?_⟩
      rw [smul_sub, ← hr, smul_algebraMap, ← map_sub, algebraMap_mem_cI]
      have : t * (r * t') - r = r * (t * t' - 1) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ ht'
  have hker : LinearMap.ker ψ = p ^ k := by
    ext r
    simp only [LinearMap.mem_ker, ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, φ,
      LinearMap.codRestrict_apply, Algebra.linearMap_apply]
    constructor
    · rintro ⟨s, hs, hsr⟩
      rw [smul_algebraMap, algebraMap_mem_cI] at hsr
      have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem p (n := k) hs
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hsr ⊢
      rw [map_mul] at hsr
      exact (hu.mul_right_eq_zero).mp hsr
    · intro hr
      exact ⟨1, p.primeCompl.one_mem, by rw [one_smul, algebraMap_mem_cI]; exact hr⟩
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hψ)
  unfold relative₂
  rw [← e.length_eq, length_quot_pow]

theorem localization_cI_eq (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    localization₂ P.asIdeal (cI K J) =
      localization₂ P.asIdeal (cI K (P.asIdeal ^ (Associates.mk P.asIdeal).count (Associates.mk J).factors)) := by
  set k := (Associates.mk P.asIdeal).count (Associates.mk J).factors
  have hdvd : P.asIdeal ^ k ∣ J := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) P.associates_irreducible]
  obtain ⟨J', hJ'⟩ := hdvd
  have hJ'0 : J' ≠ 0 := by rintro rfl; exact hJ (by simpa using hJ')
  have hpk0 : P.asIdeal ^ k ≠ 0 := pow_ne_zero _ P.ne_bot

  have hc : FractionalIdeal.count K P (J' : FractionalIdeal (nonZeroDivisors R) K) = 0 := by
    have h1 := FractionalIdeal.count_coe K P hJ
    rw [hJ', FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K P
      (FractionalIdeal.coeIdeal_ne_zero.mpr hpk0) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ'0),
      FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow_self] at h1
    rw [← hJ'] at h1
    change (k : ℤ) + _ = (k : ℤ) at h1
    linarith
  have hnot : ¬ J' ≤ P.asIdeal := by
    intro hle
    have h2 := FractionalIdeal.count_mono K P (FractionalIdeal.coeIdeal_ne_zero.mpr hJ'0)
      (FractionalIdeal.coeIdeal_le_coeIdeal K |>.mpr hle)
    rw [hc, FractionalIdeal.count_self] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨s, hsJ', hsP⟩ := Set.not_subset.mp hnot
  apply le_antisymm
  · apply localization_mono
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_cI.mp hx
    rw [algebraMap_mem_cI]
    rw [hJ'] at hy
    exact (Ideal.mul_le_inf.trans inf_le_left : P.asIdeal ^ k * J' ≤ P.asIdeal ^ k) hy
  · rintro x ⟨t, ht, htx⟩
    obtain ⟨y, hy, hyx⟩ := mem_cI.mp htx
    refine ⟨s * t, ?_, ?_⟩
    · intro hst
      rcases Ideal.IsPrime.mem_or_mem (inferInstance) hst with h | h
      · exact hsP h
      · exact ht h
    · rw [mul_smul, ← hyx, smul_algebraMap, algebraMap_mem_cI, hJ']
      have := Ideal.mul_mem_mul hy hsJ'
      rwa [mul_comm y s] at this

theorem relativeLength_localized_coeIdeal (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    relative₂ (localization₂ P.asIdeal (cI K J)) (localization₂ P.asIdeal (1 : Submodule R K)) =
      (Associates.mk P.asIdeal).count (Associates.mk J).factors := by
  rw [localization_cI_eq P hJ, relativeLength_localized_pow]

end PI.IsoDetW.Loc
end
end

section
noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

abbrev mulR (a : K) : K →ₗ[R] K := (LinearMap.mulLeft K a).restrictScalars R

theorem mulR_injective {a : K} (ha : a ≠ 0) : Function.Injective (mulR (R := R) a) :=
  fun x y h => mul_left_cancel₀ ha h

theorem mulR_sat (p : Ideal R) [p.IsPrime] (a : K) (s : R) (y : K) (hs : s ∈ p.primeCompl)
    (hy : s • y ∈ LinearMap.range (mulR (R := R) a)) : y ∈ LinearMap.range (mulR (R := R) a) :=
  sat_of_linear p (LinearMap.mulLeft K a) s y hs hy

theorem map_mulR (a : K) (I : FI) :
    (I : Submodule R K).map (mulR a) = ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K) := by
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
    LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

theorem lidx_mulR (P : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) (I J : FI) :
    lidx P.asIdeal ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K)
      ((FractionalIdeal.spanSingleton _ a * J : FI) : Submodule R K) =
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) := by
  rw [← map_mulR, ← map_mulR]
  exact lidx_map P.asIdeal (mulR a) (mulR_injective ha) (mulR_sat P.asIdeal a) _ _

theorem rlen_mulR (P : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) (I J : FI) :
    relative₂ (localization₂ P.asIdeal ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K))
      (localization₂ P.asIdeal ((FractionalIdeal.spanSingleton _ a * J : FI) : Submodule R K)) =
    relative₂ (localization₂ P.asIdeal (I : Submodule R K)) (localization₂ P.asIdeal (J : Submodule R K)) := by
  rw [← map_mulR, ← map_mulR]
  exact relativeLength_localized_map P.asIdeal (mulR a) (mulR_injective ha) (mulR_sat P.asIdeal a) _ _

theorem rlen_coeIdeal (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    relative₂ (localization₂ P.asIdeal ((J : FI) : Submodule R K)) (localization₂ P.asIdeal (1 : Submodule R K)) =
      ((FractionalIdeal.count K P (J : FI)).toNat : ℕ∞) := by
  have := relativeLength_localized_coeIdeal (K := K) P hJ
  rw [FractionalIdeal.count_coe K P hJ, Int.toNat_natCast]
  exact this

theorem exists_integral (I : FI) (hI : I ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ ∃ J : Ideal R, J ≠ 0 ∧
      FractionalIdeal.spanSingleton _ (algebraMap R K a) * I = (J : FI) := by
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  refine ⟨a, ha, J, ?_, ?_⟩
  · rintro rfl
    apply hI
    rw [hIJ]; simp
  · rw [hIJ, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ ha',
      FractionalIdeal.spanSingleton_one, one_mul]

theorem coe_le_one {I : FI} (h : I ≤ 1) : (I : Submodule R K) ≤ 1 :=
  (FractionalIdeal.coe_le_coe.mpr h).trans_eq FractionalIdeal.coe_one

theorem rlen_ne_top (P : HeightOneSpectrum R) {D X : FI} (hD : D ≠ 0) (hDX : D ≤ X) :
    relative₂ (localization₂ P.asIdeal (D : Submodule R K)) (localization₂ P.asIdeal (X : Submodule R K)) ≠ ⊤ := by
  have hX : X ≠ 0 := by rintro rfl; exact hD (le_bot_iff.mp hDX)
  obtain ⟨a, ha, J, hJ, hXJ⟩ := exists_integral X hX
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  rw [← rlen_mulR P ha' D X, hXJ]
  have hle : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ (J : FI) :=
    hXJ ▸ (by gcongr)
  have hle1 : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ 1 :=
    hle.trans (FractionalIdeal.coeIdeal_le_one)
  obtain ⟨J', hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
  have hJ'0 : J' ≠ 0 := by
    rintro rfl
    have : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * D = 0 := by
      rw [← hJ']; simp
    rcases mul_eq_zero.mp this with h | h
    · exact ha' (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
    · exact hD h
  rw [← hJ']
  have h1 := rlen_mono (localization_mono P.asIdeal (le_refl ((J' : FI) : Submodule R K)))
    (localization_mono P.asIdeal (show ((J' : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K) from
      by rw [hJ']; exact FractionalIdeal.coe_le_coe.mpr hle))
    (localization_mono P.asIdeal (coe_le_one FractionalIdeal.coeIdeal_le_one))
  rw [rlen_coeIdeal P hJ'0] at h1
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1

theorem lidx_one_coeIdeal (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    lidx P.asIdeal (1 : Submodule R K) ((J : FI) : Submodule R K) = FractionalIdeal.count K P (J : FI) := by
  have hle : ((J : FI) : Submodule R K) ≤ 1 := coe_le_one FractionalIdeal.coeIdeal_le_one
  have hne : (J : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  rw [lidx_eq_of_le P.asIdeal (D := ((J : FI) : Submodule R K)) (le_inf hle le_rfl)
    (by rw [rlen_coeIdeal P hJ]; exact ENat.coe_ne_top _) (by rw [rlen_self]; exact ENat.zero_ne_top),
    rlen_coeIdeal P hJ, rlen_self]
  simp only [ENat.toNat_coe, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  exact Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K P J)

theorem spanSingleton_algebraMap (a : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) = ((Ideal.span {a} : Ideal R) : FI) :=
  (FractionalIdeal.coeIdeal_span_singleton a).symm

theorem lidx_one_left (P : HeightOneSpectrum R) {I : FI} (hI : I ≠ 0) :
    lidx P.asIdeal (1 : Submodule R K) (I : Submodule R K) = FractionalIdeal.count K P I := by
  obtain ⟨a, ha, J, hJ, hIJ⟩ := exists_integral I hI
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  have hsa : Ideal.span {a} ≠ (0 : Ideal R) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  have hsaJ : Ideal.span {a} * J ≠ 0 := mul_ne_zero hsa hJ
  rw [← FractionalIdeal.coe_one, ← lidx_mulR P ha' 1 I, mul_one, hIJ, spanSingleton_algebraMap]

  have hD1 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((Ideal.span {a} : Ideal R) : FI) := by
    apply FractionalIdeal.coe_le_coe.mpr
    rw [FractionalIdeal.coeIdeal_mul]
    exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
  have hD2 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K) := by
    apply FractionalIdeal.coe_le_coe.mpr
    rw [FractionalIdeal.coeIdeal_mul]
    exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one
  have hD3 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((1 : FI) : Submodule R K) :=
    FractionalIdeal.coe_le_coe.mpr FractionalIdeal.coeIdeal_le_one
  have hDne : ((Ideal.span {a} * J : Ideal R) : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hsaJ
  rw [lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K)) hD1 hD3 hD2
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD1))
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD3))
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD2))]
  rw [lidx_antisymm, FractionalIdeal.coe_one, lidx_one_coeIdeal P hsa, lidx_one_coeIdeal P hJ]
  have hc := congrArg (FractionalIdeal.count K P) hIJ
  rw [FractionalIdeal.count_mul K P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha') hI,
    spanSingleton_algebraMap] at hc
  linarith

theorem exists_sandwich (I : FI) (hI : I ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ FractionalIdeal.spanSingleton _ (algebraMap R K r) ≤ I ∧
      I ≤ FractionalIdeal.spanSingleton _ (algebraMap R K r)⁻¹ := by
  obtain ⟨a, ha, J, hJ, hIJ⟩ := exists_integral I hI
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  obtain ⟨j, hjJ, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  refine ⟨a * j, mul_ne_zero ha hj0, ?_, ?_⟩
  ·
    rw [FractionalIdeal.spanSingleton_le_iff_mem]
    have : algebraMap R K j ∈ FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * I := by
      rw [hIJ]; exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨j, hjJ, rfl⟩
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_singleton_mul).mp this
    have e : algebraMap R K (a * j) = (a * a) • x := by
      rw [map_mul, hxe, Algebra.smul_def, map_mul]; ring
    rw [e]
    exact FractionalIdeal.mem_coe.mp (Submodule.smul_mem _ _ (FractionalIdeal.mem_coe.mpr hx))
  · intro x hx
    have hj' : algebraMap R K j ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hj0
    have hax : algebraMap R K a * x ∈ (J : FI) := by
      rw [← hIJ]; exact FractionalIdeal.mem_singleton_mul.mpr ⟨x, hx, rfl⟩
    obtain ⟨z, -, hze⟩ := (FractionalIdeal.mem_coeIdeal _).mp hax
    rw [FractionalIdeal.mem_spanSingleton]
    refine ⟨j * z, ?_⟩
    rw [Algebra.smul_def, map_mul, map_mul, hze]
    field_simp

theorem spanSingleton_mul_le (x y : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (x * y)) ≤
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) := by
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
  exact ⟨y, by rw [Algebra.smul_def, map_mul, mul_comm]⟩

theorem spanSingleton_le_one (x : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) ≤ 1 := by
  rw [spanSingleton_algebraMap]; exact FractionalIdeal.coeIdeal_le_one

theorem lidx_frac (P : HeightOneSpectrum R) {I J : FI} (hI : I ≠ 0) (hJ : J ≠ 0) :
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) =
      FractionalIdeal.count K P J - FractionalIdeal.count K P I := by
  obtain ⟨a, ha, haI, -⟩ := exists_sandwich I hI
  obtain ⟨b, hb, hbJ, -⟩ := exists_sandwich J hJ
  set D := FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (a * b)) with hD
  have hD0 : D ≠ 0 := by
    rw [hD, ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff]
    exact mul_ne_zero ha hb
  have hDI : D ≤ I := (spanSingleton_mul_le a b).trans haI
  have hDJ : D ≤ J := (by rw [hD, mul_comm]; exact spanSingleton_mul_le b a : D ≤ _).trans hbJ
  have hD1 : D ≤ 1 := spanSingleton_le_one _
  rw [lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K))
    (FractionalIdeal.coe_le_coe.mpr hDI) (FractionalIdeal.coe_le_coe.mpr hD1)
    (FractionalIdeal.coe_le_coe.mpr hDJ)
    (rlen_ne_top P hD0 hDI) (rlen_ne_top P hD0 hD1) (rlen_ne_top P hD0 hDJ)]
  rw [lidx_antisymm P.asIdeal _ ((1 : FI) : Submodule R K), FractionalIdeal.coe_one,
    lidx_one_left P hI, lidx_one_left P hJ]
  ring

end PI.IsoDetW.Loc
end
end

section
noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs

theorem localization_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (p : Ideal R) [p.IsPrime]
    (X : ∀ i, Submodule R (M i)) :
    localization₂ p (Submodule.pi Set.univ X) = Submodule.pi Set.univ (fun i => localization₂ p (X i)) := by
  classical
  ext x
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, mem_locP]
  constructor
  · rintro ⟨s, hs, hsx⟩ i
    exact ⟨s, hs, by simpa using hsx i⟩
  · intro h
    choose s hs hsx using h
    refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, fun i => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Pi.smul_apply, mul_smul]
    exact (X i).smul_mem _ (hsx i)

theorem rlen_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (X Z : ∀ i, Submodule R (M i)) :
    relative₂ (Submodule.pi Set.univ X) (Submodule.pi Set.univ Z) = ∑ i, relative₂ (X i) (Z i) := by
  classical
  let φ : (Submodule.pi Set.univ Z) →ₗ[R] (Π i, Z i ⧸ (X i).comap (Z i).subtype) :=
    LinearMap.pi fun i => ((X i).comap (Z i).subtype).mkQ ∘ₗ
      (LinearMap.codRestrict (Z i) (LinearMap.proj i ∘ₗ (Submodule.pi Set.univ Z).subtype)
        (fun z => z.2 i (Set.mem_univ i)))
  have hsurj : Function.Surjective φ := by
    intro q
    choose z hz using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨⟨fun i => (z i).1, fun i _ => (z i).2⟩, ?_⟩
    funext i
    rw [← hz i]
    rfl
  have hker : LinearMap.ker φ = (Submodule.pi Set.univ X).comap (Submodule.pi Set.univ Z).subtype := by
    ext z
    simp [φ, funext_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_pi]
    rfl
  unfold relative₂
  rw [((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)).length_eq,
    Module.length_pi_of_fintype]

end PI.IsoDetW.Loc
end
end

section
noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

def std : Submodule R (ι → K) := Submodule.pi Set.univ (fun _ => (1 : Submodule R K))

def sc (a : K) : Submodule R (ι → K) :=
  Submodule.pi Set.univ (fun _ => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) a : FI) : Submodule R K))

def IsLat (A : Submodule R (ι → K)) : Prop :=
  ∃ r : R, r ≠ 0 ∧ sc (algebraMap R K r) ≤ A ∧ A ≤ sc (algebraMap R K r)⁻¹

omit [IsDedekindDomain R] [DecidableEq ι] in
theorem mem_sc {a : K} {v : ι → K} :
    v ∈ (sc a : Submodule R (ι → K)) ↔ ∀ i, ∃ z : R, z • a = v i := by
  simp [sc, Submodule.mem_pi, Submodule.mem_span_singleton]

omit [IsDedekindDomain R] in
theorem span_le_span {a b : K} (t : R) (h : a = algebraMap R K t * b) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ FractionalIdeal.spanSingleton (nonZeroDivisors R) b := by
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
  exact ⟨t, by rw [Algebra.smul_def, h]⟩

omit [IsDedekindDomain R] [DecidableEq ι] in
theorem sc_mono {a b : K}
    (h : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ FractionalIdeal.spanSingleton (nonZeroDivisors R) b) :
    (sc a : Submodule R (ι → K)) ≤ sc b :=
  Submodule.pi_mono fun _ _ => FractionalIdeal.coe_le_coe.2 h

omit [IsDedekindDomain R] in
theorem algebraMap_ne_zero' {r : R} (hr : r ≠ 0) : algebraMap R K r ≠ 0 := by
  rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hr

omit [IsDedekindDomain R] in
theorem spanSingleton_ne_zero' {a : K} (ha : a ≠ 0) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≠ 0 := by
  rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha

omit [DecidableEq ι] in
theorem rlen_sc_ne_top (P : HeightOneSpectrum R) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r) : Submodule R (ι → K)))
      (localization₂ P.asIdeal (sc (algebraMap R K s)⁻¹)) ≠ ⊤ := by
  unfold sc
  rw [localization_pi, localization_pi, rlen_pi, ENat.sum_ne_top]
  intro i _
  refine rlen_ne_top P (spanSingleton_ne_zero' (algebraMap_ne_zero' hr)) (span_le_span (r * s) ?_)
  rw [map_mul, mul_assoc, mul_inv_cancel₀ (algebraMap_ne_zero' hs), mul_one]

omit [DecidableEq ι] in
theorem rlen_lat_ne_top (P : HeightOneSpectrum R) {A : Submodule R (ι → K)} (hA : IsLat A) {r : R}
    (hr : r ≠ 0) (hrA : sc (algebraMap R K r) ≤ A) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r))) (localization₂ P.asIdeal A) ≠ ⊤ := by
  obtain ⟨s, hs, -, hA2⟩ := hA
  exact ne_top_of_le_ne_top (rlen_sc_ne_top P hr hs)
    (rlen_mono le_rfl (localization_mono _ hrA) (localization_mono _ hA2))

omit [DecidableEq ι] in
theorem lat_cocycle (P : HeightOneSpectrum R) {A B C : Submodule R (ι → K)} (hA : IsLat A) (hB : IsLat B)
    (hC : IsLat C) : lidx P.asIdeal A C = lidx P.asIdeal A B + lidx P.asIdeal B C := by
  obtain ⟨a, ha, hA1, -⟩ := id hA
  obtain ⟨b, hb, hB1, -⟩ := id hB
  obtain ⟨c, hc, hC1, -⟩ := id hC
  have hr : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  have hDA : sc (algebraMap R K (a * b * c)) ≤ A :=
    (sc_mono (span_le_span (b * c) (by simp only [map_mul]; try ring))).trans hA1
  have hDB : sc (algebraMap R K (a * b * c)) ≤ B :=
    (sc_mono (span_le_span (a * c) (by simp only [map_mul]; try ring))).trans hB1
  have hDC : sc (algebraMap R K (a * b * c)) ≤ C :=
    (sc_mono (span_le_span (a * b) (by simp only [map_mul]; try ring))).trans hC1
  exact lidx_cocycle P.asIdeal hDA hDB hDC (rlen_lat_ne_top P hA hr hDA) (rlen_lat_ne_top P hB hr hDB)
    (rlen_lat_ne_top P hC hr hDC)

omit [DecidableEq ι] in
theorem isLat_pi (c : ι → FI) (hc : ∀ i, c i ≠ 0) :
    IsLat (Submodule.pi Set.univ (fun i => (c i : Submodule R K))) := by
  classical
  choose r hr hr1 hr2 using fun i => exists_sandwich (c i) (hc i)
  have hP : ∀ i, (∏ j ∈ Finset.univ.erase i, r j) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.2 fun j _ => hr j
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.2 fun i _ => hr i, ?_, ?_⟩
  · refine Submodule.pi_mono fun i _ => ?_
    refine FractionalIdeal.coe_le_coe.2 ((span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_).trans (hr1 i))
    rw [← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  · refine Submodule.pi_mono fun i _ => ?_
    refine FractionalIdeal.coe_le_coe.2 ((hr2 i).trans (span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_))
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (algebraMap_ne_zero' (hP i)), one_mul]

omit [IsDedekindDomain R] in
theorem map_sc_le (M : Matrix ι ι K) {d : R} (hd0 : d ≠ 0)
    (hd : ∀ i j, IsLocalization.IsInteger R (d • M i j)) (a : K) :
    (sc a : Submodule R (ι → K)).map (M.mulVecLin.restrictScalars R) ≤ sc (a * (algebraMap R K d)⁻¹) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_sc] at hv
  rw [mem_sc]
  choose z hz using hv
  choose m hm using hd
  have had := algebraMap_ne_zero' (K := K) hd0
  intro k
  refine ⟨∑ j, m k j * z j, ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [Algebra.smul_def, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hz j, map_mul, hm k j, Algebra.smul_def, Algebra.smul_def]
  field_simp

theorem isLat_map (g : Matrix ι ι K) (hg : g.det ≠ 0) {A : Submodule R (ι → K)} (hA : IsLat A) :
    IsLat (A.map (g.mulVecLin.restrictScalars R)) := by
  obtain ⟨s, hs, hA1, hA2⟩ := hA
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset ((ι × ι) ⊕ (ι × ι))) (Sum.elim (fun p => g p.1 p.2) (fun p => g⁻¹ p.1 p.2))
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hg1 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g i j) :=
    fun i j => hd (Sum.inl (i, j)) (Finset.mem_univ _)
  have hg2 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g⁻¹ i j) :=
    fun i j => hd (Sum.inr (i, j)) (Finset.mem_univ _)
  have had := algebraMap_ne_zero' (K := K) hd0
  have has := algebraMap_ne_zero' (K := K) hs
  refine ⟨s * d, mul_ne_zero hs hd0, ?_, ?_⟩
  · intro v hv
    have hu := map_sc_le g⁻¹ hd0 hg2 _ (Submodule.mem_map_of_mem (f := g⁻¹.mulVecLin.restrictScalars R) hv)
    rw [map_mul, mul_inv_cancel_right₀ had] at hu
    refine ⟨g⁻¹.mulVec v, hA1 hu, ?_⟩
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg), Matrix.one_mulVec]
  · refine (Submodule.map_mono hA2).trans ((map_sc_le g hd0 hg1 _).trans ?_)
    rw [map_mul, mul_inv]

omit [DecidableEq ι] in
theorem pi_inf_pi (X Z : ι → Submodule R K) :
    Submodule.pi Set.univ X ⊓ Submodule.pi Set.univ Z = Submodule.pi Set.univ (fun i => X i ⊓ Z i) := by
  ext v
  simp [Submodule.mem_pi, forall_and]

omit [DecidableEq ι] in
theorem toNat_sum (f : ι → ℕ∞) (hf : ∀ i, f i ≠ ⊤) : (∑ i, f i).toNat = ∑ i, (f i).toNat := by
  have : (∑ i, f i) = ((∑ i, (f i).toNat : ℕ) : ℕ∞) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => (ENat.natCast_toNat (hf i)).symm
  rw [this, ENat.toNat_natCast]

omit [DecidableEq ι] in
theorem lidx_pi_frac (P : HeightOneSpectrum R) (c b : ι → FI) (hc : ∀ i, c i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    lidx P.asIdeal (Submodule.pi Set.univ (fun i => (c i : Submodule R K)))
      (Submodule.pi Set.univ (fun i => (b i : Submodule R K))) =
      ∑ i, (FractionalIdeal.count K P (b i) - FractionalIdeal.count K P (c i)) := by
  have hinf : ∀ i, c i ⊓ b i ≠ 0 := by
    intro i
    obtain ⟨r, hr, hr1, -⟩ := exists_sandwich (c i) (hc i)
    obtain ⟨t, ht, ht1, -⟩ := exists_sandwich (b i) (hb i)
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (r * t)) ≤ c i ⊓ b i :=
      le_inf ((span_le_span t (by rw [map_mul, mul_comm])).trans hr1)
        ((span_le_span r (by rw [map_mul])).trans ht1)
    intro h0
    rw [h0, FractionalIdeal.le_zero_iff] at hle
    exact spanSingleton_ne_zero' (algebraMap_ne_zero' (mul_ne_zero hr ht)) hle
  have hf1 : ∀ i, relative₂ (localization₂ P.asIdeal ((c i : Submodule R K) ⊓ (b i : Submodule R K)))
      (localization₂ P.asIdeal (c i : Submodule R K)) ≠ ⊤ := by
    intro i
    have := rlen_ne_top P (hinf i) (inf_le_left : c i ⊓ b i ≤ c i)
    rwa [FractionalIdeal.coe_inf] at this
  have hf2 : ∀ i, relative₂ (localization₂ P.asIdeal ((c i : Submodule R K) ⊓ (b i : Submodule R K)))
      (localization₂ P.asIdeal (b i : Submodule R K)) ≠ ⊤ := by
    intro i
    have := rlen_ne_top P (hinf i) (inf_le_right : c i ⊓ b i ≤ b i)
    rwa [FractionalIdeal.coe_inf] at this
  rw [lidx_eq, pi_inf_pi, localization_pi, localization_pi, localization_pi, rlen_pi, rlen_pi, toNat_sum _ hf1, toNat_sum _ hf2]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← lidx_frac P (hc i) (hb i), lidx_eq]

end PI.IsoDetW.Loc
end
end

section
noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

abbrev mR (g : Matrix ι ι K) : (ι → K) →ₗ[R] (ι → K) := g.mulVecLin.restrictScalars R

theorem mR_apply (g : Matrix ι ι K) (x : ι → K) : mR (R := R) g x = g.mulVec x := rfl

theorem mR_injective {g : Matrix ι ι K} (hg : g.det ≠ 0) : Function.Injective (mR (R := R) g) := by
  intro x y h
  have h2 := congrArg (fun v => g⁻¹.mulVec v) h
  simp only [mR_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hg),
    Matrix.one_mulVec] at h2
  exact h2

theorem mR_sat (P : HeightOneSpectrum R) (g : Matrix ι ι K) (s : R) (y : ι → K)
    (hs : s ∈ P.asIdeal.primeCompl) (hy : s • y ∈ LinearMap.range (mR (R := R) g)) :
    y ∈ LinearMap.range (mR (R := R) g) :=
  sat_of_linear P.asIdeal g.mulVecLin s y hs hy

theorem lidx_mR (P : HeightOneSpectrum R) {g : Matrix ι ι K} (hg : g.det ≠ 0)
    (A B : Submodule R (ι → K)) :
    lidx P.asIdeal (A.map (mR g)) (B.map (mR g)) = lidx P.asIdeal A B :=
  lidx_map P.asIdeal (mR g) (mR_injective hg) (mR_sat P g) A B

theorem map_mR_mul (g h : Matrix ι ι K) (A : Submodule R (ι → K)) :
    (A.map (mR h)).map (mR g) = A.map (mR (g * h)) := by
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, mR_apply, mR_apply, mR_apply, Matrix.mulVec_mulVec]

theorem map_mR_one (A : Submodule R (ι → K)) : A.map (mR (1 : Matrix ι ι K)) = A := by
  have : mR (R := R) (1 : Matrix ι ι K) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.id_apply, mR_apply, Matrix.one_mulVec]
  rw [this, Submodule.map_id]

theorem std_eq : (std : Submodule R (ι → K)) =
    Submodule.pi Set.univ (fun _ : ι => ((1 : FI) : Submodule R K)) := by
  simp only [std, FractionalIdeal.coe_one]

theorem isLat_std : IsLat (std : Submodule R (ι → K)) := by
  rw [std_eq]; exact isLat_pi (fun _ => 1) (fun _ => one_ne_zero)

variable (R) in

def chi (P : HeightOneSpectrum R) (g : Matrix ι ι K) : ℤ :=
  lidx P.asIdeal (std : Submodule R (ι → K)) ((std : Submodule R (ι → K)).map (mR g))

theorem chi_one (P : HeightOneSpectrum R) : chi R P (1 : Matrix ι ι K) = 0 := by
  rw [chi, map_mR_one, lidx_self]

theorem chi_mul (P : HeightOneSpectrum R) {g h : Matrix ι ι K} (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    chi R P (g * h) = chi R P g + chi R P h := by
  have hgh : (g * h).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hg hh
  unfold chi
  rw [← map_mR_mul, lat_cocycle P (B := (std : Submodule R (ι → K)).map (mR g)) isLat_std
    (isLat_map g hg isLat_std) (isLat_map g hg (isLat_map h hh isLat_std)), lidx_mR P hg]

theorem map_std_le {g : Matrix ι ι K} (hg : ∀ a b, ∃ z : R, algebraMap R K z = g a b) :
    (std : Submodule R (ι → K)).map (mR g) ≤ std := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : ∀ b, ∃ w : R, algebraMap R K w = y b := fun b =>
    Submodule.mem_one.mp ((Submodule.mem_pi.mp hy) b (Set.mem_univ b))
  choose w hw using hy'
  choose z hz using hg
  refine Submodule.mem_pi.mpr (fun a _ => Submodule.mem_one.mpr ?_)
  refine ⟨∑ b, z a b * w b, ?_⟩
  rw [mR_apply, Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul, hz, hw]

theorem map_std_eq {g g' : Matrix ι ι K} (hg : ∀ a b, ∃ z : R, algebraMap R K z = g a b)
    (hg' : ∀ a b, ∃ z : R, algebraMap R K z = g' a b) (hgg' : g * g' = 1) :
    (std : Submodule R (ι → K)).map (mR g) = std := by
  refine le_antisymm (map_std_le hg) (fun y hy => ?_)
  refine ⟨g'.mulVec y, map_std_le hg' ⟨y, hy, rfl⟩, ?_⟩
  simp [mR_apply, Matrix.mulVec_mulVec, hgg']

theorem chi_transvection_int (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (z : R) :
    chi R P (Matrix.transvection i j (algebraMap R K z)) = 0 := by
  have hint : ∀ c : R, ∀ a b, ∃ w : R, algebraMap R K w = Matrix.transvection i j (algebraMap R K c) a b := by
    intro c a b
    refine ⟨Matrix.transvection i j c a b, ?_⟩
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [chi, map_std_eq (hint z) (g' := Matrix.transvection i j (algebraMap R K (-z))) (hint (-z))
    (by rw [Matrix.transvection_mul_transvection_same i j hij, ← map_add, add_neg_cancel, map_zero,
      Matrix.transvection_zero]), lidx_self]

theorem chi_transvection (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (c : K) :
    chi R P (Matrix.transvection i j c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, Matrix.transvection_zero, chi_one]
  set D : Matrix ι ι K := Matrix.diagonal (Function.update 1 i c)
  set D' : Matrix ι ι K := Matrix.diagonal (Function.update 1 i c⁻¹)
  have hDD' : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    by_cases ha : a = i
    · subst ha; simp [hc]
    · simp [Function.update_of_ne ha]
  have hdet : ∀ M N : Matrix ι ι K, M * N = 1 → M.det ≠ 0 := fun M N h hM => by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, hM, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hD : D.det ≠ 0 := hdet D D' hDD'
  have hD'D : D' * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    by_cases ha : a = i
    · subst ha; simp [hc]
    · simp [Function.update_of_ne ha]
  have hD' : D'.det ≠ 0 := hdet D' D hD'D
  have ht1 : (Matrix.transvection i j (1 : K)).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero
  have he : Matrix.transvection i j c = D * Matrix.transvection i j 1 * D' := by
    ext a b
    simp only [D, D', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    rcases eq_or_ne a i with rfl | ha
    · rcases eq_or_ne b a with rfl | hba
      · simp [Function.update_self, hij.symm]
        field_simp
      · rcases eq_or_ne b j with rfl | hbj
        · simp [Function.update_self, Function.update_of_ne hba, hba.symm]
        · simp [hba.symm, hbj.symm]
    · rcases eq_or_ne a b with rfl | hab
      · simp [Function.update_of_ne ha, ha.symm]
      · simp [hab, ha.symm, Function.update_of_ne ha]
  have h1 := chi_transvection_int (K := K) P hij 1
  rw [map_one] at h1
  rw [he, chi_mul P (by rw [Matrix.det_mul]; exact mul_ne_zero hD ht1) hD', chi_mul P hD ht1, h1,
    add_zero, ← chi_mul P hD hD', hDD', chi_one]

theorem std_map_diagonal (D : ι → K) :
    (std : Submodule R (ι → K)).map (mR (Matrix.diagonal D)) =
      Submodule.pi Set.univ (fun i => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i) : FI) :
        Submodule R K)) := by
  ext x
  simp only [Submodule.mem_map, std, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_spanSingleton, mR_apply, Matrix.mulVec_diagonal]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    obtain ⟨w, hw⟩ := hy i
    exact ⟨w, by rw [Matrix.mulVec_diagonal, Algebra.smul_def, hw, mul_comm]⟩
  · intro h
    choose w hw using h
    refine ⟨fun i => algebraMap R K (w i), fun i => ⟨w i, rfl⟩, ?_⟩
    ext i
    rw [Matrix.mulVec_diagonal, ← hw i, Algebra.smul_def, mul_comm]

theorem count_spanSingleton_prod (P : HeightOneSpectrum R) (D : ι → K) (hD : ∀ i, D i ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i)) =
      ∑ i, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i)) := by
  have : FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i) =
      ∏ i, FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton, ih]
  rw [this, FractionalIdeal.count_prod K P _ _ (fun i _ =>
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (hD i))]

theorem chi_diagonal (P : HeightOneSpectrum R) (D : ι → K) (hD : ∀ i, D i ≠ 0) :
    chi R P (Matrix.diagonal D) =
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i)) := by
  rw [chi, std_map_diagonal, std_eq, lidx_pi_frac P (fun _ => 1)
    (fun i => FractionalIdeal.spanSingleton _ (D i)) (fun _ => one_ne_zero)
    (fun i => FractionalIdeal.spanSingleton_ne_zero_iff.mpr (hD i)), count_spanSingleton_prod P D hD]
  simp [FractionalIdeal.count_one]

theorem chi_eq (P : HeightOneSpectrum R) (g : Matrix ι ι K) (hg : g.det ≠ 0) :
    chi R P g = FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) g.det) := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => chi R P M = FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) M.det))
    g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      intro i hi
      rw [Matrix.det_diagonal] at hD
      exact hD (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    rw [chi_diagonal P D hD', Matrix.det_diagonal]
  · intro t
    rw [Matrix.TransvectionStruct.det, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
    exact chi_transvection P t.hij t.c
  · intro A B hA hB hA' hB'
    rw [chi_mul P hA hB, hA', hB', Matrix.det_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hA)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hB)]

end PI.IsoDetW.Loc
end
end
