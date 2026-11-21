import Mathlib
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Filter Topology ComplexConjugate

namespace GroundTheory.Global

section Average

variable {G : Type*} [Group G]

theorem cosetAverage_eq_sum (I : Subgroup G) [Fintype I] (f : G → ℂ) (g : G) :
    cosetAverage I f g = (Nat.card I : ℂ)⁻¹ * ∑ i : I, f (g * i) := by
  rw [cosetAverage, finsum_eq_sum_of_fintype]

theorem norm_cosetAverage_le (I : Subgroup G) [Finite I] (f : G → ℂ) {C : ℝ}
    (hC : ∀ g, ‖f g‖ ≤ C) (g : G) : ‖cosetAverage I f g‖ ≤ C := by
  have := Fintype.ofFinite I
  have hI : (0 : ℝ) < Nat.card I := Nat.cast_pos.2 Nat.card_pos
  rw [cosetAverage_eq_sum, norm_mul, norm_inv, Complex.norm_natCast]
  calc (Nat.card I : ℝ)⁻¹ * ‖∑ i : I, f (g * i)‖ ≤ (Nat.card I : ℝ)⁻¹ * ∑ _i : I, C := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC _)
    _ = C := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
          inv_mul_cancel_left₀ hI.ne']

theorem cosetAverage_add (I : Subgroup G) [Finite I] (f₁ f₂ : G → ℂ) (g : G) :
    cosetAverage I (f₁ + f₂) g = cosetAverage I f₁ g + cosetAverage I f₂ g := by
  have := Fintype.ofFinite I
  simp only [cosetAverage_eq_sum, Pi.add_apply, Finset.sum_add_distrib, mul_add]



theorem cosetAverage_one (I : Subgroup G) [Finite I] (g : G) : cosetAverage I 1 g = 1 := by
  have := Fintype.ofFinite I
  have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [cosetAverage_eq_sum]
  simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hI

end Average

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section LocalAverage

variable (v : HeightOneSpectrum (𝓞 K))

theorem norm_localAverage_le (f : Gal(L/K) → ℂ) {C : ℝ} (hC : ∀ g, ‖f g‖ ≤ C) (m : ℕ) :
    ‖localAverage L v f m‖ ≤ C :=
  norm_cosetAverage_le _ f hC _

theorem localAverage_add (f₁ f₂ : Gal(L/K) → ℂ) (m : ℕ) :
    localAverage L v (f₁ + f₂) m = localAverage L v f₁ m + localAverage L v f₂ m :=
  cosetAverage_add _ f₁ f₂ _



theorem localAverage_one (m : ℕ) : localAverage L v (1 : Gal(L/K) → ℂ) m = 1 :=
  cosetAverage_one _ _

end LocalAverage

variable (K L) in

def artinTerm (f : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) : ℂ :=
  localAverage L v f m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ m / m

variable (K L) in

def artinLocalLog (f : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  ∑' m : ℕ, artinTerm K L f s v m

variable (K L) in

def artinLogL (f : Gal(L/K) → ℂ) (s : ℂ) : ℂ :=
  ∑' v : HeightOneSpectrum (𝓞 K), artinLocalLog K L f s v

variable (K L) in

def artinL (f : Gal(L/K) → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (artinLogL K L f s)

theorem artinTerm_zero (f : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    artinTerm K L f s v 0 = 0 := by
  simp [artinTerm]


section Convergence

theorem norm_absNorm_cpow_neg_le (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} {σ : ℝ} (hσs : σ ≤ s.re) :
    ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  have h1 := one_lt_absNorm_asIdeal v
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1.le) (by linarith)

theorem absNorm_rpow_neg_le_half (v : HeightOneSpectrum (𝓞 K)) {σ : ℝ} (hσ : 1 ≤ σ) :
    (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 := one_lt_absNorm_asIdeal v
  have h2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast h1
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, one_div]
        exact inv_anti₀ (by norm_num) h2

theorem norm_artinTerm_le (f : Gal(L/K) → ℂ) {C : ℝ} (hC : ∀ g, ‖f g‖ ≤ C) {s : ℂ} {σ : ℝ}
    (hσ : 1 ≤ σ) (hσs : σ ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    ‖artinTerm K L f s v m‖ ≤ 2 * C * (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) * (1 / 2) ^ m := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  set t : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ht1 : t ≤ 1 / 2 := absNorm_rpow_neg_le_half v hσ
  rcases Nat.eq_zero_or_eq_succ_pred m with rfl | hm
  · rw [artinTerm_zero, norm_zero]
    positivity
  · set k := m.pred
    rw [hm]
    have hy := norm_absNorm_cpow_neg_le v hσs
    rw [← ht] at hy
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    calc ‖artinTerm K L f s v (k + 1)‖
        = ‖localAverage L v f (k + 1)‖ * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ^ (k + 1) /
            ((k + 1 : ℕ) : ℝ) := by
          rw [artinTerm, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ C * t ^ (k + 1) / 1 := by
          gcongr
          exact norm_localAverage_le v f hC _
      _ = C * (t ^ k * t) := by rw [div_one, pow_succ]
      _ ≤ C * ((1 / 2) ^ k * t) := by gcongr
      _ = 2 * C * t * (1 / 2) ^ (k + 1) := by ring

theorem summable_absNorm_rpow_neg_place {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal :=
    fun v w h => HeightOneSpectrum.ext h
  refine ((summable_absNorm_rpow_inv (K := K) hσ).comp_injective hinj).congr fun v => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _)]

theorem summable_artinMajorant {C : ℝ} (hC0 : 0 ≤ C) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ =>
      2 * C * (Ideal.absNorm p.1.asIdeal : ℝ) ^ (-σ) * (1 / 2) ^ p.2 :=
  Summable.mul_of_nonneg ((summable_absNorm_rpow_neg_place hσ).mul_left (2 * C))
    summable_geometric_two (fun v => by positivity) (fun m => by positivity)

omit [IsGalois K L] in
theorem exists_norm_le (f : Gal(L/K) → ℂ) : ∃ C, ∀ g, ‖f g‖ ≤ C := by
  classical
  have := Fintype.ofFinite Gal(L/K)
  exact ⟨∑ g, ‖f g‖, fun g => Finset.single_le_sum (fun x _ => norm_nonneg (f x))
    (Finset.mem_univ g)⟩

theorem summable_norm_artinTerm (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ => ‖artinTerm K L f s p.1 p.2‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le f
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => norm_artinTerm_le f hC hs.le le_rfl p.1 p.2) (summable_artinMajorant hC0 hs)

theorem summable_artinTerm (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ => artinTerm K L f s p.1 p.2 :=
  (summable_norm_artinTerm f hs).of_norm

theorem hasSum_artinLocalLog (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (𝓞 K)) :
    HasSum (fun m => artinTerm K L f s v m) (artinLocalLog K L f s v) :=
  ((summable_artinTerm f hs).prod_factor v).hasSum

theorem hasSum_artinTerm_artinLogL (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : HeightOneSpectrum (𝓞 K) × ℕ => artinTerm K L f s p.1 p.2)
      (artinLogL K L f s) := by
  have h := (summable_artinTerm f hs).hasSum
  have h2 := h.prod_fiberwise fun v => hasSum_artinLocalLog f hs v
  rw [artinLogL, h2.tsum_eq]
  exact h

theorem hasSum_artinLocalLog_artinLogL (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v => artinLocalLog K L f s v) (artinLogL K L f s) := by
  have h := (summable_artinTerm f hs).hasSum.prod_fiberwise fun v => hasSum_artinLocalLog f hs v
  rwa [(hasSum_artinTerm_artinLogL f hs).tsum_eq] at h

end Convergence

section Holomorphy






end Holomorphy

section Additivity

theorem artinTerm_add (f₁ f₂ : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    artinTerm K L (f₁ + f₂) s v m = artinTerm K L f₁ s v m + artinTerm K L f₂ s v m := by
  rw [artinTerm, artinTerm, artinTerm, localAverage_add, add_mul, add_div]

theorem artinLogL_add (f₁ f₂ : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinLogL K L (f₁ + f₂) s = artinLogL K L f₁ s + artinLogL K L f₂ s := by
  refine (hasSum_artinTerm_artinLogL (f₁ + f₂) hs).unique ?_
  simp only [artinTerm_add]
  exact (hasSum_artinTerm_artinLogL f₁ hs).add (hasSum_artinTerm_artinLogL f₂ hs)

theorem artinL_add (f₁ f₂ : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinL K L (f₁ + f₂) s = artinL K L f₁ s * artinL K L f₂ s := by
  rw [artinL, artinLogL_add f₁ f₂ hs, Complex.exp_add, artinL, artinL]







end Additivity

section Conjugation




end Conjugation

end GroundTheory.Global
