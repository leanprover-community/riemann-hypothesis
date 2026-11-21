import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupDedekindAlgClosedDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExcisionNbhdAdjoinRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosedStatement

section
open GlobalTheory.EtC

namespace GlobalTheory.DivUnitForm

private lemma exists_sub_mem_span_pow_of_surj_mod_span {B A₂ : Type} [CommRing B] [CommRing A₂] [Algebra B A₂]
    (f : B) (hsurj : ∀ a' : A₂, ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f})
    (n : ℕ) (a' : A₂) : ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f ^ n} := by
  induction n generalizing a' with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih a'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨a₁, ha₁⟩ := hsurj r
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 ha₁
    refine ⟨a + f ^ n * a₁, Ideal.mem_span_singleton'.2 ⟨s, ?_⟩⟩
    have hr' : a' = r * algebraMap B A₂ f ^ n + algebraMap B A₂ a := by rw [hr]; ring
    have hs' : r = s * algebraMap B A₂ f + algebraMap B A₂ a₁ := by rw [hs]; ring
    rw [hr', hs', map_add, map_mul, map_pow]
    ring

theorem _root_.GlobalTheory.DivUnitForm.unit_form : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂]
    [Algebra B A₂] (f : B), _root_.GlobalTheory.EtC.IsExcisionNbhd B A₂ f →
    ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂),
      e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) =
        (c : Localization.Away (algebraMap B A₂ f)) *
          algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  intro B A₂ _ _ _ f hf c
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    (c : Localization.Away (algebraMap B A₂ f))
  obtain ⟨l, y, hy⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
  have hxy : algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (x * y) =
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f ^ (k + l)) := by
    rw [map_mul, ← hx, ← hy, map_pow, pow_add]
    have hc : (c : Localization.Away (algebraMap B A₂ f)) *
        ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
          = 1 := Units.mul_inv c
    linear_combination (algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
      (algebraMap B A₂ f) ^ k * algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
        (algebraMap B A₂ f) ^ l) * hc
  obtain ⟨⟨s, hs⟩, hsxy⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap B A₂ f))
    (Localization.Away (algebraMap B A₂ f))).1 hxy
  obtain ⟨N, rfl⟩ := hs
  simp only at hsxy
  set X := x * algebraMap B A₂ f ^ N with hX
  have hXy : X * y = algebraMap B A₂ f ^ (k + N + l) := by
    rw [hX, show k + N + l = N + (k + l) by ring, pow_add]
    linear_combination hsxy
  obtain ⟨b, hb⟩ := exists_sub_mem_span_pow_of_surj_mod_span f hf.2.1 (k + N + l + 1) X
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨b, k + N, 1 - algebraMap B A₂ f * y * r, Ideal.mem_span_singleton'.2 ⟨-(y * r), by ring⟩, ?_⟩
  have hbX : algebraMap B A₂ b = X * (1 - algebraMap B A₂ f * y * r) := by
    have h1 : X * (1 - algebraMap B A₂ f * y * r) = X - algebraMap B A₂ f * r * (X * y) := by ring
    rw [h1, hXy]
    linear_combination hr
  rw [hbX, hX]
  simp only [map_mul, map_pow]
  rw [← hx]
  ring

end GlobalTheory.DivUnitForm
end

section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_form_localization_etale_nbhd : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂] [Algebra B A₂] (f : B), IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧ algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  first | (exact @GlobalTheory.DivUnitForm.unit_form) | (exact GlobalTheory.DivUnitForm.unit_form) | (intros; apply GlobalTheory.DivUnitForm.unit_form  <;> assumption)
end

section
open scoped nonZeroDivisors
open GlobalTheory.EtC

namespace GlobalTheory.KummerDiv

variable {B : Type} [CommRing B] [IsDedekindDomain B]

theorem artinian_quot {I : Ideal B} (hI : I ≠ ⊥) : IsArtinianRing (B ⧸ I) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : (p.comap (Ideal.Quotient.mk I)).IsMaximal := by
    refine Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance
    intro h
    apply hI
    rw [eq_bot_iff, ← h]
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

theorem exists_split (f b : B) (hb : b ≠ 0) :
    ∃ (N : ℕ) (Q : Ideal B), Ideal.span {b} = (Ideal.span {b} ⊔ Ideal.span {f ^ N}) * Q ∧
      Q ⊔ Ideal.span {f} = ⊤ := by
  haveI := artinian_quot (I := Ideal.span {b}) (by simpa using hb)
  obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
    (Ideal.Quotient.mk (Ideal.span {b}) f) (1 : B ⧸ Ideal.span {b})
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmem : f ^ N - f ^ (N + 1) * y' ∈ Ideal.span {b} := by
    rw [← Ideal.Quotient.eq]
    simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
    rw [map_mul, map_pow, map_pow, hy]
  set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef
  have hbP : Ideal.span {b} ≤ P := le_sup_left
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hbP
  refine ⟨N, Q, hQ, ?_⟩
  have hP0 : P ≠ 0 := by
    intro h
    apply hb
    have : b ∈ P := hbP (Ideal.mem_span_singleton_self b)
    rw [h] at this
    simpa using this
  have key : P * (Q ⊔ Ideal.span {f}) = P * ⊤ := by
    rw [Ideal.mul_top, Ideal.mul_sup, ← hQ]
    apply le_antisymm
    · exact sup_le hbP Ideal.mul_le_left
    · apply sup_le le_sup_left
      rw [Ideal.span_singleton_le_iff_mem]
      have e : f ^ N = (f ^ N - f ^ (N + 1) * y') + f ^ N * y' * f := by ring
      rw [e]
      refine add_mem (Ideal.mem_sup_left hmem) (Ideal.mem_sup_right ?_)
      exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ (Ideal.mem_sup_right
        (Ideal.mem_span_singleton_self _))) (Ideal.mem_span_singleton_self f)
  exact mul_left_cancel₀ hP0 key

theorem exists_mem_coprime {I : Ideal B} (hI : I ≠ ⊥) (f : B) (h : I ⊔ Ideal.span {f} = ⊤) :
    ∃ g ∈ I, g ≠ 0 ∧ IsCoprime f g := by
  have h1 : (1 : B) ∈ I ⊔ Ideal.span {f} := h ▸ Submodule.mem_top
  obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  by_cases ha0 : a = 0
  · subst ha0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨x, hx, hx0, ⟨c, 0, by simpa using hay⟩⟩
  · exact ⟨a, ha, ha0, ⟨c, 1, by linear_combination hay⟩⟩

theorem isCoprime_ideal_of_le {I J J' : Ideal B} (h : IsCoprime I J) (hle : J ≤ J') :
    IsCoprime I J' := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact eq_top_iff.2 (h ▸ sup_le_sup_left hle I)

end GlobalTheory.KummerDiv

namespace GlobalTheory.KummerDiv

variable {B : Type} [CommRing B] [IsDedekindDomain B]

theorem core (q : ℕ) (hq : q ≠ 0) (hdiv : ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c)
    (f b : B) (hf : f ≠ 0) (hb : b ≠ 0) :
    ∃ (g n t w : B) (N : ℕ), g ≠ 0 ∧ IsCoprime f g ∧ IsCoprime f n ∧ IsCoprime g w ∧
      b ∣ f ^ N * g ∧ n ∣ g ^ q ∧ b * t ^ q = n * w := by
  obtain ⟨N, Q, hQ, hQf⟩ := exists_split f b hb
  set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hb
    simpa using hQ
  have hf0 : Ideal.span {f} ≠ ⊥ := by simpa using hf
  let Q' : (Ideal B)⁰ := ⟨Q, mem_nonZeroDivisors_of_ne_zero hQ0⟩
  obtain ⟨c, hc⟩ := hdiv (ClassGroup.mk0 Q')⁻¹
  obtain ⟨J, hJf, hJc⟩ := GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hf0 c
  have hmemQJ : Q * (J : Ideal B) ^ q ∈ (Ideal B)⁰ := (Q' * J ^ q).2
  have h1 : ClassGroup.mk0 ⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ = 1 := by
    have : (⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ : (Ideal B)⁰) = Q' * J ^ q := Subtype.ext (by simp [Q'])
    rw [this, map_mul, map_pow, hJc, hc, mul_inv_cancel]
  obtain ⟨n, hn⟩ := ((ClassGroup.mk0_eq_one_iff hmemQJ).1 h1).principal
  have hn' : Q * (J : Ideal B) ^ q = Ideal.span {n} := hn
  have hJ0 : (J : Ideal B) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Q * (J : Ideal B) ^ q = ⊥ := by rw [hn']; simp
    rcases Ideal.mul_eq_bot.1 this with h | h
    · exact hQ0 h
    · exact hJ0 (pow_eq_zero_iff hq |>.1 h)

  have cQ : IsCoprime (Ideal.span {f}) Q := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hQf
  have cJ : IsCoprime (Ideal.span {f}) (J : Ideal B) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hJf
  have hfn : IsCoprime f n := by
    rw [← Ideal.isCoprime_span_singleton_iff, ← hn']
    exact cQ.mul_right (cJ.pow_right)

  have hQJ0 : Q * (J : Ideal B) ≠ ⊥ := mul_ne_zero hQ0 hJ0
  have hQJf : Q * (J : Ideal B) ⊔ Ideal.span {f} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq]; exact (cQ.mul_right cJ).symm
  obtain ⟨g, hgQJ, hg0, hfg⟩ := exists_mem_coprime hQJ0 f hQJf

  have hg0' : Ideal.span {g} ≠ ⊥ := by simpa using hg0
  obtain ⟨J₂, hJ₂g, hJ₂c⟩ := GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hg0' (ClassGroup.mk0 J)⁻¹
  have hmemJJ : (J : Ideal B) * (J₂ : Ideal B) ∈ (Ideal B)⁰ := (J * J₂).2
  have h2 : ClassGroup.mk0 ⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ = 1 := by
    have : (⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ : (Ideal B)⁰) = J * J₂ := rfl
    rw [this, map_mul, hJ₂c, mul_inv_cancel]
  obtain ⟨t, ht⟩ := ((ClassGroup.mk0_eq_one_iff hmemJJ).1 h2).principal
  have ht' : (J : Ideal B) * (J₂ : Ideal B) = Ideal.span {t} := ht

  have hspan : Ideal.span {b * t ^ q} = Ideal.span {n} * (P * (J₂ : Ideal B) ^ q) := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ← ht', hQ, ← hn',
      mul_pow]
    ring
  have hdvd : n ∣ b * t ^ q := by
    rw [← Ideal.mem_span_singleton]
    have hle : Ideal.span {b * t ^ q} ≤ Ideal.span {n} := hspan ▸ Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self _)
  obtain ⟨w, hw⟩ := hdvd
  have hn0' : Ideal.span {n} ≠ 0 := by simpa using hn0
  have hwspan : Ideal.span {w} = P * (J₂ : Ideal B) ^ q := by
    apply mul_left_cancel₀ hn0'
    rw [Ideal.span_singleton_mul_span_singleton, ← hw, hspan]
  have cgP : IsCoprime (Ideal.span {g}) P := by
    apply isCoprime_ideal_of_le _ (le_sup_right : Ideal.span {f ^ N} ≤ P)
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hfg.symm.pow_right
  have cgJ₂ : IsCoprime (Ideal.span {g}) (J₂ : Ideal B) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hJ₂g
  have hgw : IsCoprime g w := by
    rw [← Ideal.isCoprime_span_singleton_iff, hwspan]
    exact cgP.mul_right cgJ₂.pow_right
  refine ⟨g, n, t, w, N, hg0, hfg, hfn, hgw, ?_, ?_, hw⟩
  · rw [← Ideal.mem_span_singleton, hQ]
    exact Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      ((Ideal.mul_le_left : Q * (J : Ideal B) ≤ Q) hgQJ)
  · rw [← Ideal.mem_span_singleton, ← hn']
    have : g ^ q ∈ (Q * (J : Ideal B)) ^ q := Ideal.pow_mem_pow hgQJ q
    rw [mul_pow] at this
    exact Ideal.mul_mono_left (Ideal.pow_le_self hq) this

end GlobalTheory.KummerDiv

namespace GlobalTheory.KummerDiv

theorem divisor_step : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b : B, b ≠ 0 →
    ∀ m : ℕ, ∃ g : B, g ≠ 0 ∧ IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ,
      ∃ n d t n' d' : B, IsCoprime f n ∧ IsCoprime f d ∧ IsCoprime g n' ∧ IsCoprime g d' ∧
      algebraMap B (Localization.Away (f * g)) (b * d) =
        (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) ∧
      (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') =
        algebraMap B (Localization.Away (f * g)) n' := by
  intro k B _ _ _ _ _ _ q hq f hf b hb m
  have hqk : (q : k) ≠ 0 := hq.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hqk (by simp)
  have hdiv : ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := GlobalTheory.T.classGroup_dedekind_algClosed_divisible k B q hqk
  obtain ⟨g, n, t, w, N, hg0, hfg, hfn, hgw, hbd, hnd, hw⟩ := core q hq0 hdiv f b hf hb
  refine ⟨g, hg0, hfg, ?_⟩
  set L := Localization.Away (f * g)
  have hfgU : IsUnit (algebraMap B L (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgU
  have hfU : IsUnit (algebraMap B L f) := isUnit_of_mul_isUnit_left hfgU
  have hgU : IsUnit (algebraMap B L g) := isUnit_of_mul_isUnit_right hfgU
  have hbU : IsUnit (algebraMap B L b) := by
    refine isUnit_of_dvd_unit (map_dvd (algebraMap B L) hbd) ?_
    rw [map_mul, map_pow]
    exact (hfU.pow N).mul hgU
  have hnU : IsUnit (algebraMap B L n) := by
    refine isUnit_of_dvd_unit (map_dvd (algebraMap B L) hnd) ?_
    rw [map_pow]
    exact hgU.pow q
  set un := (hnU.mul (hfU.pow m)).unit with hun
  have hv : (algebraMap B L n * algebraMap B L f ^ m) * ((un⁻¹ : Lˣ) : L) = 1 := by
    have : (un : L) = algebraMap B L n * algebraMap B L f ^ m := rfl
    rw [← this]; exact Units.mul_inv un
  refine ⟨hbU.unit * un⁻¹, n, 1, t, w, f ^ m, hfn, isCoprime_one_right, hgw, hfg.symm.pow_right, ?_, ?_⟩
  · have hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b := rfl
    rw [Units.val_mul, hb', map_mul, map_mul, map_one, map_pow]
    linear_combination (-(algebraMap B L b)) * hv
  · have hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b := rfl
    have hw' := congrArg (algebraMap B L) hw
    simp only [map_mul, map_pow] at hw'
    rw [Units.val_mul, hb', map_mul, map_pow, map_pow]
    linear_combination (((un⁻¹ : Lˣ) : L) * algebraMap B L f ^ m) * hw' + algebraMap B L w * hv

end GlobalTheory.KummerDiv
end

section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b : B, b ≠ 0 → ∀ m : ℕ, ∃ g : B, g ≠ 0 ∧ IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, ∃ n d t n' d' : B, IsCoprime f n ∧ IsCoprime f d ∧ IsCoprime g n' ∧ IsCoprime g d' ∧ algebraMap B (Localization.Away (f * g)) (b * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) ∧ (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' := by
  first | (exact @GlobalTheory.KummerDiv.divisor_step) | (exact GlobalTheory.KummerDiv.divisor_step) | (intros; apply GlobalTheory.KummerDiv.divisor_step  <;> assumption)
end

section
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_eq_mul_qth_power_near_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  intro k B _ _ _ _ _ _ q hq f hf A₂ _ _ hA₂ c b₁ m e he hc g hg u n d hn hd hu
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x₁, y₁, hxy₁⟩ := (hg.mul_right hn).mul_right hd
  obtain ⟨a, ha⟩ : ∃ a : A₂, a = algebraMap B A₂ (g * n * d) * e := ⟨_, rfl⟩
  have hab : a * algebraMap B A₂ y₁ - 1 ∈ Ideal.span {algebraMap B A₂ f} := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp he
    have h1 := congrArg (algebraMap B A₂) hxy₁
    simp only [map_add, map_mul, map_one] at h1
    rw [Ideal.mem_span_singleton, ha]
    refine ⟨-(algebraMap B A₂ x₁) * e + t, ?_⟩
    simp only [map_mul]
    linear_combination e * h1 + ht
  have hA₂' : IsExcisionNbhd B (Localization.Away a) f := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA₂ a (algebraMap B A₂ y₁) hab
  have hdvd : ∀ z : A₂, z ∣ a → IsUnit (algebraMap A₂ (Localization.Away a) z) := fun z hz =>
    isUnit_of_dvd_unit (map_dvd _ hz) (IsLocalization.Away.algebraMap_isUnit a)
  have hgu := hdvd (algebraMap B A₂ g) ⟨algebraMap B A₂ n * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hnu := hdvd (algebraMap B A₂ n) ⟨algebraMap B A₂ g * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hdu := hdvd (algebraMap B A₂ d) ⟨algebraMap B A₂ g * algebraMap B A₂ n * e, by rw [ha]; simp only [map_mul]; ring⟩
  have heu := hdvd e ⟨algebraMap B A₂ (g * n * d), by rw [ha]; ring⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : A₂, ε₀ = algebraMap B A₂ n * (algebraMap B A₂ d * e) ^ j := ⟨_, rfl⟩
  have hεu : IsUnit (algebraMap A₂ (Localization.Away a) ε₀) := by
    rw [hε₀, map_mul, map_pow, map_mul]; exact hnu.mul ((hdu.mul heu).pow j)
  obtain ⟨x₂, y₂, h₂⟩ := hn.mul_right (hd.pow_right (n := j))
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B (j + 1) hq f hf (n * d ^ j) y₂
    (Ideal.mem_span_singleton.mpr ⟨-x₂, by linear_combination h₂⟩)
  have hcong : ε₀ - algebraMap B A₂ r ^ (j + 1) ∈ Ideal.span {algebraMap B A₂ f} := by
    have h1 : algebraMap B A₂ f ∣ algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) :=
      map_dvd _ (Ideal.mem_span_singleton.mp hr)
    have h2 : algebraMap B A₂ f ∣ e ^ j - 1 :=
      (Ideal.mem_span_singleton.mp he).trans (by simpa using sub_dvd_pow_sub_pow e 1 j)
    have h3 : ε₀ - algebraMap B A₂ r ^ (j + 1) = algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) +
        algebraMap B A₂ n * algebraMap B A₂ d ^ j * (e ^ j - 1) := by
      rw [hε₀]; simp only [map_sub, map_mul, map_pow]; ring
    rw [Ideal.mem_span_singleton, h3]; exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  have hcong' : algebraMap A₂ (Localization.Away a) ε₀ - algebraMap B (Localization.Away a) r ^ (j + 1) ∈
      Ideal.span {algebraMap B (Localization.Away a) f} := by
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) r,
      IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) f, ← map_pow, ← map_sub,
      Ideal.mem_span_singleton]
    exact map_dvd _ (Ideal.mem_span_singleton.mp hcong)
  have hqu : IsUnit ((j + 1 : ℕ) : Localization.Away a) := by
    have := hq.map ((algebraMap B (Localization.Away a)).comp (algebraMap k B)); rwa [map_natCast] at this
  obtain ⟨A₃, _, _, hA₃, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit (Localization.Away a) (algebraMap B (Localization.Away a) f)
    (j + 1) hqu _ _ hεu hcong'
  letI : Algebra B A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap B (Localization.Away a)))
  letI : Algebra A₂ A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap A₂ (Localization.Away a)))
  haveI t1 : IsScalarTower B (Localization.Away a) A₃ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t3 : IsScalarTower B A₂ A₃ := IsScalarTower.of_algebraMap_eq (fun z => by
    show algebraMap (Localization.Away a) A₃ (algebraMap B (Localization.Away a) z) =
      algebraMap (Localization.Away a) A₃ (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ z))
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) z])
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, t3, GlobalTheory.T.isExcisionNbhd_trans' B (Localization.Away a) A₃ f hA₂' hA₃, ?_, ?_⟩
  · have : algebraMap B A₃ g = algebraMap (Localization.Away a) A₃
        (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ g)) := by
      rw [← IsScalarTower.algebraMap_apply B A₂ (Localization.Away a)]; rfl
    rw [this]; exact hgu.map _
  have hDu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f))
      (algebraMap A₂ A₃ (algebraMap B A₂ d * e))) := by
    have hde : IsUnit (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ d * e)) := by
      rw [map_mul]; exact hdu.mul heu
    exact (hde.map (algebraMap (Localization.Away a) A₃)).map _
  have hX : algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x ^ (j + 1) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) *
      (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
       algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j := by
    rw [← map_pow, ← hx]
    show algebraMap A₃ _ (algebraMap A₂ A₃ ε₀) = _
    rw [hε₀]; simp only [map_mul, map_pow]
  have hXu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x) :=
    (isUnit_pow_iff (Nat.succ_ne_zero j)).mp (by rw [← map_pow, ← hx]; exact (hεu.map _).map _)
  have hFu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ f))) := by
    rw [← IsScalarTower.algebraMap_apply B A₂ A₃]; exact IsLocalization.Away.algebraMap_isUnit _
  refine ⟨hXu.unit * hDu.unit⁻¹, fun φ ψ hφ hψ => ?_⟩
  have hφ' : ∀ y, φ (algebraMap A₂ _ y) = algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ y) :=
    fun y => RingHom.congr_fun hφ y
  have hψ' : ∀ z, ψ (algebraMap B _ z) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ z)) := fun z => by
    have := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply] at this
    rw [this, IsScalarTower.algebraMap_apply B A₂ A₃ z]
  have H1 := congrArg φ hc
  have H2 := congrArg ψ hu
  simp only [map_mul, map_pow, hφ'] at H1
  simp only [map_mul, map_pow, hψ'] at H2
  have hW := hDu.mul_val_inv
  rw [Units.val_mul, IsUnit.unit_spec]
  generalize (↑hDu.unit⁻¹ : Localization.Away (algebraMap B A₃ f)) = W at hW ⊢
  simp only [map_mul] at hW hFu
  have key0 : φ c * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) =
      ψ u * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) := by
    apply (hFu.pow m).mul_right_cancel
    linear_combination -(algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d))) * H1 + H2
  calc φ c = φ c * (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) * W) ^ (j + 1) := by
        rw [hW, one_pow, mul_one]
    _ = _ := by
      linear_combination (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j * W ^ (j + 1) * key0 -
        ψ u * W ^ (j + 1) * hX

end GlobalTheory.EtC
end

section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus) | (exact GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus) | (intros; apply GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus <;> assumption)
end

section
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_isPow_on_excisionNbhd : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro k B _ _ _ _ _ _ q hq f g hg u t n' d' hn hd hu
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨a, bn, ha⟩ := hn
  obtain ⟨a', bd, hb⟩ := hd
  have hw : (a * a' * g - a - a') * g = n' * d' * (bn * bd) - 1 := by
    linear_combination (-(bd * d')) * ha + (a * g - 1) * hb
  have hC' : IsExcisionNbhd B (Localization.Away (n' * d')) g :=
    GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B B g (isExcisionNbhd_self B g) (n' * d') (bn * bd)
      (Ideal.mem_span_singleton'.mpr ⟨_, hw⟩)
  set C' := Localization.Away (n' * d') with hC'def
  have hnd : IsUnit (algebraMap B C' (n' * d')) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hnd
  have hnC : IsUnit (algebraMap B C' n') := isUnit_of_mul_isUnit_left hnd
  have hdC : IsUnit (algebraMap B C' d') := isUnit_of_mul_isUnit_right hnd
  set Di : C' := ((hdC.unit⁻¹ : C'ˣ) : C') with hDi
  have hDi1 : Di * algebraMap B C' d' = 1 := by rw [hDi]; exact hdC.val_inv_mul
  set ε : C' := algebraMap B C' n' * Di with hεdef
  have hε : IsUnit ε := hnC.mul (Units.isUnit _)
  have hεd : ε * algebraMap B C' d' = algebraMap B C' n' := by rw [hεdef, mul_assoc, hDi1, mul_one]
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B q hq g hg (n' * bd) (bn * d')
    (Ideal.mem_span_singleton'.mpr ⟨a * a' * g - a - a', by linear_combination hw⟩)
  obtain ⟨w, hw'⟩ := Ideal.mem_span_singleton'.mp hr
  have hqC : IsUnit (q : C') := by simpa using hq.map ((algebraMap B C').comp (algebraMap k B))
  have hεr : ε - algebraMap B C' r ^ q ∈ Ideal.span {algebraMap B C' g} := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap B C' n' * Di * algebraMap B C' a' + algebraMap B C' w, ?_⟩
    have e1 := congrArg (algebraMap B C') hw'
    have e2 := congrArg (algebraMap B C') hb
    simp only [map_mul, map_sub, map_add, map_pow, map_one] at e1 e2
    rw [hεdef]
    linear_combination e1 + (algebraMap B C' n' * Di) * e2 - (algebraMap B C' n' * algebraMap B C' bd) * hDi1
  obtain ⟨C, _, _, hC, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit C' (algebraMap B C' g) q hqC ε (algebraMap B C' r) hε hεr
  letI : Algebra B C := ((algebraMap C' C).comp (algebraMap B C')).toAlgebra
  haveI : IsScalarTower B C' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨C, inferInstance, inferInstance, GlobalTheory.T.isExcisionNbhd_trans' B C' C g hC' hC, ?_⟩
  set L := Localization.Away (algebraMap B C (f * g))
  set ψ : B →+* L := (algebraMap C L).comp (algebraMap B C) with hψ
  set ρ : C' →+* L := (algebraMap C L).comp (algebraMap C' C) with hρ
  have hψρ : ∀ y : B, ψ y = ρ (algebraMap B C' y) := fun _ => rfl
  have hφ : ∀ y : B, Localization.awayMap (algebraMap B C) (f * g)
      (algebraMap B (Localization.Away (f * g)) y) = ψ y := by
    intro y; exact IsLocalization.map_eq _ _
  have hu' : Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d') = ψ n' := by
    have h := congrArg (Localization.awayMap (algebraMap B C) (f * g)) hu
    rw [map_mul (Localization.awayMap (algebraMap B C) (f * g)), hφ, hφ] at h
    rw [← map_pow ψ, ← map_mul ψ]; exact h
  have hnL : IsUnit (ψ n') := by rw [hψρ]; exact hnC.map ρ
  have hdL : IsUnit (ψ d') := by rw [hψρ]; exact hdC.map ρ
  have hεL : ρ ε * ψ d' = ψ n' := by
    have := congrArg ρ hεd; rw [map_mul] at this; rw [hψρ, hψρ]; exact this
  have hxL : algebraMap C L x ^ q = ρ ε := by
    have := congrArg (algebraMap C L) hx; rw [map_pow] at this; exact this.symm
  have hXU : algebraMap C L x ^ q = Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * ψ t ^ q := by
    rw [← hdL.mul_left_inj, hxL, hεL, ← hu', mul_assoc]
  have hTq : IsUnit (ψ t ^ q) := by
    have h : IsUnit (Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d')) := by
      rw [hu']; exact hnL
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)
  have hT : IsUnit (ψ t) := (isUnit_pow_iff hq0).mp hTq
  have hX : IsUnit (algebraMap C L x) := by
    refine (isUnit_pow_iff hq0).mp ?_
    rw [hXU]; exact ((Units.map (Localization.awayMap (algebraMap B C) (f * g) : Localization.Away (f * g) →* L)) u).isUnit.mul hTq
  refine ⟨hX.unit * hT.unit⁻¹, ?_⟩
  rw [Units.val_mul, mul_pow, IsUnit.unit_spec, hXU, mul_assoc, ← mul_pow, hT.mul_val_inv, one_pow, mul_one]

end GlobalTheory.EtC
end

section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coprime_unit_etale_extension : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (exact GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (intros; apply GlobalTheory.EtC.unit_isPow_on_excisionNbhd  <;> assumption)
end

section
namespace GlobalTheory.EtC

theorem kummer_divisor_step : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro q k B _ _ _ _ _ _ hq f hf A₂ _ _ hA c
  obtain ⟨b₁, m, e, he, hc⟩ := GlobalTheory.T.exists_unit_form_localization_etale_nbhd B A₂ f hA c
  by_cases hb : b₁ = 0
  · refine ⟨1, isCoprime_one_right, 1, ?_, ⟨B, inferInstance, inferInstance, isExcisionNbhd_self B 1, 1, by simp⟩⟩
    have hL := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA e 1 (by simpa using he)
    refine ⟨Localization.Away e, inferInstance, inferInstance, inferInstance, inferInstance, hL, by simp, 1, ?_⟩
    intro φ ψ hφ hψ
    subst hb
    have hc' := congrArg φ hc
    simp only [map_zero, map_mul, map_pow] at hc'
    have hx : IsUnit (φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) e) *
        φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f)) ^ m) := by
      have h1 : ∀ y : A₂, φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) y) =
          algebraMap (Localization.Away e) _ (algebraMap A₂ (Localization.Away e) y) := fun y => by
        rw [← RingHom.comp_apply, hφ]; rfl
      rw [h1, h1]
      refine IsUnit.mul ((IsLocalization.Away.algebraMap_isUnit e).map _) (IsUnit.pow _ ?_)
      rw [← IsScalarTower.algebraMap_apply]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (Localization.Away e) f)) (algebraMap B (Localization.Away e) f)
    have hu := (c.isUnit.map φ).mul hx
    rw [← hc'] at hu
    haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
    exact Subsingleton.elim _ _
  · obtain ⟨g, hg0, hfg, u, n, d, t, n', d', hn, hd, hn', hd', h1, h2⟩ := GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition k B q hq f hf b₁ hb m
    exact ⟨g, hfg, u, GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus k B q hq f hf A₂ hA c b₁ m e he hc g hfg u n d hn hd h1,
      GlobalTheory.T.coprime_unit_etale_extension k B q hq f g hg0 u t n' d' hn' hd' h2⟩

end GlobalTheory.EtC
end

section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.kummer_divisor_step) | (exact GlobalTheory.EtC.kummer_divisor_step) | (intros; apply GlobalTheory.EtC.kummer_divisor_step <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.KummerStep

noncomputable abbrev gU (A : Type) [CommRing A] : Aˣ →* (Γ(Spec (CommRingCat.of A), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isUnit_natCast_of {k R : Type} [Field k] [CommRing R] (φ : k →+* R) {q : ℕ} (hq : IsUnit (q : k)) :
    IsUnit (q : R) := by
  simpa using hq.map φ

theorem kum_spMap (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hq : IsUnit (q : A))
    (u : Aˣ) : pull _ (spMap φ) _ _ (kum q (gU A u)) = kum q (gU B (Units.map φ.toMonoidHom u)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [(GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.2.2 (Spec.map (CommRingCat.ofHom φ)) (gU A u) hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 : (Spec.map (CommRingCat.ofHom φ)).appTop = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← h]; simp
  simp only [gU, Units.coe_map, MonoidHom.coe_coe]
  rw [h2]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  simp

theorem kum_pow_eq (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (u v : Aˣ) :
    kum q (gU A (u * v ^ q)) = kum q (gU A u) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [map_mul, map_pow, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A u) _ hq').1, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A v) (gU A v) hq').2, add_zero]

theorem kum_pow (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (v : Aˣ) :
    kum q (gU A (v ^ q)) = 0 := by
  have := kum_pow_eq q hq 1 v
  rw [one_mul] at this
  rw [this, map_one]
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have h := ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hq').1
  rw [one_mul] at h
  simpa using h

theorem of_steps (L1 : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c) (L2 : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q) : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  intro q _ k B _ _ _ _ _ _ hq f hf A' _ _ hA' w
  obtain ⟨A₂, _, _, _, _, hA₂, c, hc⟩ := L1 q k B hq f hf A' hA' w
  set c₀ : (Localization.Away (algebraMap B A₂ f))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (algebraMap B A₂ f)))).hom.hom.toMonoidHom c with hc₀
  have hcc : gU _ c₀ = c := by
    ext; simp [c₀, gU]
  obtain ⟨g, hfg, u, ⟨A₃, _, _, _, _, hA₃, hg, v, hv⟩, C, _, _, hC, v', hv'⟩ := L2 q k B hq f hf A₂ hA₂ c₀
  letI : Algebra A' A₃ := ((algebraMap A₂ A₃).comp (algebraMap A' A₂)).toAlgebra
  haveI : IsScalarTower B A' A₃ := IsScalarTower.of_algebraMap_eq (fun b => by
    show algebraMap B A₃ b = algebraMap A₂ A₃ (algebraMap A' A₂ (algebraMap B A' b))
    rw [← IsScalarTower.algebraMap_apply B A' A₂, ← IsScalarTower.algebraMap_apply B A₂ A₃])
  have hkB : ∀ (R : Type) [CommRing R] [Algebra B R], IsUnit (q : R) := fun R _ _ =>
    isUnit_natCast_of ((algebraMap B R).comp (algebraMap k B)) hq
  refine ⟨g, hfg, A₃, C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hA₃, hg, hC, kum q (gU _ u), ?_, ?_⟩
  · rw [kum_spMap q _ (hkB _)]
    have : Units.map (Localization.awayMap (algebraMap B C) (f * g)).toMonoidHom u = v' ^ q := by
      ext; simpa using hv'
    rw [this]
    exact kum_pow q (hkB _) v'
  · intro φ ψ hφ hψ
    have hu₁ : IsUnit (((algebraMap A₂ (Localization.Away (algebraMap B A₂ f))).comp (algebraMap A' A₂))
        (algebraMap B A' f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hu₂ : IsUnit (((algebraMap A₃ (Localization.Away (algebraMap B A₃ f))).comp (algebraMap A₂ A₃))
        (algebraMap B A₂ f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A₂ A₃]
      exact IsLocalization.Away.algebraMap_isUnit _
    set φ₁ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f) :=
      IsLocalization.Away.lift (algebraMap B A' f) hu₁
    set φ₂ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f) :=
      IsLocalization.Away.lift (algebraMap B A₂ f) hu₂
    have hφ₁ : φ₁.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A' f)) (algebraMap B A' f) hu₁
    have hφ₂ : φ₂.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) hu₂
    have hφe : φ = φ₂.comp φ₁ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) ?_
      rw [hφ, RingHom.comp_assoc, hφ₁, ← RingHom.comp_assoc, hφ₂, RingHom.comp_assoc]
      rfl
    have key := hv φ₂ ψ hφ₂ hψ
    have hkey : Units.map φ₂.toMonoidHom c₀ = Units.map ψ.toMonoidHom u * v ^ q := by
      ext; simpa using key
    rw [hφe, spMap_comp', pull_comp, hc φ₁ hφ₁, ← hcc, kum_spMap q φ₂ (hkB _), hkey, kum_pow_eq q (hkB _),
      kum_spMap q ψ (hkB _)]

theorem exists_class_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a :=
  of_steps GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow

end GlobalTheory.EtC.KummerStep
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerClass_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  first | (exact @GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros) | (exact GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros) | (intros; apply GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros <;> assumption)
end
