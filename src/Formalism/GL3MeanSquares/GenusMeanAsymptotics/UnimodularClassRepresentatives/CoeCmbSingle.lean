import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def InP (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : K) : Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k, jK z = jK (ι t) * a

theorem congrP_iff_inP (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a b : K) : CongrP 𝔭 k a b ↔ InP 𝔭 k (a - b) := by
  have e : ∀ t : 𝓞 F, jK (ι t) = algebraMap F K (t : F) := fun t => rfl
  simp only [CongrP, InP, e]

theorem jK_inj : Function.Injective (jK) := fun a b hab => RingOfIntegers.ext hab

theorem InP.add {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, ι t₂ * z₁ + ι t₁ * z₂,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz₁) (Ideal.mul_mem_left _ _ hz₂), ?_⟩
  simp only [map_add, map_mul, e₁, e₂]
  ring

theorem InP.neg {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) : InP 𝔭 k (-a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, -z, neg_mem hz, by rw [map_neg, e, mul_neg]⟩

theorem InP.mul {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k l : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 l b) : InP 𝔭 (k + l) (a * b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, z₁ * z₂, ?_, ?_⟩
  · rw [pow_add]
    exact Ideal.mul_mem_mul hz₁ hz₂
  · simp only [map_mul, e₁, e₂]
    ring

theorem InP.mono {𝔭 : Ideal (𝓞 F)} {k l : ℕ} (hkl : l ≤ k) {a : K} (ha : InP 𝔭 k a) : InP 𝔭 l a := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, z, Ideal.pow_le_pow_right hkl hz, e⟩

theorem inP_jK {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    InP 𝔭 k (jK z) := ⟨1, (Ideal.ne_top_iff_one _).mp h𝔭.ne_top, z, hz, by rw [map_one, map_one, one_mul]⟩

def SP (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subring K where
  carrier := {a | InP 𝔭 0 a}
  mul_mem' := fun ha hb => ha.mul hb
  one_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 1) (by simp)
    rwa [map_one] at this
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 0) (by simp)
    rwa [map_zero] at this
  neg_mem' := fun ha => ha.neg

theorem mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z : 𝓞 K, jK z = jK (ι t) * a := by
  show InP 𝔭 0 a ↔ _
  constructor
  · rintro ⟨t, ht, z, -, e⟩
    exact ⟨t, ht, z, e⟩
  · rintro ⟨t, ht, z, e⟩
    exact ⟨t, ht, z, by simp, e⟩

theorem mem_SP_iff_locF {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ a ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have hp : 𝔭.IsPrime := inferInstance
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one _).mp hp.ne_top, map_one _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t₁, ht₁, rfl⟩ := hx
      obtain ⟨t₂, ht₂, rfl⟩ := hy
      exact ⟨t₁ * t₂, fun hm => (hp.mem_or_mem hm).elim ht₁ ht₂, map_mul _ _ _⟩
  change a ∈ SP K 𝔭 ↔ ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
    s • a ∈ (1 : Submodule (𝓞 K) K)
  rw [mem_SP]
  constructor
  · rintro ⟨t, ht, z, e⟩
    refine ⟨ι t, Submonoid.subset_closure ⟨t, ht, rfl⟩, ?_⟩
    rw [Submodule.mem_one]
    exact ⟨z, by rw [e, Algebra.smul_def]⟩
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨t, ht, rfl⟩ := key s hs
    rw [Submodule.mem_one] at hsa
    obtain ⟨z, hz⟩ := hsa
    exact ⟨t, ht, z, by rw [hz, Algebra.smul_def]⟩

theorem jK_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (z : 𝓞 K) : jK z ∈ SP K 𝔭 := mem_SP.mpr ⟨1, (Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top inferInstance), z,
  by rw [map_one, map_one, one_mul]⟩

theorem InP.mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a : K} (ha : InP 𝔭 k a) : a ∈ SP K 𝔭 := ha.mono (Nat.zero_le _)

theorem InP.conj (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) :
    InP 𝔭 k (star a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  have hι : ∀ c : 𝓞 F, conjO K (ι c) = ι c := by
    intro c
    apply RingOfIntegers.ext
    show star (algebraMap F K (c : F)) = algebraMap F K (c : F)
    exact (hF _).mpr ⟨_, rfl⟩
  have hι' : (conjO K).comp (algebraMap (𝓞 F) (𝓞 K)) = algebraMap (𝓞 F) (𝓞 K) := RingHom.ext hι
  refine ⟨t, ht, conjO K z, ?_, ?_⟩
  · have h1 : conjO K z ∈ (extP K 𝔭 ^ k).map (conjO K) := Ideal.mem_map_of_mem _ hz
    rwa [Ideal.map_pow, extP, Ideal.map_map, hι'] at h1
  · have s1 : jK (conjO K z) = star (jK z) := rfl
    have s2 : star (jK (ι t)) = jK (ι t) := (hF _).mpr ⟨_, rfl⟩
    rw [s1, e, star_mul, s2, mul_comm]

theorem exists_unif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ π₀ ∈ 𝔭, π₀ ∉ 𝔭 ^ 2 ∧ ∃ s₀ : 𝓞 F, s₀ ∉ 𝔭 ∧ Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀} := by
  have hne : 𝔭 ≠ ⊥ := fun h0 =>
    RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h0 ▸ h𝔭))
  obtain ⟨π₀, hπ1, hπ2⟩ : ∃ x ∈ 𝔭 ^ 1, x ∉ 𝔭 ^ (1 + 1) := by
    have hlt : 𝔭 ^ (1 + 1) < 𝔭 ^ 1 := Ideal.pow_succ_lt_pow hne 1
    obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx1, hx2⟩
  rw [pow_one] at hπ1
  have hπ2' : π₀ ∉ 𝔭 ^ 2 := hπ2
  obtain ⟨J, hJ⟩ : 𝔭 ∣ Ideal.span {π₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ1)
  have hJ𝔭 : ¬ J ≤ 𝔭 := by
    intro hle
    apply hπ2'
    have h3 : Ideal.span {π₀} ≤ 𝔭 ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hle
    exact h3 (Ideal.subset_span rfl)
  obtain ⟨s₀, hsJ, hs𝔭⟩ := SetLike.not_le_iff_exists.mp hJ𝔭
  refine ⟨π₀, hπ1, hπ2', s₀, hs𝔭, ?_⟩
  rw [hJ, mul_comm 𝔭 J]
  exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)

theorem span_pow_mul_le {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F}
    (h : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}) (k : ℕ) :
    Ideal.span {ι (s₀ ^ k)} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π₀ ^ k)} := by
  have h1 : (Ideal.span {s₀} * 𝔭) ^ k ≤ Ideal.span {π₀} ^ k := Ideal.pow_right_mono h k
  rw [mul_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h1
  have h2 := Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) h1
  rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.map_pow] at h2
  exact h2

end Formalism.HermitianLattices.Ext.L3.HU
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

structure IsUnif0 (𝔭 : Ideal (𝓞 F)) (π₀ s₀ : 𝓞 F) : Prop where
  mem : π₀ ∈ 𝔭
  notMem : π₀ ∉ 𝔭 ^ 2
  s_notMem : s₀ ∉ 𝔭
  le : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}

theorem exists_isUnif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ π₀ s₀, IsUnif0 𝔭 π₀ s₀ := by
  obtain ⟨π₀, h1, h2, s₀, h3, h4⟩ := exists_unif0 h𝔭
  exact ⟨π₀, s₀, ⟨h1, h2, h3, h4⟩⟩

theorem jι_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  intro h0
  apply ha
  have h1 : algebraMap F K (a : F) = 0 := h0
  rw [map_eq_zero] at h1
  first
  | exact_mod_cast h1
  | exact RingOfIntegers.ext h1

theorem IsUnif0.ne_zero {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) : π₀ ≠ 0 := by
  rintro rfl
  exact hu.notMem (Submodule.zero_mem _)

theorem ne_zero_of_notMem {𝔭 : Ideal (𝓞 F)} {t : 𝓞 F} (ht : t ∉ 𝔭) : t ≠ 0 := by
  rintro rfl
  exact ht (Submodule.zero_mem _)

theorem mem_noncompactPart_iff {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) (k : ℕ)
    (a : K) : InP 𝔭 k a ↔ ∃ s ∈ SP K 𝔭, a = jK (ι π₀) ^ k * s := by
  have hp : 𝔭.IsPrime := h𝔭
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have hmem : ι (s₀ ^ k) * z ∈ Ideal.span {ι (π₀ ^ k)} :=
      span_pow_mul_le hu.le k (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    have htu : t * s₀ ^ k ∉ 𝔭 := fun hm =>
      (hp.mem_or_mem hm).elim ht (fun h => hu.s_notMem (hp.mem_of_pow_mem k h))
    have hd : jK (ι (t * s₀ ^ k)) ≠ 0 := jι_ne_zero (ne_zero_of_notMem htu)
    refine ⟨jK w / jK (ι (t * s₀ ^ k)), mem_SP.mpr ⟨t * s₀ ^ k, htu, w, ?_⟩, ?_⟩
    · rw [mul_div_assoc', eq_div_iff hd, mul_comm]
    · have hw' := congrArg jK hw
      simp only [map_mul, map_pow] at hw'
      rw [mul_div_assoc', eq_div_iff hd]
      simp only [map_mul, map_pow]
      linear_combination -hw' - jK (ι s₀) ^ k * e
  · rintro ⟨s, hs, rfl⟩
    have h1 : InP 𝔭 k (jK (ι π₀) ^ k) := by
      rw [← map_pow]
      exact inP_jK (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hu.mem) k)
    have h2 := h1.mul (show InP 𝔭 0 s from hs)
    simpa using h2

theorem exists_norm (hF : IsFixF K F) (u : 𝓞 K) : ∃ n₀ : 𝓞 F, ι n₀ = u * conjO K u := by
  have hs : star (jK (u * conjO K u)) = jK (u * conjO K u) := by
    rw [map_mul]
    show star (jK u * star (jK u)) = jK u * star (jK u)
    rw [star_mul, star_star, mul_comm]
  obtain ⟨f, hf⟩ := (hF _).mp hs
  have hint : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap F K f) := by
      rw [hf]
      exact (u * conjO K u).isIntegral_coe
    exact (isIntegral_algHom_iff ((algebraMap F K).toIntAlgHom) (algebraMap F K).injective).mp h1
  exact ⟨⟨f, hint⟩, RingOfIntegers.ext hf⟩

theorem isLocUnif (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) [hp : 𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀) :
    IsLocUnif (SP K 𝔭) (jK (ι π₀)) where
  star_mem := fun a ha => InP.conj hF ha
  mem := jK_mem_SP _
  fix := star_ι hF _
  ne := jι_ne_zero hu.ne_zero
  tr := by
    obtain ⟨z, hz⟩ := exists_add_conj_eq hK hF (1 : 𝓞 F)
    refine ⟨jK z, jK_mem_SP _, ?_⟩
    have := congrArg jK hz
    rw [map_add, map_one, map_one] at this
    exact this
  skew := by
    obtain ⟨P, hP, -⟩ := exists_maximal_over hK hF h𝔭
    obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    refine ⟨jK (θ - conjO K θ), jK_mem_SP _, ?_, ?_⟩
    · have : star (jK (θ - conjO K θ)) = jK (conjO K (θ - conjO K θ)) := rfl
      rw [this, map_sub, L3.conjO_conjO, ← map_neg]
      congr 1
      ring
    · intro h
      apply hθ
      rw [jK_inj (h.trans (map_zero _).symm)]
      exact zero_mem _
  dv := by
    intro f hf hfix
    obtain ⟨t, ht, z, e⟩ := mem_SP.1 hf
    have hzfix : conjO K z = z := by
      apply jK_inj
      have : jK (conjO K z) = star (jK z) := rfl
      rw [this, e, star_mul', star_ι hF, hfix]
    obtain ⟨z₀, rfl⟩ := (conjO_eq_iff_mem_range hF z).1 hzfix
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    by_cases hz : z₀ ∈ 𝔭
    · right
      have h1 := hu.le (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self s₀) hz)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
      refine mem_SP.2 ⟨t * s₀, fun h => (hp.mem_or_mem h).elim ht hu.s_notMem, ι y, ?_⟩
      have hϖ : jK (ι π₀) ≠ 0 := jι_ne_zero hu.ne_zero
      have h2 := congrArg (fun x => jK (ι x)) hy
      simp only [map_mul] at h2 ⊢
      field_simp
      rw [h2, e]
      ring
    · left
      have hz0 : jK (ι z₀) ≠ 0 := jι_ne_zero (ne_zero_of_notMem hz)
      have hf0 : f ≠ 0 := by
        rintro rfl
        rw [mul_zero] at e
        exact hz0 e
      refine mem_SP.2 ⟨z₀, hz, ι t, ?_⟩
      rw [e]
      field_simp
  rad := by
    intro s hs
    obtain ⟨t, ht, z, e⟩ := mem_SP.1 hs
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    obtain ⟨n₀, hn₀⟩ := exists_norm hF (ι t + ι π₀ * z)
    have hn : n₀ ∉ 𝔭 := by
      intro hmem
      have h1 : ι (n₀ - t * t) ∈ extP K 𝔭 ^ 1 := by
        have : ι (n₀ - t * t) = ι π₀ * (z * ι t + ι t * conjO K z + ι π₀ * z * conjO K z) := by
          rw [map_sub, hn₀, map_add, map_mul (conjO K), conjO_map hF, conjO_map hF, map_mul]
          ring
        rw [this]
        exact Ideal.mul_mem_right _ _ (ι_mem_pow (by rw [pow_one]; exact hu.mem))
      rw [mem_pow_iff, pow_one] at h1
      have h2 : t * t ∈ 𝔭 := by
        have := sub_mem hmem h1
        rwa [sub_sub_cancel] at this
      exact (hp.mem_or_mem h2).elim ht ht
    have hn0 : jK (ι n₀) ≠ 0 := jι_ne_zero (ne_zero_of_notMem hn)
    have e1 : jK (ι t) * (1 + jK (ι π₀) * s) = jK (ι t + ι π₀ * z) := by
      rw [map_add, map_mul, e]
      ring
    have e2 : jK (ι n₀) = jK (ι t + ι π₀ * z) * jK (conjO K (ι t + ι π₀ * z)) := by
      rw [hn₀, map_mul]
    have hne : 1 + jK (ι π₀) * s ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e1
      rw [← e1, zero_mul] at e2
      exact hn0 e2
    refine ⟨hne, mem_SP.2 ⟨n₀, hn, ι t * conjO K (ι t + ι π₀ * z), ?_⟩⟩
    rw [e2, ← e1, map_mul]
    field_simp
  arch := by
    intro a
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n₀, hn₀⟩ := exists_norm hF y
    have hcy : conjO K y ≠ 0 := by
      intro h
      apply hy0
      rw [← L3.conjO_conjO y, h, map_zero]
    have hn0 : n₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hn₀
      exact (mul_ne_zero hy0 hcy) hn₀.symm
    have hc' : Ideal.span {n₀} ≠ (0 : Ideal (𝓞 F)) := by simpa using hn0
    have hnu : ¬ IsUnit 𝔭 := by
      rw [Ideal.isUnit_iff]
      exact h𝔭.ne_top
    obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hnu hc').exists_eq_pow_mul_and_not_dvd
    rw [Ideal.dvd_iff_le] at hnd
    obtain ⟨t, ht, ht'⟩ := SetLike.not_le_iff_exists.1 hnd
    generalize multiplicity 𝔭 (Ideal.span {n₀}) = l at hb
    refine ⟨l, mem_SP.2 ⟨t, ht', ?_⟩⟩
    have h1 : π₀ ^ l * t ∈ Ideal.span {n₀} := by
      rw [hb]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hu.mem _) ht
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 h1
    refine ⟨ι w * conjO K y * x, ?_⟩
    have hyK : jK y ≠ 0 := fun h => hy0 (jK_inj (h.trans (map_zero _).symm))
    have h2 := congrArg (fun x => jK (ι x)) hw
    simp only [map_mul, map_pow, hn₀] at h2 ⊢
    field_simp
    linear_combination (jK x) * h2

end Formalism.HermitianLattices.Ext.L3.HU
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def gramK (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) : Matrix κ κ K := Matrix.of fun i j => h (b i) (b j)

theorem form_repr (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (x y : V) :
    h x y = star (b.equivFun x) ⬝ᵥ (gramK h b *ᵥ b.equivFun y) := by
  calc h x y = h (∑ i, b.equivFun x i • b i) (∑ j, b.equivFun y j • b j) := by
        rw [b.sum_equivFun x, b.sum_equivFun y]
    _ = ∑ i, ∑ j, star (b.equivFun x i) * (b.equivFun y j * h (b i) (b j)) := by
        simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
        simp only [dotProduct, mulVec, Pi.star_apply, gramK, Matrix.of_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramK_conjTranspose {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (b : Basis κ K V) :
    (gramK h b)ᴴ = gramK h b := by
  ext i j
  exact hs.eq (b j) (b i)

theorem smul_basis_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) {a : K} (ha : a ∈ SP K 𝔭)
    (i : κ) : a • b i ∈ locF 𝔭 (spanO b) := by
  obtain ⟨t, ht, z, e⟩ := mem_SP.1 ha
  refine (mem_locF 𝔭 _ _).2 ⟨t, ht, ?_⟩
  rw [← algebraMap_smul K (ι t), smul_smul, ← e, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_locF_iff_repr {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (x : V) :
    x ∈ locF 𝔭 (spanO b) ↔ ∀ i, b.equivFun x i ∈ SP K 𝔭 := by
  constructor
  · intro hx i
    obtain ⟨t, ht, h1⟩ := (mem_locF 𝔭 _ _).1 hx
    have h2 : ι t • x = _ := coe_eq_sum b ⟨_, h1⟩
    generalize crd b ⟨_, h1⟩ = c at h2
    refine mem_SP.2 ⟨t, ht, c i, ?_⟩
    have h3 := congrArg (fun v => b.equivFun v i) h2
    simp only [← algebraMap_smul K (ι t), map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
      Basis.equivFun_self, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h3
    exact h3.symm
  · intro hx
    rw [← b.sum_equivFun x]
    exact Submodule.sum_mem _ fun i _ => smul_basis_mem b (hx i) i

theorem mem_smul_locF_iff_repr {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ) (x : V) :
    x ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) ↔ ∀ i, InP 𝔭 k (b.equivFun x i) := by
  constructor
  · intro hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y hy =>
      intro i
      rw [← algebraMap_smul K r, map_smul, Pi.smul_apply, smul_eq_mul]
      exact (inP_jK hr).mul (l := 0) ((mem_locF_iff_repr b y).1 hy i)
    | add y _ z _ hy hz =>
      intro i
      rw [map_add]
      exact (hy i).add (hz i)
  · intro hx
    rw [← b.sum_equivFun x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨t, ht, z, hz, e⟩ := hx i
    have ht0 : jK (ι t) ≠ 0 := jι_ne_zero (ne_zero_of_notMem ht)
    have h1 : (jK (ι t))⁻¹ ∈ SP K 𝔭 := mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ ht0]⟩
    have h2 : b.equivFun x i • b i = z • ((jK (ι t))⁻¹ • b i) := by
      rw [← algebraMap_smul K z, smul_smul, e]
      congr 1
      field_simp
    rw [h2]
    exact Submodule.smul_mem_smul hz (smul_basis_mem b h1 i)

theorem equivFun_toLin (b : Basis κ K V) (G : Matrix κ κ K) (x : V) :
    b.equivFun (Matrix.toLin b b G x) = G *ᵥ b.equivFun x := by
  have := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b G) x
  rw [LinearMap.toMatrix_toLin] at this
  funext i
  exact (congrFun this i).symm

def equivOfMatrix (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (Matrix.toLin b b G) (Matrix.toLin b b G')
    (by rw [← Matrix.toLin_mul, hG, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, mul_eq_one_comm.1 hG, Matrix.toLin_one])

theorem equivFun_equivOfMatrix (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun (equivOfMatrix b G G' hG x) = G *ᵥ b.equivFun x := equivFun_toLin b G x

theorem equivFun_equivOfMatrix_symm (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun ((equivOfMatrix b G G' hG).symm x) = G' *ᵥ b.equivFun x := equivFun_toLin b G' x

theorem equivOfMatrix_mem_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (hU : Gᴴ * gramK h b * G = gramK h b) :
    equivOfMatrix b G G' hG ∈ Formalism.HermitianLatticesTheory.isom h := by
  intro x y
  rw [form_repr h b, form_repr h b x y, equivFun_equivOfMatrix, equivFun_equivOfMatrix, form_mulVec, hU]

theorem mulVec_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) {v : κ → K}
    (hv : ∀ i, v i ∈ SP K 𝔭) (i : κ) : (G *ᵥ v) i ∈ SP K 𝔭 :=
  (SP K 𝔭).sum_mem fun j _ => (SP K 𝔭).mul_mem (hG i j) (hv j)

theorem gmap_equivOfMatrix {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (h1 : Ent (SP K 𝔭) G) (h2 : Ent (SP K 𝔭) G') :
    Formalism.HermitianLatticesTheory.gmap (equivOfMatrix b G G' hG) (locF 𝔭 (spanO b)) = locF 𝔭 (spanO b) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_locF_iff_repr]
    intro i
    have : b.equivFun (equivOfMatrix b G G' hG x) = G *ᵥ b.equivFun x := equivFun_equivOfMatrix b G G' hG x
    show b.equivFun (equivOfMatrix b G G' hG x) i ∈ _
    rw [this]
    exact mulVec_mem h1 ((mem_locF_iff_repr b x).1 hx) i
  · intro x hx
    refine ⟨(equivOfMatrix b G G' hG).symm x, ?_, (equivOfMatrix b G G' hG).apply_symm_apply x⟩
    show _ ∈ locF 𝔭 (spanO b)
    rw [mem_locF_iff_repr]
    intro i
    rw [equivFun_equivOfMatrix_symm]
    exact mulVec_mem h2 ((mem_locF_iff_repr b x).1 hx) i

end Formalism.HermitianLattices.Ext.L3.HU
end
end

section
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Newton

theorem det_one_add (hϖ : ϖ ∈ S) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  set w : S := ⟨ϖ, hϖ⟩ with hw
  obtain ⟨c, h⟩ : ∃ c : S, (1 + w • M₀).det = 1 + M₀.trace * w + c * w ^ 2 :=
    ⟨_, Matrix.det_one_add_smul w M₀⟩
  refine ⟨((M₀.trace + c * w : S) : K), Subtype.prop _, ?_⟩
  have key : (1 + ϖ • M₀.map S.subtype) = S.subtype.mapMatrix (1 + w • M₀) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hw]
    · simp [Matrix.one_apply_ne hij, hw]
  have h2 : (1 + M₀.trace * w + c * w ^ 2 : S) = 1 + w * (M₀.trace + c * w) := by ring
  rw [key, ← RingHom.map_det, h, h2]
  simp [hw]

theorem step_identity (P H X Y Y' Z V V' : Matrix n n K) (a b : K)
    (hG : P * H * X = H + (a * b) • Z) (hHY : H * Y = b • V') (hYH : Y' * H = b • V)
    (hV : V + V' = Z) :
    (P - a • (Y' * P)) * H * (X - a • (X * Y)) =
      H + (a * a * b) • (-(Z * Y) - Y' * Z + Y' * V' + a • (Y' * Z * Y)) := by
  have e1 : P - a • (Y' * P) = (1 - a • Y') * P := by rw [sub_mul, one_mul, smul_mul_assoc]
  have e2 : X - a • (X * Y) = X * (1 - a • Y) := by rw [mul_sub, mul_one, mul_smul_comm]
  have e3 : (1 - a • Y') * P * H * (X * (1 - a • Y)) = (1 - a • Y') * (P * H * X) * (1 - a • Y) := by
    simp only [Matrix.mul_assoc]
  have hYHY : Y' * H * Y = b • (Y' * V') := by
    rw [Matrix.mul_assoc, hHY, mul_smul_comm]
  have hV2 : V = Z - V' := eq_sub_of_add_eq hV
  rw [e1, e2, e3, hG]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  simp only [← Matrix.mul_assoc, hYHY]
  simp only [← Matrix.mul_assoc, hHY, hYH, hV2]
  simp only [Matrix.mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

theorem step (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hES : Ent S E) {e k : ℕ}
    (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ (k + 1) • Z' := by
  obtain ⟨τ, hτ, hτ1⟩ := hS.tr
  have hstar : ∀ m : ℕ, star (ϖ ^ m) = ϖ ^ m := fun m => by rw [star_pow, hS.fix]
  have hZH : Zᴴ = Z := by
    have h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
    rw [hXZ, conjTranspose_add, hH, conjTranspose_smul, hstar] at h1
    have h2 : ϖ ^ k • Zᴴ = ϖ ^ k • Z := add_left_cancel h1
    exact smul_right_injective _ (pow_ne_zero k hS.ne) h2
  have hYent : Ent S (E * (τ • Z)) := hES.mul (Ent.smul hτ hZ)
  have hYc : Ent S (E * (τ • Z))ᴴ := Ent.conjTranspose hS.star_mem hYent
  have hab : ϖ ^ (k - e) * ϖ ^ e = ϖ ^ k := by rw [← pow_add, Nat.sub_add_cancel (by omega : e ≤ k)]
  have hG : Xᴴ * H * X = H + (ϖ ^ (k - e) * ϖ ^ e) • Z := by rw [hab]; exact hXZ
  have hHY : H * (E * (τ • Z)) = ϖ ^ e • (τ • Z) := by
    rw [← Matrix.mul_assoc, hHE, smul_mul_assoc, one_mul]
  have hEH : Eᴴ * H = ϖ ^ e • (1 : Matrix n n K) := by
    have h3 := congrArg conjTranspose hHE
    rw [conjTranspose_mul, hH, conjTranspose_smul, conjTranspose_one, hstar] at h3
    exact h3
  have hYH : (E * (τ • Z))ᴴ * H = ϖ ^ e • (star τ • Z) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, hEH, conjTranspose_smul, hZH, mul_smul_comm, mul_one]
  have hV : star τ • Z + τ • Z = Z := by rw [← add_smul, add_comm, hτ1, one_smul]
  have hid := Newton.step_identity Xᴴ H X (E * (τ • Z)) (E * (τ • Z))ᴴ Z (star τ • Z) (τ • Z)
    (ϖ ^ (k - e)) (ϖ ^ e) hG hHY hYH hV
  refine ⟨-(X * (E * (τ • Z))), ϖ ^ (k - e - 1) • (-(Z * (E * (τ • Z))) - (E * (τ • Z))ᴴ * Z +
    (E * (τ • Z))ᴴ * (τ • Z) + ϖ ^ (k - e) • ((E * (τ • Z))ᴴ * Z * (E * (τ • Z)))), (hX.mul hYent).neg,
    Ent.smul (S.pow_mem hS.mem _) ((((hZ.mul hYent).neg.sub (hYc.mul hZ)).add
      (hYc.mul (Ent.smul hτ hZ))).add (Ent.smul (S.pow_mem hS.mem _) ((hYc.mul hZ).mul hYent))), ?_⟩
  have e1 : X + ϖ ^ (k - e) • -(X * (E * (τ • Z))) = X - ϖ ^ (k - e) • (X * (E * (τ • Z))) := by
    rw [smul_neg, ← sub_eq_add_neg]
  have e2 : (X - ϖ ^ (k - e) • (X * (E * (τ • Z))))ᴴ =
      Xᴴ - ϖ ^ (k - e) • ((E * (τ • Z))ᴴ * Xᴴ) := by
    rw [conjTranspose_sub, conjTranspose_smul, hstar, conjTranspose_mul]
  have hp : ϖ ^ (k - e) * ϖ ^ (k - e) * ϖ ^ e = ϖ ^ (k + 1) * ϖ ^ (k - e - 1) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [e1, e2, hid, smul_smul, hp]

end Newton

theorem det_unit (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    X.det ≠ 0 ∧ X.det⁻¹ ∈ S := by
  have hW : Ent S (ϖ ^ (k - e - 1) • (Z * E)) := Ent.smul (S.pow_mem hS.mem _) (hZ.mul hES)
  obtain ⟨s, hs, hdet⟩ := Newton.det_one_add hS.mem hW
  have hmat : Xᴴ * H * X * E = ϖ ^ e • (1 + ϖ • (ϖ ^ (k - e - 1) • (Z * E))) := by
    rw [hXZ, add_mul, hHE, smul_mul_assoc, smul_add, smul_smul, smul_smul, ← pow_succ, ← pow_add,
      show e + 1 + (k - e - 1) = k by omega]
  have h1 := congrArg Matrix.det hmat
  rw [det_mul, det_mul, det_mul, det_smul, hdet, det_conjTranspose] at h1
  have h2 := congrArg Matrix.det hHE
  rw [det_mul, det_smul, det_one, mul_one] at h2
  have hc : (ϖ ^ e) ^ Fintype.card n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hS.ne)
  have h3 : star X.det * X.det = 1 + ϖ * s := by
    apply mul_right_cancel₀ hc
    linear_combination h1 - star X.det * X.det * h2
  obtain ⟨hne, hinv⟩ := hS.rad s hs
  have hX0 : X.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h3
    exact hne h3.symm
  have hsX : star X.det ≠ 0 := star_ne_zero.mpr hX0
  refine ⟨hX0, ?_⟩
  have e4 : X.det⁻¹ = star X.det * (1 + ϖ * s)⁻¹ := by
    rw [← h3, mul_inv, ← mul_assoc, mul_inv_cancel₀ hsX, one_mul]
  rw [e4]
  exact S.mul_mem (hS.star_mem _ hX.det) hinv

theorem exists_newton (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) (N : ℕ) :
    ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ N • Z' := by
  have key : ∀ j : ℕ, ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ (k + j) • Z' := by
    intro j
    induction j with
    | zero => exact ⟨0, Z, Ent.zero, hZ, by simpa using hXZ⟩
    | succ j ih =>
      obtain ⟨D, Z', hD, hZ', hEq⟩ := ih
      obtain ⟨D₁, Z'', hD₁, hZ'', hEq'⟩ := Newton.step hS hH hES hHE (by omega : e + 1 ≤ k + j)
        (hX.add (Ent.smul (S.pow_mem hS.mem _) hD)) hZ' hEq
      refine ⟨D + ϖ ^ j • D₁, Z'', hD.add (Ent.smul (S.pow_mem hS.mem _) hD₁), hZ'', ?_⟩
      have e1 : X + ϖ ^ (k - e) • (D + ϖ ^ j • D₁) =
          X + ϖ ^ (k - e) • D + ϖ ^ (k + j - e) • D₁ := by
        rw [smul_add, smul_smul, ← pow_add, add_assoc, show k - e + j = k + j - e by omega]
      rw [e1, hEq', show k + (j + 1) = k + j + 1 by omega]
  obtain ⟨D, Z', hD, hZ', hEq⟩ := key N
  refine ⟨D, ϖ ^ k • Z', hD, Ent.smul (S.pow_mem hS.mem _) hZ', ?_⟩
  rw [hEq, smul_smul, ← pow_add, add_comm k N]

end Formalism.HermitianLattices.Ext.L3.HU
end

section
open Matrix Polynomial

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Node

theorem div_mem (hS : IsLocUnif S ϖ) : ∀ (l : ℕ) (f : K), f ∈ S → star f = f →
    f * (ϖ⁻¹) ^ (l + 1) ∉ S → ϖ ^ l * f⁻¹ ∈ S := by
  intro l
  induction l with
  | zero =>
    intro f hf hs hn
    rcases hS.dv f hf hs with h | h
    · simpa using h
    · exact absurd (by simpa using h) hn
  | succ l ih =>
    intro f hf hs hn
    rcases hS.dv f hf hs with h | h
    · rw [pow_succ, mul_assoc]
      exact S.mul_mem (S.pow_mem hS.mem _) (S.mul_mem hS.mem h)
    · have hgs : star (f * ϖ⁻¹) = f * ϖ⁻¹ := by
        rw [star_mul', star_inv₀, hS.fix, hs]
      have hgn : f * ϖ⁻¹ * (ϖ⁻¹) ^ (l + 1) ∉ S := by
        rwa [mul_assoc, ← pow_succ']
      have := ih (f * ϖ⁻¹) h hgs hgn
      rw [mul_inv, inv_inv] at this
      have e : ϖ ^ (l + 1) * f⁻¹ = ϖ ^ l * (f⁻¹ * ϖ) := by ring
      rw [e]
      exact this

theorem exists_pow (hS : IsLocUnif S ϖ) {ι : Type*} (s : Finset ι) (a : ι → K) :
    ∃ l : ℕ, ∀ i ∈ s, ϖ ^ l * a i ∈ S := by
  choose L hL using hS.arch
  refine ⟨∑ i ∈ s, L (a i), fun i hi => ?_⟩
  have hle : L (a i) ≤ ∑ j ∈ s, L (a j) :=
    Finset.single_le_sum (f := fun j => L (a j)) (fun _ _ => Nat.zero_le _) hi
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact S.mul_mem (S.pow_mem hS.mem _) (hL _)

noncomputable def pol (A B : Matrix n n K) : K[X] := det ((X : K[X]) • A.map C + B.map C)

theorem pol_eval (A B : Matrix n n K) (c : K) : (pol A B).eval c = det (c • A + B) := by
  unfold pol
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.smul_apply]
  ring

theorem pol_natDegree_le (A B : Matrix n n K) : (pol A B).natDegree ≤ Fintype.card n :=
  Polynomial.natDegree_det_X_add_C_le A B

end Node

theorem exists_node [CharZero K] (hS : IsLocUnif S ϖ) (n : Type*) [Fintype n] [DecidableEq n] :
    ∃ l : ℕ, ∀ X : Matrix n n K, Ent S X → X.det ≠ 0 → X.det⁻¹ ∈ S →
      ∃ c ∈ S, c + star c = 1 ∧ ∃ W' : Matrix n n K, Ent S W' ∧
        (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K) := by
  obtain ⟨τ, hτS, hτ⟩ := hS.tr
  obtain ⟨θ, hθS, hθs, hθ0⟩ := hS.skew
  have hdetS : ∀ M : Matrix n n K, Ent S M → M.det ∈ S := by
    intro M hM
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_det]
    exact SetLike.coe_mem _
  have hadjS : ∀ M : Matrix n n K, Ent S M → Ent S M.adjugate := by
    intro M hM i j
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_adjugate]
    exact SetLike.coe_mem _
  have hnot : ϖ⁻¹ ∉ S := by
    intro h
    have := (hS.rad (-ϖ⁻¹) (S.neg_mem h)).1
    apply this
    rw [mul_neg, mul_inv_cancel₀ hS.ne]
    ring
  let N := Fintype.card n
  let s : Finset ℕ := Finset.range (2 * N + 1)
  let v : ℕ → K := fun k => τ + (k : K) * θ
  have hv : Set.InjOn v s := by
    intro a _ b _ hab
    have h1 : (a : K) * θ = (b : K) * θ := add_left_cancel hab
    exact_mod_cast mul_right_cancel₀ hθ0 h1
  have hvS : ∀ k, v k ∈ S := fun k => S.add_mem hτS (S.mul_mem (natCast_mem S k) hθS)
  have hvs : ∀ k, star (v k) = 1 - v k := by
    intro k
    simp only [v, star_add, star_mul', star_natCast, hθs]
    linear_combination hτ
  obtain ⟨l, hl⟩ := Node.exists_pow hS s (fun k => (Lagrange.basis s v k).eval 1)
  refine ⟨l, fun X hX hd hdi => ?_⟩
  let R : K[X] := Node.pol (1 - X) X * Node.pol (Xᴴ - 1) 1
  have hRdeg : R.degree < (s.card : WithBot ℕ) := by
    have h1 : R.natDegree ≤ 2 * N := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [two_mul]
      exact add_le_add (Node.pol_natDegree_le _ _) (Node.pol_natDegree_le _ _)
    refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le h1) ?_
    simp only [s, Finset.card_range]
    exact_mod_cast Nat.lt_succ_self _
  have hReval : ∀ c : K, star c = 1 - c →
      R.eval c = (c • (1 : Matrix n n K) + star c • X).det *
        star ((c • (1 : Matrix n n K) + star c • X).det) := by
    intro c hc
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval, ← Matrix.det_conjTranspose]
    congr 2
    · rw [hc, smul_sub, sub_smul, one_smul]; abel
    · simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_one, star_star]
      rw [hc, smul_sub, sub_smul, one_smul]; abel
  have hR1 : R.eval 1 = star X.det := by
    simp only [R]
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval]
    simp [Matrix.det_conjTranspose]
  have hsum : R.eval 1 = ∑ k ∈ s, R.eval (v k) * (Lagrange.basis s v k).eval 1 := by
    conv_lhs => rw [Lagrange.eq_interpolate hv hRdeg]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  have hX0 : X.det ≠ 0 := hd
  have hR1S : (R.eval 1)⁻¹ ∈ S := by
    rw [hR1, ← star_inv₀]
    exact hS.star_mem _ hdi
  have hR10 : R.eval 1 ≠ 0 := by
    rw [hR1]; exact star_ne_zero.mpr hX0
  have hMS : ∀ k, Ent S (v k • (1 : Matrix n n K) + star (v k) • X) := by
    intro k i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine S.add_mem (S.mul_mem (hvS k) ?_) (S.mul_mem (hS.star_mem _ (hvS k)) (hX i j))
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have hex : ∃ k ∈ s, R.eval (v k) * (ϖ⁻¹) ^ (l + 1) ∉ S := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    have h1 : R.eval 1 * ϖ⁻¹ ∈ S := by
      have e : R.eval 1 * ϖ⁻¹ =
          ∑ k ∈ s, (R.eval (v k) * (ϖ⁻¹) ^ (l + 1)) * (ϖ ^ l * (Lagrange.basis s v k).eval 1) := by
        rw [hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        have e1 : ϖ ^ l * (ϖ⁻¹) ^ (l + 1) = ϖ⁻¹ := by
          rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hS.ne, one_pow, one_mul]
        linear_combination (-(Polynomial.eval (v k) R * Polynomial.eval 1 (Lagrange.basis s v k))) * e1
      rw [e]
      exact S.sum_mem fun k hk => S.mul_mem (hcon k hk) (hl k hk)
    have e2 : ϖ⁻¹ = (R.eval 1)⁻¹ * (R.eval 1 * ϖ⁻¹) := by
      field_simp
    rw [e2]
    exact S.mul_mem hR1S h1
  obtain ⟨k, hk, hkn⟩ := hex
  set M := v k • (1 : Matrix n n K) + star (v k) • X with hMdef
  have hfk : R.eval (v k) = M.det * star M.det := hReval (v k) (hvs k)
  have hfS : R.eval (v k) ∈ S := by
    rw [hfk]; exact S.mul_mem (hdetS M (hMS k)) (hS.star_mem _ (hdetS M (hMS k)))
  have hfs : star (R.eval (v k)) = R.eval (v k) := by
    rw [hfk, star_mul', star_star, mul_comm]
  have hf0 : R.eval (v k) ≠ 0 := by
    intro h0; apply hkn; rw [h0, zero_mul]; exact S.zero_mem
  have hdiv := Node.div_mem hS l _ hfS hfs hkn
  have hM0 : M.det ≠ 0 := by
    intro h0; apply hf0; rw [hfk, h0, zero_mul]
  have hcS : ϖ ^ l * M.det⁻¹ ∈ S := by
    have e : ϖ ^ l * M.det⁻¹ = ϖ ^ l * (R.eval (v k))⁻¹ * star M.det := by
      rw [hfk]
      have : star M.det ≠ 0 := star_ne_zero.mpr hM0
      field_simp
    rw [e]
    exact S.mul_mem hdiv (hS.star_mem _ (hdetS M (hMS k)))
  refine ⟨v k, hvS k, by rw [hvs k]; ring, (ϖ ^ l * M.det⁻¹) • M.adjugate, ?_, ?_⟩
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hcS (hadjS M (hMS k) i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1
    rw [← hMdef]
    field_simp

end Formalism.HermitianLattices.Ext.L3.HU
end

section
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Cayley.exists_det_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  let ϖ₀ : S := ⟨ϖ, hS.mem⟩
  refine ⟨((Matrix.trace M₀ + (Matrix.det (1 + (Polynomial.X : Polynomial S) •
      M₀.map Polynomial.C)).divX.divX.eval ϖ₀ * ϖ₀ : S) : K), SetLike.coe_mem _, ?_⟩
  have hmap : (1 : Matrix n n K) + ϖ • M₀.map S.subtype = S.subtype.mapMatrix (1 + ϖ₀ • M₀) := by
    ext i j
    by_cases h : i = j <;> simp [h, ϖ₀]
  rw [hmap, ← RingHom.map_det, Matrix.det_one_add_smul ϖ₀ M₀]
  simp only [map_add, map_mul, map_one, map_pow, Subring.coe_subtype]
  simp only [Subring.coe_add, Subring.coe_mul, ϖ₀]
  ring

theorem Cayley.exists_inv_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ Q : Matrix n n K, Ent S Q ∧ (1 + ϖ • M) * Q = 1 := by
  obtain ⟨s, hs, hdet⟩ := Cayley.exists_det_one_add hS hM
  obtain ⟨hne, hinv⟩ := hS.rad s hs
  have hA : Ent S (1 + ϖ • M) := Ent.add Ent.one (Ent.smul hS.mem hM)
  refine ⟨(1 + ϖ * s)⁻¹ • (1 + ϖ • M).adjugate, Ent.smul hinv hA.adjugate, ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem exists_cayley (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e l N : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hN : 2 * l + e + 1 ≤ N)
    {X Z W' : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ N • Z)
    {c : K} (hc : c ∈ S) (hcc : c + star c = 1) (hW' : Ent S W')
    (hWW : (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K)) :
    ∃ G D : Matrix n n K, Ent S D ∧ Gᴴ * H * G = H ∧ G = X + ϖ ^ (N - 2 * l - e) • D := by
  classical
  set j := N - 2 * l - e with hj
  have hj1 : 1 ≤ j := by omega
  have hNj : N = j + e + 2 * l := by omega
  have hϖ0 : ϖ ≠ 0 := hS.ne
  have hstar : ∀ k : ℕ, star (ϖ ^ k) = ϖ ^ k := fun k => by rw [star_pow, hS.fix]
  have hcs : star c ∈ S := hS.star_mem c hc
  obtain ⟨A, hA⟩ : ∃ A : Matrix n n K, A = c • (1 : Matrix n n K) + star c • X := ⟨_, rfl⟩
  rw [← hA] at hWW
  have hAent : Ent S A := by
    rw [hA]
    exact Ent.add (Ent.smul hc Ent.one) (Ent.smul hcs hX)
  have hWA : W' * A = ϖ ^ l • (1 : Matrix n n K) := by
    have hne : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
    have h1 : A * ((ϖ ^ l)⁻¹ • W') = 1 := by
      rw [Matrix.mul_smul, hWW, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have h2 : ((ϖ ^ l)⁻¹ • W') * A = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    calc W' * A = ϖ ^ l • ((ϖ ^ l)⁻¹ • (W' * A)) := by
          rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
      _ = ϖ ^ l • (1 : Matrix n n K) := by rw [h2]
  have hAW : ∀ M : Matrix n n K, Aᴴ * (W'ᴴ * M) = ϖ ^ l • M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hWA, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hstar, Matrix.smul_mul, Matrix.one_mul]
  have hHE' : ∀ M : Matrix n n K, H * (E * M) = ϖ ^ e • M := by
    intro M
    rw [← Matrix.mul_assoc, hHE, Matrix.smul_mul, Matrix.one_mul]
  have hZh : Zᴴ = Z := by
    have h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [hXZ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH, hstar] at h1
    exact smul_right_injective _ (pow_ne_zero N hϖ0) (add_left_cancel h1)
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Matrix n n K, D₁ = E * (W'ᴴ * (Z * W')) := ⟨_, rfl⟩
  have hD₁ent : Ent S D₁ := by
    rw [hD₁]
    exact Ent.mul hES (Ent.mul (Ent.conjTranspose hS.star_mem hW') (Ent.mul hZ hW'))
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix n n K, Δ = (c * ϖ ^ j) • (D₁ * A) := ⟨_, rfl⟩
  have key1 : Aᴴ * (H * Δ) = (c * ϖ ^ N) • Z := by
    rw [hΔ, hD₁]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
    rw [hHE']
    simp only [Matrix.mul_smul]
    rw [hAW, hWA]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    rw [hNj]
    ring
  have key2 : Δᴴ * (H * A) = (star c * ϖ ^ N) • Z := by
    have h : Δᴴ * (H * A) = (Aᴴ * (H * Δ))ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [h, key1, Matrix.conjTranspose_smul, hZh, star_mul', hstar]
  have hAh : Aᴴ = star c • (1 : Matrix n n K) + c • Xᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star]
  have k1 : star c • (H * Δ) + c • (Xᴴ * (H * Δ)) = (c * ϖ ^ N) • Z := by
    rw [← key1, hAh, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  have k2 : c • (Δᴴ * H) + star c • (Δᴴ * (H * X)) = (star c * ϖ ^ N) • Z := by
    rw [← key2, hA, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one]
  have k0 : Xᴴ * (H * X) = H + ϖ ^ N • Z := by rw [← Matrix.mul_assoc, hXZ]
  have hTR : (X - c • Δ)ᴴ * H * (X - c • Δ) = (1 + star c • Δ)ᴴ * H * (1 + star c • Δ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    rw [k0]
    linear_combination (norm := module) -k1 - k2 - hcc • (ϖ ^ N • Z)
  have hMent : Ent S ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) :=
    Ent.smul (mul_mem (mul_mem hcs hc) (_root_.pow_mem hS.mem _)) (Ent.mul hD₁ent hAent)
  obtain ⟨Q, hQent, hRQ⟩ := Cayley.exists_inv_one_add hS hMent
  have hjj : ϖ * ϖ ^ (j - 1) = ϖ ^ j := by
    rw [← pow_succ']
    congr 1
    omega
  have hR : (1 : Matrix n n K) + ϖ • ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) =
      1 + star c • Δ := by
    rw [hΔ, smul_smul, smul_smul]
    congr 2
    rw [← hjj]
    ring
  rw [hR] at hRQ
  have hRQ' : Q + star c • (Δ * Q) = 1 := by
    have h := hRQ
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
    exact h
  refine ⟨(X - c • Δ) * Q, -(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q)), ?_, ?_, ?_⟩
  · exact Ent.sub (Ent.smul (neg_mem (mul_mem hcs hc)) (Ent.mul hX (Ent.mul hD₁ent (Ent.mul hAent hQent))))
      (Ent.smul (mul_mem hc hc) (Ent.mul hD₁ent (Ent.mul hAent hQent)))
  · rw [Matrix.conjTranspose_mul]
    calc Qᴴ * (X - c • Δ)ᴴ * H * ((X - c • Δ) * Q)
        = Qᴴ * ((X - c • Δ)ᴴ * H * (X - c • Δ)) * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * ((1 + star c • Δ)ᴴ * H * (1 + star c • Δ)) * Q := by rw [hTR]
      _ = ((1 + star c • Δ) * Q)ᴴ * H * ((1 + star c • Δ) * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hRQ]; simp
  · calc (X - c • Δ) * Q = X * (Q + star c • (Δ * Q)) - star c • (X * (Δ * Q)) - c • (Δ * Q) := by
          simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
          abel
      _ = X + ϖ ^ j • (-(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q))) := by
          rw [hRQ', Matrix.mul_one, hΔ]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
          module

end Formalism.HermitianLattices.Ext.L3.HU
end

section
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_unitary_near [CharZero K] (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H)
    (hHS : Ent S H) (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K))
    (hk : e + 1 ≤ k) {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z)
    (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    ∃ G G' D : Matrix n n K, Ent S G ∧ Ent S G' ∧ Ent S D ∧ G * G' = 1 ∧ Gᴴ * H * G = H ∧
      G = X + ϖ ^ (k - e) • D := by
  obtain ⟨l, hl⟩ := exists_node (K := K) hS n
  obtain ⟨D1, Z1, hD1, hZ1, hX1⟩ := exists_newton hS hH hHS hES hHE hk hX hZ hXZ (k + 2 * l)
  have hpk : ϖ ^ (k - e) ∈ S := pow_mem hS _
  have hX1S : Ent S (X + ϖ ^ (k - e) • D1) := hX.add (hD1.smul hpk)
  have hk1 : e + 1 ≤ k + 2 * l := by omega
  obtain ⟨hd1, hd1S⟩ := det_unit hS hH hHS hES hHE hk1 hX1S hZ1 hX1
  obtain ⟨c, hc, hcc, W', hW', hWW⟩ := hl _ hX1S hd1 hd1S
  have hN : 2 * l + e + 1 ≤ k + 2 * l := by omega
  obtain ⟨G, D2, hD2, hG, hGe⟩ :=
    exists_cayley hS hH hHS hES hHE hN hX1S hZ1 hX1 hc hcc hW' hWW
  have hexp : k + 2 * l - 2 * l - e = k - e := by omega
  rw [hexp] at hGe
  have hGS : Ent S G := by
    rw [hGe]
    exact hX1S.add (hD2.smul hpk)
  have hG0 : Gᴴ * H * G = H + ϖ ^ k • (0 : Matrix n n K) := by
    rw [smul_zero, add_zero]
    exact hG
  obtain ⟨hd, hdS⟩ := det_unit hS hH hHS hES hHE hk hGS Ent.zero hG0
  refine ⟨G, G.det⁻¹ • G.adjugate, D1 + D2, hGS, hGS.adjugate.smul hdS, hD1.add hD2, ?_, hG, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · rw [hGe, smul_add, add_assoc]

end Formalism.HermitianLattices.Ext.L3.HU
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def IsE (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : ℕ) : Prop :=
  ∀ x : V, (∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) →
    ∀ t ∈ 𝔭 ^ e, algebraMap (𝓞 F) (𝓞 K) t • x ∈ A

theorem gramK_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) :
    (gramK h b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  have h1 := form_repr h b (b.equivFun.symm v) (b.equivFun.symm v)
  rw [LinearEquiv.apply_symm_apply, hv0, dotProduct_zero] at h1
  have h2 := hd _ h1
  rw [← b.equivFun.apply_symm_apply v, h2, map_zero]

theorem exists_E (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) {π₀ : 𝓞 F} (hπ : π₀ ∈ 𝔭) :
    ∃ E : Matrix κ κ K, Ent (SP K 𝔭) E ∧ gramK h b * E = jK (ι π₀) ^ e • (1 : Matrix κ κ K) := by
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  refine ⟨jK (ι π₀) ^ e • (gramK h b)⁻¹, ?_, by rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet]⟩
  intro i j
  have h1 : ∀ y ∈ locF 𝔭 (spanO b), h y (b.equivFun.symm fun i => (gramK h b)⁻¹ i j) ∈
      locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [form_repr h b, LinearEquiv.apply_symm_apply]
    have h2 : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) = Pi.single j 1 := by
      funext l
      have : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) l = (gramK h b * (gramK h b)⁻¹) l j := rfl
      rw [this, Matrix.mul_nonsing_inv _ hdet, Matrix.one_apply, Pi.single_apply]
    rw [h2, dotProduct_single_one, ← mem_SP_iff_locF]
    exact InP.conj hF ((mem_locF_iff_repr b y).1 hy j)
  have h3 := (mem_locF_iff_repr b _).1 (he _ h1 (π₀ ^ e) (Ideal.pow_mem_pow hπ e)) i
  rw [← algebraMap_smul K, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, map_pow,
    map_pow] at h3
  exact h3

theorem gramK_eq_map {h : V →ₗ⋆[K] V →ₗ[K] K} {b : Basis κ K V} {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) : gramK h b = H.map jK := by
  ext i j
  exact (hH i j).symm

theorem map_form (H Y : Matrix κ κ (𝓞 K)) :
    (Y.map jK)ᴴ * H.map jK * Y.map jK = (Yᴴ * H * Y).map jK := by
  rw [Matrix.map_mul, Matrix.map_mul, conjTranspose_map jK (fun _ => rfl)]

theorem exists_Z {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀)
    {H Y : Matrix κ κ (𝓞 K)} {k : ℕ} (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ Z : Matrix κ κ K, Ent (SP K 𝔭) Z ∧
      (Y.map jK)ᴴ * H.map jK * Y.map jK = H.map jK + jK (ι π₀) ^ k • Z := by
  choose Z hZ hZ' using fun i j => (mem_noncompactPart_iff hu k _).1 (inP_jK (hY i j))
  refine ⟨Matrix.of Z, hZ, ?_⟩
  rw [map_form]
  ext i j
  have := hZ' i j
  rw [Matrix.sub_apply, map_sub] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul,
    ← this]
  ring

theorem ent_map {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (Y : Matrix κ κ (𝓞 K)) : Ent (SP K 𝔭) (Y.map jK) :=
  fun _ _ => jK_mem_SP _

theorem equivFun_sum_smul (b : Basis κ K V) (c : κ → 𝓞 K) :
    b.equivFun (∑ l, c l • b l) = fun l => jK (c l) := by
  have : ∑ l, c l • b l = ∑ l, jK (c l) • b l :=
    Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm
  rw [this, ← Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem exists_isom_matrix (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (Y : Matrix κ κ (𝓞 K))
    (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ i, g (b i) - ∑ l, Y l i • b l ∈
      (extP K 𝔭 ^ (k - e) • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨Z, hZ, hXZ⟩ := exists_Z hu hY
  have hg := gramK_eq_map hH
  rw [hg] at hHE
  have hHh : (H.map jK)ᴴ = H.map jK := by rw [← hg]; exact gramK_conjTranspose hs b
  obtain ⟨G, G', D, hG, hG', hD, hGG, hU, hGX⟩ := exists_unitary_near (isLocUnif hK hF h𝔭 hu) hHh
    (ent_map H) hE hHE hk (ent_map Y) hZ hXZ
  refine ⟨equivOfMatrix b G G' hGG, ⟨equivOfMatrix_mem_isom h b G G' hGG (by rw [hg]; exact hU),
    gmap_equivOfMatrix b G G' hGG hG hG'⟩, fun i => ?_⟩
  rw [mem_smul_locF_iff_repr]
  intro l
  have hb1 : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    rw [Basis.equivFun_self, Pi.single_apply]
    simp only [eq_comm]
  rw [map_sub, equivFun_equivOfMatrix, equivFun_sum_smul, hb1, mulVec_single_one, Pi.sub_apply]
  show InP 𝔭 (k - e) (G l i - jK (Y l i))
  rw [hGX, mem_noncompactPart_iff hu]
  refine ⟨D l i, hD l i, ?_⟩
  simp


theorem form_col (H Y : Matrix κ κ (𝓞 K)) (i j : κ) :
    (Yᴴ * H * Y) i j = star (fun l => Y l i) ⬝ᵥ (H *ᵥ fun l => Y l j) := by
  have := form_mulVec Y H (Pi.single i 1) (Pi.single j 1)
  rw [form_single, mulVec_single_one, mulVec_single_one] at this
  exact this.symm


end Formalism.HermitianLattices.Ext.L3.HU
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def cmb (b : Basis κ K V) (c : κ → 𝓞 K) : spanO b := (bO b).equivFun.symm c

theorem coe_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : (cmb b c : V) = ∑ l, c l • b l := by
  rw [cmb, Basis.equivFun_symm_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [Submodule.coe_smul, bO_apply]

theorem crd_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : crd b (cmb b c) = c :=
  (bO b).equivFun.apply_symm_apply c

theorem cmb_crd (b : Basis κ K V) (y : spanO b) : cmb b (crd b y) = y :=
  (bO b).equivFun.symm_apply_apply y

def inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) : spanO b →ₗ[𝓞 K] ↥(locF 𝔭 (spanO b)) :=
  Submodule.inclusion (le_locF 𝔭 (spanO b))

theorem coe_inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) (y : spanO b) : (inA 𝔭 b y : V) = y := rfl

abbrev QA (𝔭 : Ideal (𝓞 F)) (b : Basis κ K V) (k : ℕ) : Type :=
  ↥(locF 𝔭 (spanO b)) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))

theorem mk_eq_iff {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) (k : ℕ) (x y : ↥(locF 𝔭 (spanO b))) :
    (Submodule.Quotient.mk x : QA 𝔭 b k) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem quotLocF_mk' {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (y : spanO b) : quotLocF h𝔭 (spanO b) k (Submodule.Quotient.mk y) = Submodule.Quotient.mk (inA 𝔭 b y) :=
  rfl

theorem exists_cmb {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (q : QA 𝔭 b k) : ∃ c : κ → 𝓞 K, q = Submodule.Quotient.mk (inA 𝔭 b (cmb b c)) := by
  obtain ⟨q₀, rfl⟩ := (quotLocF h𝔭 (spanO b) k).surjective q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q₀
  exact ⟨crd b y, by rw [cmb_crd, quotLocF_mk']⟩

theorem cmb_eq_sum (b : Basis κ K V) (c : κ → 𝓞 K) : cmb b c = ∑ i, c i • cmb b (Pi.single i 1) := by
  apply (bO b).equivFun.injective
  show crd b _ = crd b _
  rw [crd_cmb]
  have : crd b (∑ i, c i • cmb b (Pi.single i 1)) = ∑ i, c i • crd b (cmb b (Pi.single i 1)) := by
    unfold crd
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [this]
  funext l
  simp [crd_cmb, Pi.single_apply]

theorem end_apply_cmb {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K))
    (hXY : ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
      Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i))) (c : κ → 𝓞 K) :
    X (Submodule.Quotient.mk (inA 𝔭 b (cmb b c))) = Submodule.Quotient.mk (inA 𝔭 b (cmb b (Y *ᵥ c))) := by
  have h1 : cmb b (Y *ᵥ c) = ∑ i, c i • cmb b fun l => Y l i := by
    apply (bO b).equivFun.injective
    show crd b _ = crd b _
    have : crd b (∑ i, c i • cmb b fun l => Y l i) = ∑ i, c i • crd b (cmb b fun l => Y l i) := by
      unfold crd
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    rw [this, crd_cmb]
    funext l
    simp [crd_cmb, mulVec, dotProduct, mul_comm]
  rw [h1, cmb_eq_sum b c]
  simp only [← Submodule.mkQ_apply] at hXY ⊢
  simp only [map_sum, map_smul, hXY]


def eL {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (b : Basis κ K V) (k : ℕ) :
    Module.End (𝓞 K) (QA 𝔭 b k) ≃ Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (quotLocF h𝔭 (spanO b) k).symm.conj.toEquiv.trans (eM b (extP K 𝔭 ^ k))




end Formalism.HermitianLattices.Ext.L3.HU
end
end
