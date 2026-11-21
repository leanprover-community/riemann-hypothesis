import Formalism.LocalToGlobal.Columns.TiedGlSplit
import Formalism.LocalToGlobal.Columns.TwQDefs

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

theorem qsp_exists_pi (P : Pl E) (hP : conjPrime₂ P ≠ P) : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal := by
  obtain ⟨s, hs, hns⟩ := exists_mem_notMem (Ne.symm hP)
  exact ⟨s, hs, fun h => hns ((mem_conjP P s).2 h)⟩

include hc in

theorem qsp_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem qsp_isOver (P : Pl E) : IsOver (underPl F P) P := rfl

include hc in

theorem qsp_exists (P : Pl E) (hP : conjPrime₂ P ≠ P) :
    ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal ∧ Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E)) := by
  obtain ⟨ϖ, hϖ, hcϖ⟩ := qsp_exists_pi P hP
  obtain ⟨t, ht⟩ := gls_trace_mem hc ϖ
  obtain ⟨N, hN⟩ := qsp_norm_mem hc ϖ
  have hsig : ∀ x : E, hc.sig x = star x := fun _ => rfl
  have hsig0 : hc.sig (ϖ : E) = ((cO E ϖ : 𝓞 E) : E) := by rw [hsig]; exact (algebraMap_cO ϖ).symm
  have hN' : algebraMap F E (N : F) = (ϖ : E) * hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hN
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have ht' : algebraMap F E (t : F) = (ϖ : E) + hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_add, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have hNv : N ∈ (underPl F P).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    rw [hN]; exact Ideal.mul_mem_right _ _ hϖ
  have htv : t ∉ (underPl F P).asIdeal := by
    intro h
    have h1 : algebraMap (𝓞 F) (𝓞 E) t ∈ P.asIdeal := h
    rw [ht] at h1
    exact hcϖ (by simpa using P.asIdeal.sub_mem h1 hϖ)
  obtain ⟨s⟩ := Formalism.MainNotions.Gaps.LG.sc_core hc.sig (fun x => by rw [hsig, hsig, star_star])
    (fun x hx => (hc.fixed x).1 hx) hc.deg2 (underPl F P) ϖ t N ht' hN' hNv htv
  have hN2 : ((cO E ϖ : 𝓞 E) : E) * hc.sig ((cO E ϖ : 𝓞 E) : E) = algebraMap F E (N : F) := by
    rw [hN', ← hsig0, mul_comm, hsig, hsig, star_star]
  obtain ⟨sa⟩ := Formalism.MainNotions.Gaps.LG.sc_orient s (cO E ϖ) N hNv hN2
  have e : hc.sig ((cO E ϖ : 𝓞 E) : E) = (ϖ : E) := by rw [← hsig0, hsig, hsig, star_star]
  exact ⟨ϖ, hϖ, hcϖ, ⟨e ▸ sa⟩⟩

end Split

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section Cmp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* v.adicCompletion F)
  (hint : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) ≤ 1)
  (hPv : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal)

include hint hPv in
theorem qsp_val_one (t : 𝓞 E) (ht : t ∉ P.asIdeal) : Valued.v (φ (algebraMap (𝓞 E) E t)) = 1 :=
  le_antisymm (hint t) (not_lt.1 fun h => ht ((hPv t).1 h))

theorem qsp_frac (x : E) (hx : P.valuation E x ≤ 1) :
    ∃ (a : 𝓞 E) (t : 𝓞 E), t ∉ P.asIdeal ∧ x * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hnd
  have hd0 : (d : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hspan : Ideal.span {(d : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hd0
  have hPu : ¬ IsUnit P.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact P.isPrime.ne_top
  obtain ⟨e, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPu
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.1 hJP
  have hvd : P.intValuation (d : 𝓞 E) ≤ WithZero.exp (-(e : ℤ)) := by
    rw [P.intValuation_le_pow_iff_dvd, hJ]
    exact dvd_mul_right _ _
  have hvn : P.intValuation n ≤ WithZero.exp (-(e : ℤ)) := by
    refine le_trans ?_ hvd
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) ≤ P.valuation E (algebraMap (𝓞 E) E (d : 𝓞 E))
    rw [← hnd, map_mul]
    exact mul_le_of_le_one_left' hx
  have hnt : n * t ∈ Ideal.span {(d : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ((P.intValuation_le_pow_iff_mem n e).1 hvn) htJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hnt
  refine ⟨a, t, htP, ?_⟩
  have hD : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hd0
  have hat : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E d =
      algebraMap (𝓞 E) E n * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, ha]
  apply mul_right_cancel₀ hD
  linear_combination (algebraMap (𝓞 E) E t) * hnd - hat

include hint hPv in

theorem qsp_le_of_val (x : E) (hx : P.valuation E x ≤ 1) : Valued.v (φ x) ≤ 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx
  have h1 := qsp_val_one P φ hint hPv t ht
  have h2 := hint a
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2

include hint hPv in

theorem qsp_lt_of_val (x : E) (hx : P.valuation E x < 1) : Valued.v (φ x) < 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx.le
  have h1 := qsp_val_one P φ hint hPv t ht
  have ha : a ∈ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E a) < 1
    rw [← hxt, map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 ht, mul_one]
    exact hx
  have h2 := (hPv a).2 ha
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2

include hint hPv in

theorem qsp_val_iff (x : E) : Valued.v (φ x) ≤ 1 ↔ P.valuation E x ≤ 1 := by
  refine ⟨fun h => ?_, qsp_le_of_val P φ hint hPv x⟩
  by_contra hc
  rw [not_le] at hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hc
  have hinv : P.valuation E x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx0).1 hc
  have hlt := qsp_lt_of_val P φ hint hPv x⁻¹ hinv
  rw [map_inv₀] at hlt
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx0
  exact absurd h (not_le.2 ((Valuation.one_lt_val_iff _ hφ).2 hlt))

include hint hPv in

theorem qsp_mod (x d : E) (hd : d ≠ 0) (z : v.adicCompletion F) (hz : Valued.v z ≤ 1) (hxz : φ x = φ d * z) :
    P.valuation E x ≤ P.valuation E d := by
  have hφd : φ d ≠ 0 := (map_ne_zero φ).2 hd
  have h1 : φ (x / d) = z := by
    rw [map_div₀, hxz, mul_div_cancel_left₀ _ hφd]
  have h2 : P.valuation E (x / d) ≤ 1 := (qsp_val_iff P φ hint hPv _).1 (by rw [h1]; exact hz)
  have h3 : x = x / d * d := by rw [div_mul_cancel₀ _ hd]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' h2

end Cmp

end Formalism.L2.Col
end
end
