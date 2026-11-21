import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.RelDiffTop

section
open NumberField Polynomial

namespace PIW.CMDiscSq

theorem exists_of_star_eq {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {y : E} (hy : star y = y) :
    ∃ a : F, algebraMap F E a = y := by
  have : y ∈ Set.range (algebraMap F E) := by rw [hR]; exact hy
  exact this

theorem adjoin_eq_top_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    Algebra.adjoin F {x} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hd : x - star x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hbd : (y - star y) / (x - star x) * (x - star x) = y - star y := div_mul_cancel₀ _ hd
  have hb : star ((y - star y) / (x - star x)) = (y - star y) / (x - star x) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star, ← neg_sub y, ← neg_sub x,
      neg_div_neg_eq]
  have ha : star (y - (y - star y) / (x - star x) * x) = y - (y - star y) / (x - star x) * x := by
    rw [star_sub, star_mul', hb]
    linear_combination hbd
  obtain ⟨b, hb'⟩ := exists_of_star_eq hR hb
  obtain ⟨a, ha'⟩ := exists_of_star_eq hR ha
  have hy : y = algebraMap F E a + algebraMap F E b * x := by rw [ha', hb']; ring
  rw [hy]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ a)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b) (Algebra.subset_adjoin rfl))

theorem minpoly_eq_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    [FiniteDimensional F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    ∃ s n : F, algebraMap F E s = x + star x ∧ algebraMap F E n = x * star x ∧
      minpoly F x = X ^ 2 - C s * X + C n := by
  obtain ⟨s, hs⟩ := exists_of_star_eq hR (y := x + star x) (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := exists_of_star_eq hR (y := x * star x) (by rw [star_mul', star_star, mul_comm])
  refine ⟨s, n, hs, hn, ?_⟩
  have hmon : (X ^ 2 - C s * X + C n : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 - C s * X + C n : F[X]).natDegree = 2 := by compute_degree!
  have hroot : aeval x (X ^ 2 - C s * X + C n : F[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h2 : 2 ≤ (minpoly F x).natDegree := by
    rw [minpoly.two_le_natDegree_iff hint]
    rintro ⟨a, rfl⟩
    apply hx
    have : algebraMap F E a ∈ Set.range (algebraMap F E) := ⟨a, rfl⟩
    rw [hR] at this
    exact this
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon
    (minpoly.dvd F x hroot) (by rw [hdeg]; exact h2)).symm

end PIW.CMDiscSq
end

section
open NumberField Polynomial

namespace PIW.CMDiscSq

theorem sub_mem_differentIdeal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) (hne : θ - t ≠ 0) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 E) E
  have hx : star (algebraMap (𝓞 E) E θ) ≠ algebraMap (𝓞 E) E θ := by
    intro h
    apply hne
    rw [sub_eq_zero]
    apply hinj
    rw [ht, h]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ (adjoin_eq_top_of_star_ne hR hx)
  obtain ⟨s, n, hs, hn, hmin⟩ := minpoly_eq_of_star_ne hR hx
  have hAx : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral θ
  have hval : algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) =
      algebraMap (𝓞 E) E (θ - t) := by
    have h1 : aeval (algebraMap (𝓞 E) E θ) (derivative (minpoly F (algebraMap (𝓞 E) E θ))) =
        algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F E hAx, derivative_map,
        aeval_map_algebraMap, aeval_algebraMap_apply]
    rw [← h1, hmin, map_sub, ht]
    simp only [derivative_X_pow, derivative_mul, derivative_C, derivative_X, map_add, map_sub,
      map_mul, map_pow, aeval_X, aeval_C, hs, zero_mul, zero_add, mul_one, add_zero,
      Nat.cast_ofNat, map_ofNat]
    ring
  rw [hinj hval] at hmem
  exact hmem

theorem relDiffTop : RelDiffTop := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨⟨_, _, hP⟩, hR⟩ := hFE
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hP P hPmax
  apply hθt
  apply hle
  apply sub_mem_differentIdeal hR θ t ht
  intro h0
  apply hθt
  rw [h0]
  exact P.zero_mem

end PIW.CMDiscSq
end
