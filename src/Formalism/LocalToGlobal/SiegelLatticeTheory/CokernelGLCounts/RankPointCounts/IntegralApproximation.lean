module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.IntegralApproximation

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem exists_int_approx (x : F) (hx : p.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, p.valuation F (x - algebraMap (𝓞 F) F a) < 1 := by
  classical
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F)) x
  dsimp only at hx ⊢
  have hs0 : (s : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hvs : p.intValuation (s : 𝓞 F) ≠ 0 := p.intValuation_ne_zero _ hs0
  rw [HeightOneSpectrum.valuation_of_mk', div_le_one₀ (zero_lt_iff.mpr hvs)] at hx
  have hp0 : p.asIdeal ≠ ⊥ := p.ne_bot
  have htop : p.asIdeal ≠ ⊤ := p.isPrime.ne_top
  have hex : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hs0
    have hmem : (s : 𝓞 F) ∈ ⨅ i, p.asIdeal ^ i := by
      rw [Ideal.mem_iInf]
      intro i
      cases i with
      | zero => simp
      | succ n => exact h n
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ htop] at hmem
    exact (Ideal.mem_bot).1 hmem
  obtain ⟨n, hn1, hn⟩ : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1) ∧ (s : 𝓞 F) ∈ p.asIdeal ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · simp [h0]
    · have hm := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      rw [not_not, Nat.sub_add_cancel hpos] at hm
      exact hm
  have hb : b ∈ p.asIdeal ^ n := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at hn ⊢
    exact hx.trans hn
  have hI : Ideal.span {(s : 𝓞 F)} ⊔ p.asIdeal ^ (n + 1) = p.asIdeal ^ n := by
    apply Ideal.eq_prime_pow_of_succ_lt_of_le hp0
    · refine lt_of_le_of_ne le_sup_right fun h => hn1 ?_
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hn) (Ideal.pow_le_pow_right (Nat.le_succ n))
  rw [← hI] at hb
  obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.1 hb
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨c, ?_⟩
  have hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hs0
  have key : IsLocalization.mk' F b s - algebraMap (𝓞 F) F c = IsLocalization.mk' F r s := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← hyr, map_add (f := _), map_mul]
    field_simp
    ring
  rw [key, HeightOneSpectrum.valuation_of_mk', div_lt_one₀ (zero_lt_iff.mpr hvs)]
  have hr' := (HeightOneSpectrum.intValuation_le_pow_iff_mem p r (n + 1)).2 hr
  have hs' : ¬ p.intValuation (s : 𝓞 F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun h =>
    hn1 ((HeightOneSpectrum.intValuation_le_pow_iff_mem p _ _).1 h)
  exact lt_of_le_of_lt hr' (not_le.1 hs')

end Res

open Formalism.L2.SG.DataInst Formalism.MainNotions.S.LocalSplitGroups

theorem absNorm_two_le {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm p.asIdeal := by
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact p.ne_bot
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact p.isPrime.ne_top
  omega

end Formalism.L2.SG.IntegralApproximation
