import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup

section
open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem eulerEq_of (hF : StepFib) (hM : StepMult) (hL : StepLocal) (hR : StepRegroup) :
    EulerEq := by
  intro F E _ _ _ _ _ _ hFE M hM3
  exact hR F E M (hM E M hM3) fun v hv => hL F E M hM3 v hv (hF F E hFE v hv)

end CMEul
end
end

section
open NumberField

noncomputable section

namespace CMEul.Mult

open Formalism.HermitianLatticesTheory

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hP.ne_top
  omega

theorem card_le {K : Type} [Field K] [NumberField K] (n : ℕ) (hn : 2 ≤ n)
    (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (hs : ∀ P ∈ s, Ideal.absNorm P.1 = n) :
    s.card ≤ Module.finrank ℤ (𝓞 K) := by
  classical
  have hdvd : ∏ P ∈ s, P.1 ∣ Ideal.span {algebraMap ℤ (𝓞 K) (n : ℤ)} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro P _ Q _ hPQ
      exact Ideal.isCoprime_iff_sup_eq.mpr (P.2.coprime_of_ne Q.2 (fun h => hPQ (Subtype.ext h)))
    · intro P hP
      rw [Ideal.dvd_span_singleton]
      have hm := Ideal.absNorm_mem P.1
      rw [hs P hP] at hm
      simpa using hm
  have h2 := map_dvd Ideal.absNorm hdvd
  rw [map_prod, Ideal.absNorm_span_singleton, Algebra.norm_algebraMap] at h2
  have h3 : ∏ P ∈ s, Ideal.absNorm P.1 = n ^ s.card := by
    rw [Finset.prod_congr rfl hs, Finset.prod_const]
  rw [h3, Int.natAbs_pow, Int.natAbs_natCast] at h2
  exact (Nat.pow_dvd_pow_iff_le_right (by omega)).mp h2

theorem summable_norm_rpow {K : Type} [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s)) := by
  classical
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s))
    (fun P => by positivity) ?_
  intro u
  have hmap : ∀ P ∈ u, Ideal.absNorm P.1 ∈ u.image (fun P => Ideal.absNorm P.1) :=
    fun P hP => Finset.mem_image_of_mem _ hP
  calc ∑ P ∈ u, ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s)
      = ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
        ∑ P ∈ u with Ideal.absNorm P.1 = n, ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s) :=
        (Finset.sum_fiberwise_of_maps_to hmap (fun P => ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s))).symm
    _ = ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
          ((u.filter (fun P => Ideal.absNorm P.1 = n)).card : ℝ) * (n : ℝ) ^ (-s) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => Ideal.absNorm P.1),
          (Module.finrank ℤ (𝓞 K) : ℝ) * (n : ℝ) ^ (-s) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨P, hPu, rfl⟩ := Finset.mem_image.mp hn
        have hc := card_le (Ideal.absNorm P.1) (two_le_absNorm P.1 P.2)
          (u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1))
          (fun Q hQ => (Finset.mem_filter.mp hQ).2)
        have hc' : ((u.filter (fun Q => Ideal.absNorm Q.1 = Ideal.absNorm P.1)).card : ℝ) ≤ (Module.finrank ℤ (𝓞 K) : ℝ) := by
          exact_mod_cast hc
        exact mul_le_mul_of_nonneg_right hc' (by positivity)
    _ = (Module.finrank ℤ (𝓞 K) : ℝ) * ∑ n ∈ u.image (fun P => Ideal.absNorm P.1), (n : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℤ (𝓞 K) : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-s) := by
        gcongr
        exact hsum.sum_le_tsum _ (fun n _ => by positivity)

theorem rpow_le_half {x : ℝ} (hx : 2 ≤ x) : x ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 := by
  have h1 : x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have h2 : x⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hx
  linarith

theorem abs_eulerFac_sub_one_le {K : Type} [Field K] [NumberField K] [StarRing K] (M : ℕ)
    (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    |eulerFac K M P - 1| ≤ 2 * ((Ideal.absNorm P : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hN : (2 : ℝ) ≤ ((Ideal.absNorm P : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm P hP
  set x : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hx
  have hx0 : 0 < x := by linarith
  have hMz : -(M : ℤ) ≤ -3 := by omega
  have hhalf := rpow_le_half hN
  unfold eulerFac
  split_ifs with h
  ·
    set a : ℝ := (-1 : ℝ) ^ M * Real.sqrt x ^ (-(M : ℤ)) with ha
    have hsq1 : 1 ≤ Real.sqrt x := by
      rw [Real.one_le_sqrt]
      linarith
    have e : Real.sqrt x ^ (-3 : ℤ) = x ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hab : |a| ≤ x ^ (-(3 / 2 : ℝ)) := by
      rw [ha, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (zpow_pos (by linarith) _), ← e]
      exact zpow_le_zpow_right₀ hsq1 hMz
    have hale : a ≤ 1 / 2 := le_trans (le_abs_self a) (hab.trans hhalf)
    have hne : 1 - a ≠ 0 := by linarith
    have heq : (1 - a)⁻¹ - 1 = a / (1 - a) := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - a), div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ |a| := abs_nonneg a
    nlinarith [le_abs_self a, neg_abs_le a]
  ·
    set b : ℝ := x ^ (-(M : ℤ)) with hb
    have hb0 : 0 < b := zpow_pos hx0 _
    have hb3 : b ≤ x ^ (-(3 / 2 : ℝ)) := by
      have h1 : b ≤ x ^ (-3 : ℤ) := zpow_le_zpow_right₀ (by linarith) hMz
      have h2 : x ^ (-3 : ℤ) = x ^ (-3 : ℝ) := by
        rw [← Real.rpow_intCast]
        norm_num
      have h3 : x ^ (-3 : ℝ) ≤ x ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      linarith
    have hbh : b ≤ 1 / 2 := hb3.trans hhalf
    have hpos : 0 < 1 - b := by linarith
    have hle1 : 1 - b ≤ 1 := by linarith
    have hlo : 1 ≤ (1 - b) ^ (-(1 : ℝ) / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle1 (by norm_num)
    have hup1 : (1 - b) ^ (-(1 : ℝ) / 2) ≤ (1 - b) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by norm_num)
    rw [Real.rpow_neg_one] at hup1
    have hup2 : (1 - b)⁻¹ ≤ 1 + 2 * b := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith

end CMEul.Mult

theorem euler_factors_multipliable : CMEul.StepMult := by
  intro K _ _ _ M hM
  have hs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1 - 1) := by
    refine Summable.of_norm_bounded
      ((CMEul.Mult.summable_norm_rpow (K := K) (s := 3 / 2) (by norm_num)).mul_left 2) ?_
    intro P
    rw [Real.norm_eq_abs]
    exact CMEul.Mult.abs_eulerFac_sub_one_le M hM P.1 P.2
  simpa using Real.multipliable_one_add_of_summable hs
end
end

section
open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem two_le_absNorm {F : Type} [Field F] [NumberField F] (v : Ideal (𝓞 F)) (hv : v.IsMaximal) :
    2 ≤ Ideal.absNorm v := by
  have h1 : Ideal.absNorm v ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hv.ne_top
  have h0 : Ideal.absNorm v ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hv (RingOfIntegers.not_isField F)
  omega

theorem euler_factor_local : StepLocal := by
  intro F E _ _ _ _ _ _ M hM v hv hS
  classical
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm v : ℝ) := by exact_mod_cast two_le_absNorm v hv
  have hNpos : (0 : ℝ) < (Ideal.absNorm v : ℝ) := by linarith
  have hx1 : ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast]
    apply inv_lt_one_of_one_lt₀
    exact one_lt_pow₀ (by linarith) (by omega)
  rcases hS with ⟨P, hPm, hPv, hPc, hPN, hPu⟩ | ⟨P, Q, hPm, hQm, hPv, hQv, hPQ, hPc, hQc, hPN, hQN, hu⟩
  ·
    have heta : etaF F E v = -1 := by
      unfold etaF
      rw [if_pos ⟨P, ⟨hPm, hPv⟩, fun R hR => hPu R hR.1 hR.2⟩]
    let p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨P, hPm, hPv⟩
    have hval : eulerFac E M P = eulerF F E M v := by
      unfold eulerFac eulerF
      rw [if_pos hPc, heta, hPN]
      push_cast
      rw [Real.sqrt_sq hNpos.le]
    have := hasProd_single (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
        P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) p0 (fun b hb => by
      exfalso
      apply hb
      exact Subtype.ext (hPu b.1 b.2.1 b.2.2))
    simpa [p0, hval] using this
  ·
    have heta : etaF F E v = 1 := by
      unfold etaF
      rw [if_neg]
      rintro ⟨R, ⟨hRm, hRv⟩, hR⟩
      exact hPQ ((hR P ⟨hPm, hPv⟩).trans (hR Q ⟨hQm, hQv⟩).symm)
    let p0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨P, hPm, hPv⟩
    let q0 : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} :=
      ⟨Q, hQm, hQv⟩
    have hne : p0 ≠ q0 := fun h => hPQ (congrArg Subtype.val h)
    set y : ℝ := 1 - ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)) with hy
    have hypos : 0 < y := by rw [hy]; linarith
    have hP' : eulerFac E M P = y ^ (-(1 : ℝ) / 2) := by
      unfold eulerFac
      rw [if_neg (by rw [hPc]; exact fun h => hPQ h.symm), hPN]
    have hQ' : eulerFac E M Q = y ^ (-(1 : ℝ) / 2) := by
      unfold eulerFac
      rw [if_neg (by rw [hQc]; exact hPQ), hQN]
    have hval : eulerFac E M P * eulerFac E M Q = eulerF F E M v := by
      rw [hP', hQ', ← Real.rpow_add hypos]
      unfold eulerF
      rw [heta, one_pow, one_mul, ← hy]
      norm_num
      exact Real.rpow_neg_one y
    have := hasProd_prod_of_ne_finset_one (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
        P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} => eulerFac E M c.1) (s := {p0, q0})
      (L := SummationFilter.unconditional _) (fun b hb => by
      exfalso
      apply hb
      rcases hu b.1 b.2.1 b.2.2 with h | h
      · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
    rw [Finset.prod_pair hne] at this
    simpa [p0, q0, hval] using this

end CMEul
end
end

section
open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem euler_product_regroup : StepRegroup := by
  intro F E _ _ _ _ _ _ M hm hf
  classical
  let f : {P : Ideal (𝓞 E) // P.IsMaximal} → {v : Ideal (𝓞 F) // v.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 E)), by
      have := P.2
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.1⟩
  let e := Equiv.sigmaFiberEquiv f
  have h1 : HasProd (fun x => eulerFac E M (e x).1) (lValEta E M) :=
    (e.hasProd_iff (f := fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => eulerFac E M P.1)).mpr
      hm.hasProd
  have hfib : ∀ v : {v : Ideal (𝓞 F) // v.IsMaximal},
      HasProd (fun c : {x // f x = v} => eulerFac E M (e ⟨v, c⟩).1) (eulerF F E M v.1) := by
    intro v
    let ev : {x // f x = v} ≃
        {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.1} :=
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, Subtype.ext c.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (ev.hasProd_iff (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
      P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.1} => eulerFac E M c.1)).mpr (hf v.1 v.2)
  have h2 : HasProd (fun v : {v : Ideal (𝓞 F) // v.IsMaximal} => eulerF F E M v.1) (lValEta E M) :=
    h1.sigma hfib
  exact h2.tprod_eq

end CMEul
end
end

section
open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem euler_factor_conjugate : StepConj := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨hE, hR⟩ := hFE
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut (R := E))
  have hσ : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (σ x) = star (algebraMap (𝓞 E) E x) := fun x => rfl
  have hσσ : ∀ x : 𝓞 E, σ (σ x) = x := by
    intro x
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E (σ (σ x)) = algebraMap (𝓞 E) E x
    rw [hσ, hσ, star_star]
  refine ⟨σ, hσ, hσσ, ?_, ?_, ?_⟩
  · intro P
    unfold conjIdeal
    change _ = Ideal.span (σ '' P)
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hrs⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ s) = algebraMap (𝓞 E) E r
      rw [hσ, hrs]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, hσ s⟩
  · intro x
    constructor
    · intro hx
      have hfix : algebraMap (𝓞 E) E x ∈ {a : E | star a = a} := by
        change star (algebraMap (𝓞 E) E x) = algebraMap (𝓞 E) E x
        rw [← hσ, hx]
      rw [← hR] at hfix
      obtain ⟨y, hy⟩ := hfix
      have hyint : IsIntegral ℤ y := by
        have h1 : IsIntegral ℤ ((algebraMap F E).toIntAlgHom y) := by
          rw [RingHom.toIntAlgHom_coe, hy]
          exact RingOfIntegers.isIntegral_coe x
        exact (isIntegral_algHom_iff _ (algebraMap F E).injective).mp h1
      refine ⟨⟨y, hyint⟩, ?_⟩
      apply RingOfIntegers.ext
      exact hy
    · rintro ⟨z, rfl⟩
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ (algebraMap (𝓞 F) (𝓞 E) z)) =
        algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z)
      rw [hσ]
      have hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) ∈ Set.range (algebraMap F E) :=
        ⟨(z : F), rfl⟩
      rw [hR] at hmem
      exact hmem
  · intro P hP
    obtain ⟨θ, t, ht, hθt⟩ := hE.2.2 P hP
    refine ⟨θ, ?_⟩
    have : σ θ = t := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ θ) = algebraMap (𝓞 E) E t
      rw [hσ, ht]
    rw [this]
    exact hθt

end CMEul
end
end

section
namespace CMEul

theorem eulerEq_of_fib (hF : StepFib) : Formalism.L2.SG.MassRatio.EulerEq :=
  eulerEq_of hF _root_.euler_factors_multipliable euler_factor_local euler_product_regroup

end CMEul
end
