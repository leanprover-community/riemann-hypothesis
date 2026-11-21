import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLaws

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_supNorm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ), BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) → ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  first | exact @GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | exact GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | (intros; apply GlobalTheory.EvenTheta.sup_norm_mul_padicComplex <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicComplex_integral_bounded_series_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  first | exact @GlobalTheory.EvenTheta.SerRing.series_ring_laws | exact GlobalTheory.EvenTheta.SerRing.series_ring_laws | (intros; apply GlobalTheory.EvenTheta.SerRing.series_ring_laws <;> assumption)
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem dvd_pow_prod_sub {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] (d : R) (a : ι → R)
    (b : κ → R) (ha : d ∣ (∏ i, a i) ^ 2) (hb : d ∣ ∏ j, b j) :
    ∃ N : ℕ, d ∣ (∏ i, ∏ j, (b j - a i)) ^ N := by
  have h : (∏ i, ∏ j, (b j - a i)) ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hP⟩
    have h1 : (∏ i, a i) ∈ P := hP.mem_of_pow_mem 2 (hle (Ideal.mem_span_singleton.2 ha))
    have h2 : (∏ j, b j) ∈ P := hle (Ideal.mem_span_singleton.2 hb)
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h1
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.1 h2
    exact Ideal.IsPrime.prod_mem_iff.2 ⟨i, Finset.mem_univ _,
      Ideal.IsPrime.prod_mem_iff.2 ⟨j, Finset.mem_univ _, P.sub_mem hj hi⟩⟩
  obtain ⟨N, hN⟩ := h
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

noncomputable def bddSubring (p : ℕ) [Fact p.Prime] : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | BddSer f}
  mul_mem' ha hb := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ha hb).2.2
  add_mem' ha hb := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ha hb).1
  one_mem' := by simpa using ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 1).1
  zero_mem' := by simpa using ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 0).1
  neg_mem' {x} hx := by
    obtain ⟨B, hB⟩ := hx
    exact ⟨B, fun n => by simpa using hB n⟩

theorem intSer_of_common_divisor (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p])
    (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]) (he : BddSer e) (hΨ : BddSer Ψ) (hA : BddSer A)
    (hB : BddSer B) (h1 : PowerSeries.constantCoeff Ψ = 1)
    (hΨA : Ψ * A = (∏ i, lineSer e (y i)) ^ 2) (hΨB : Ψ * B = ∏ j, lineSer e (y' j))
    (hy : ∀ i j, y i ≠ y' j) : IntSer Ψ := by
  have hl : ∀ x : ℂ_[p], lineSer e x ∈ bddSubring p := fun x =>
    (bddSubring p).sub_mem he ((bddSubring p).mul_mem ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 x).1
      ((bddSubring p).pow_mem (show BddSer _ from ⟨1, (GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.2.1⟩) 2))
  obtain ⟨N, H, hH⟩ := dvd_pow_prod_sub (R := bddSubring p) ⟨Ψ, hΨ⟩
    (fun i => ⟨lineSer e (y i), hl _⟩) (fun j => ⟨lineSer e (y' j), hl _⟩)
    ⟨⟨A, hA⟩, Subtype.ext (by simpa using hΨA.symm)⟩
    ⟨⟨B, hB⟩, Subtype.ext (by simpa using hΨB.symm)⟩
  set c : ℂ_[p] := (∏ i, ∏ j, (y i - y' j)) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ =>
    Finset.prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hy i j))
  have key : Ψ * (H : PowerSeries ℂ_[p]) = PowerSeries.monomial (2 * n * m * N) c := by
    have h := congrArg Subtype.val hH
    have e1 : ∀ i j, lineSer e (y' j) - lineSer e (y i) =
        PowerSeries.C (y i - y' j) * PowerSeries.X ^ 2 := fun i j => by
      simp only [lineSer, map_sub]; ring
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul, SubmonoidClass.coe_finsetProd,
      AddSubgroupClass.coe_sub, e1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_pow, ← pow_mul] at h
    rw [← h, PowerSeries.monomial_eq_C_mul_X_pow, hc]
    simp only [map_pow, map_prod, mul_assoc]
  have hHc : PowerSeries.coeff (2 * n * m * N) (H : PowerSeries ℂ_[p]) = c := by
    have hinv : Ψ⁻¹ * Ψ = 1 := PowerSeries.inv_mul_cancel _ (by simp [h1])
    have : (H : PowerSeries ℂ_[p]) = PowerSeries.X ^ (2 * n * m * N) * (PowerSeries.C c * Ψ⁻¹) := by
      have h2 := congrArg (Ψ⁻¹ * ·) key
      simp only [← mul_assoc, hinv, one_mul, PowerSeries.monomial_eq_C_mul_X_pow] at h2
      rw [h2]; ring
    rw [this, PowerSeries.coeff_X_pow_mul']
    simp [h1]
  intro i
  have := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p Ψ H ‖c‖ hΨ H.2 (fun k => by
    rw [key, PowerSeries.coeff_monomial]
    split_ifs <;> simp) i (2 * n * m * N)
  rw [hHc] at this
  exact le_of_mul_le_mul_right (by simpa using this) (norm_pos_iff.2 hc0)

end GlobalTheory.EvenTheta
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_series_of_common_divisor_line_products : ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p]) (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]), BddSer e → BddSer Ψ → BddSer A → BddSer B → PowerSeries.constantCoeff Ψ = 1 → Ψ * A = (∏ i, lineSer e (y i)) ^ 2 → Ψ * B = ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → IntSer Ψ := by
  atlas_forward_decl GlobalTheory.EvenTheta.intSer_of_common_divisor
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.FunEq

open PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : K⟦X⟧} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

omit [IsUltrametricDist K] in
theorem intSer_C {c : K} (hc : ‖c‖ ≤ 1) : IntSer (C c : K⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

theorem intSer_pow {f : K⟦X⟧} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_C (K := K) (c := 1) (by simp)
  | succ n ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_aeval {h : K⟦X⟧} (hh : IntSer h) (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    IntSer (Polynomial.aeval h P) := by
  intro n
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)

theorem intSer_of_funEq (f h A B : K⟦X⟧) (N : ℕ) (hf : constantCoeff f = 1) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : ‖coeff 1 h‖ = 1) (hN : ‖(N : K)‖ < 1) (hA : IntSer A)
    (hA0 : constantCoeff A = 1) (hB : IntSer B) (hB0 : constantCoeff B = 1)
    (e : (PowerSeries.subst h f : K⟦X⟧) * A = f ^ N * B) : IntSer f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set P : Polynomial K := trunc n f with hP
  have hPi : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    intro i
    rw [hP, coeff_trunc]
    split_ifs with hi
    · exact ih i hi
    · simp
  have hPs : IntSer (P : K⟦X⟧) := fun i => by rw [Polynomial.coeff_coe]; exact hPi i
  have hP0 : constantCoeff (P : K⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn,
      coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨Q, hQ⟩ : (X : K⟦X⟧) ^ n ∣ f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]
  have hX : ∀ g : K⟦X⟧, coeff n (X ^ n * g) = constantCoeff g := fun g => by
    simpa using coeff_X_pow_mul g n 0
  have hQ0 : constantCoeff Q = coeff n f := by
    rw [← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]
  obtain ⟨h', hh'⟩ : (X : K⟦X⟧) ∣ h := X_dvd_iff.2 hh0
  have h'0 : constantCoeff h' = coeff 1 h := by
    rw [hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hfe : f = (P : K⟦X⟧) + X ^ n * Q := by rw [← hQ]; ring
  have hsQ : constantCoeff (PowerSeries.subst h Q : K⟦X⟧) = constantCoeff Q := by
    obtain ⟨Q', hQ'⟩ : (X : K⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
    have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
    conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
    have hC : (PowerSeries.subst h (C (constantCoeff Q) : K⟦X⟧) : K⟦X⟧) = C (constantCoeff Q) := by
      rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp
    rw [hC]
    simp [hh0]
  have hL : (PowerSeries.subst h f : K⟦X⟧) * A =
      Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A) := by
    conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]
    have : h ^ n = X ^ n * h' ^ n := by rw [hh', mul_pow]
    rw [this]; ring
  have hR : f ^ N * B = (P : K⟦X⟧) ^ N * B +
      X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : K⟦X⟧) ^ (N - 1 - i)) * B) := by
    have := geom_sum₂_mul f (P : K⟦X⟧) N
    rw [hQ] at this
    linear_combination (-B) * this
  have key := congrArg (coeff n) e
  rw [hL, hR, map_add, map_add, hX, hX] at key
  simp only [map_mul, map_pow, map_sum, hA0, hB0, hf, hP0, hsQ, hQ0, h'0, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  have h1 := intSer_mul (intSer_aeval hh P hPi) hA n
  have h2 := intSer_mul (intSer_pow hPs N) hB n
  have k2 : (coeff 1 h ^ n - N) * coeff n f =
      coeff n ((P : K⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A) := by
    linear_combination key
  have hu : ‖coeff 1 h ^ n - (N : K)‖ = 1 := by
    have hp : ‖coeff 1 h ^ n‖ = 1 := by rw [norm_pow, hh1, one_pow]
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]
  have := congrArg norm k2
  rw [norm_mul, hu, one_mul] at this
  rw [this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))

theorem intSer_of_funEq_padic : ∀ (p : ℕ) [Fact p.Prime] (f h A B : PowerSeries ℂ_[p]) (N : ℕ), PowerSeries.constantCoeff f = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖(N : ℂ_[p])‖ < 1 → IntSer A → PowerSeries.constantCoeff A = 1 → IntSer B → PowerSeries.constantCoeff B = 1 → (PowerSeries.subst h f : PowerSeries ℂ_[p]) * A = f ^ N * B → IntSer f :=
  fun _ _ f h A B N => intSer_of_funEq f h A B N

end GlobalTheory.EvenTheta.FunEq
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesCoeffNormLeOne_functional_equation_padic : ∀ (p : ℕ) [Fact p.Prime] (f h A B : PowerSeries ℂ_[p]) (N : ℕ), PowerSeries.constantCoeff f = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖(N : ℂ_[p])‖ < 1 → IntSer A → PowerSeries.constantCoeff A = 1 → IntSer B → PowerSeries.constantCoeff B = 1 → (PowerSeries.subst h f : PowerSeries ℂ_[p]) * A = f ^ N * B → IntSer f := by
  atlas_forward_decl GlobalTheory.EvenTheta.FunEq.intSer_of_funEq_padic
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Isog

theorem coeff_lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) (n : ℕ) :
    PowerSeries.coeff n (lineSer e x) = PowerSeries.coeff n e - if n = 2 then x else 0 := by
  simp [lineSer, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

theorem constantCoeff_lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) :
    PowerSeries.constantCoeff (lineSer e x) = PowerSeries.constantCoeff e := by
  simp [lineSer]

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_le_max' (a b : ℂ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_coeff_lineSer_le {e : PowerSeries ℂ_[p]} (he : IntSer e) (x : ℂ_[p]) (n : ℕ) :
    ‖PowerSeries.coeff n (lineSer e x)‖ ≤ max 1 ‖x‖ := by
  rw [coeff_lineSer]
  refine (norm_sub_le_max' _ _).trans (max_le_max (he n) ?_)
  split_ifs <;> simp

theorem exists_norm_coeff_lineSer {e : PowerSeries ℂ_[p]} (he : IntSer e)
    (he0 : PowerSeries.constantCoeff e = 1) (x : ℂ_[p]) :
    ∃ n, max 1 ‖x‖ ≤ ‖PowerSeries.coeff n (lineSer e x)‖ := by
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · refine ⟨0, ?_⟩
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lineSer, he0, norm_one]
    exact max_le le_rfl hx
  · refine ⟨2, ?_⟩
    rw [max_eq_right hx.le]
    have h1 := norm_sub_le_max' (PowerSeries.coeff 2 e) (PowerSeries.coeff 2 (lineSer e x))
    have h2 : PowerSeries.coeff 2 e - PowerSeries.coeff 2 (lineSer e x) = x := by
      rw [coeff_lineSer]; simp
    rw [h2] at h1
    rcases le_max_iff.1 h1 with h | h
    · exact absurd (h.trans (he 2)) (not_le.2 hx)
    · exact h

theorem IntSer.bdd {f : PowerSeries ℂ_[p]} (hf : IntSer f) : BddSer f := ⟨1, hf⟩

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs <;> simp

theorem bdd_prod {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℂ_[p]) (hg : ∀ i, BddSer (g i)) :
    BddSer (∏ i ∈ s, g i) :=
  Finset.prod_induction g BddSer (fun a b ha hb => ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 a b ha hb).2.2)
    (IntSer.bdd intSer_one) (fun i _ => hg i)

theorem int_pow {g : PowerSeries ℂ_[p]} (hg : IntSer g) (k : ℕ) : IntSer (g ^ k) := by
  induction k with
  | zero => simpa using intSer_one
  | succ k ih => rw [pow_succ]; exact ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).1 _ _ ih hg).2.2

theorem subst_lineSer_sub {e h : PowerSeries ℂ_[p]} (h0 : PowerSeries.constantCoeff h = 0)
    (x₀ x₁ : ℂ_[p]) :
    (PowerSeries.subst h (lineSer e x₀) : PowerSeries ℂ_[p]) - PowerSeries.subst h (lineSer e x₁) =
      PowerSeries.C (x₁ - x₀) * h ^ 2 := by
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have e1 : lineSer e x₀ = lineSer e x₁ + (x₁ - x₀) • PowerSeries.X ^ 2 := by
    rw [PowerSeries.smul_eq_C_mul]
    simp only [lineSer, map_sub]; ring
  rw [e1, PowerSeries.subst_add hs, PowerSeries.subst_smul hs, PowerSeries.subst_pow hs,
    PowerSeries.subst_X hs, PowerSeries.smul_eq_C_mul]
  ring

theorem bdd_of_mul_sq {Ψ h : PowerSeries ℂ_[p]} {c : ℂ_[p]} (hc : c ≠ 0) (hh : IntSer h)
    (h0 : PowerSeries.constantCoeff h = 0) (h1 : ‖PowerSeries.coeff 1 h‖ = 1)
    (hb : BddSer (Ψ * (PowerSeries.C c * h ^ 2))) : BddSer Ψ := by
  obtain ⟨h', rfl⟩ := PowerSeries.X_dvd_iff.2 h0
  have hi : IntSer h' := fun n => by simpa using hh (n + 1)
  have hc0 : ‖PowerSeries.constantCoeff h'‖ = 1 := by
    have := PowerSeries.coeff_succ_X_mul 0 h'
    simp only [zero_add] at this
    rw [this] at h1
    simpa using h1
  have hne : PowerSeries.constantCoeff h' ≠ 0 := by
    intro h; rw [h] at hc0; simp at hc0
  have hinv := (GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.2.2.1 h' hi hc0
  have hb2 := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ hb (((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 c⁻¹).1
    (IntSer.bdd (int_pow hinv 2))).2.2)).2.2
  have hm := PowerSeries.mul_inv_cancel h' hne
  have hcc : (PowerSeries.C c : PowerSeries ℂ_[p]) * PowerSeries.C c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have e : Ψ * (PowerSeries.C c * (PowerSeries.X * h') ^ 2) * (PowerSeries.C c⁻¹ * h'⁻¹ ^ 2) =
      Ψ * PowerSeries.X ^ 2 := by
    calc _ = Ψ * PowerSeries.X ^ 2 * (PowerSeries.C c * PowerSeries.C c⁻¹) * (h' * h'⁻¹) ^ 2 := by ring
      _ = _ := by rw [hm, hcc]; ring
  rw [e] at hb2
  obtain ⟨B, hB⟩ := hb2
  exact ⟨B, fun n => by simpa [PowerSeries.coeff_mul_X_pow] using hB (n + 2)⟩

end GlobalTheory.EvenTheta.Isog

namespace GlobalTheory.EvenTheta
open Isog

theorem intSer_of_isogeny_identities : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (e h S f : PowerSeries ℂ_[p]) (x₀ x₁ : ℂ_[p]) (y : Fin k → ℂ_[p]) (y' : Fin (2 * k) → ℂ_[p]), IntSer e → PowerSeries.constantCoeff e = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖((2 * k : ℕ) : ℂ_[p])‖ < 1 → PowerSeries.constantCoeff S = 1 → PowerSeries.constantCoeff f = 1 → f ^ 2 = S * lineSer e x₀ → (PowerSeries.subst h f : PowerSeries ℂ_[p]) = S ^ k * ∏ i, lineSer e (y i) → (PowerSeries.subst h (S * lineSer e x₁) : PowerSeries ℂ_[p]) = S ^ (2 * k) * ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → (∃ j, y' j = x₀) → (∃ j, y' j = x₁) → x₀ ≠ x₁ → IntSer f ∧ ‖x₀‖ ≤ 1 := by
  intro p _ k e h S f x₀ x₁ y y' he he0 hh h0 h1 hk hS0 hf0 hf2 hf hS hy ⟨j₀, hj₀⟩ ⟨j₁, hj₁⟩ hx
  obtain ⟨rI, rB, rC, -, -, rS, rM⟩ := GlobalTheory.T.padicComplex_integral_bounded_series_laws p
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hG : ∀ x, BddSer (lineSer e x) := fun x => ⟨_, norm_coeff_lineSer_le he x⟩
  have hG0 : ∀ x, PowerSeries.constantCoeff (lineSer e x) = 1 := fun x => by
    rw [constantCoeff_lineSer, he0]
  have hGs : ∀ x n, ‖PowerSeries.coeff n (PowerSeries.subst h (lineSer e x) : PowerSeries ℂ_[p])‖ ≤
      max 1 ‖x‖ := fun x => rS _ h _ (norm_coeff_lineSer_le he x) hh h0
  set P := ∏ i, lineSer e (y i) with hP
  set P' := ∏ j, lineSer e (y' j) with hP'
  have hPb : BddSer P := bdd_prod _ _ fun i => hG _
  have hP'b : BddSer P' := bdd_prod _ _ fun i => hG _
  have hP0 : PowerSeries.constantCoeff P = 1 := by simp [hP, map_prod, hG0]
  have hP'0 : PowerSeries.constantCoeff P' = 1 := by simp [hP', map_prod, hG0]
  have hinv := PowerSeries.mul_inv_cancel (S ^ (2 * k)) (by simp [hS0])
  set Ψ : PowerSeries ℂ_[p] := PowerSeries.subst h S * (S ^ (2 * k))⁻¹ with hΨ
  set A : PowerSeries ℂ_[p] := PowerSeries.subst h (lineSer e x₀) with hA
  set B : PowerSeries ℂ_[p] := PowerSeries.subst h (lineSer e x₁) with hB
  have eA : Ψ * A = P ^ 2 := by
    have h2 : (PowerSeries.subst h S : PowerSeries ℂ_[p]) * A = S ^ (2 * k) * P ^ 2 := by
      rw [hA, ← PowerSeries.subst_mul hs, ← hf2, PowerSeries.subst_pow hs, hf]; ring
    rw [hΨ]
    linear_combination (S ^ (2 * k))⁻¹ * h2 + P ^ 2 * hinv
  have eB : Ψ * B = P' := by
    rw [PowerSeries.subst_mul hs] at hS
    rw [hΨ]
    linear_combination (S ^ (2 * k))⁻¹ * hS + P' * hinv
  have eAB : A - B = PowerSeries.C (x₁ - x₀) * h ^ 2 := subst_lineSer_sub h0 x₀ x₁
  have hB0 : PowerSeries.constantCoeff B = 1 := by
    have e1 : lineSer e x₁ = 1 + PowerSeries.X * PowerSeries.mk fun n =>
        PowerSeries.coeff (n + 1) (lineSer e x₁) := by
      conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (lineSer e x₁)]
      rw [hG0, map_one, add_comm]
    have e2 : (PowerSeries.subst h (1 : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p]) = 1 := by
      rw [← PowerSeries.coe_substAlgHom hs, map_one]
    rw [hB, e1, PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, e2]
    simp [h0]
  have hΨ0 : PowerSeries.constantCoeff Ψ = 1 := by
    have := congrArg PowerSeries.constantCoeff eB
    rwa [map_mul, hB0, hP'0, mul_one] at this
  have hΨb : BddSer Ψ := by
    refine bdd_of_mul_sq (sub_ne_zero.2 hx.symm) hh h0 h1 ?_
    rw [← eAB, mul_sub, eA, eB, sq]
    exact (rB _ _ (rB _ _ hPb hPb).2.2 hP'b).2.1
  have hΨi : IntSer Ψ :=
    GlobalTheory.T.integral_series_of_common_divisor_line_products p k (2 * k) e Ψ A B y y' (IntSer.bdd he) hΨb ⟨_, hGs x₀⟩ ⟨_, hGs x₁⟩ hΨ0 eA eB hy
  have hP'm : ∀ n, ‖PowerSeries.coeff n P'‖ ≤ max 1 ‖x₁‖ := fun n => by
    have := rM Ψ B _ _ hΨi (hGs x₁) n
    rwa [eB, one_mul] at this
  have hj : j₀ ≠ j₁ := by
    rintro rfl
    exact hx (hj₀.symm.trans hj₁)
  set R := ∏ j ∈ (Finset.univ.erase j₁).erase j₀, lineSer e (y' j) with hR
  have hRb : BddSer R := bdd_prod _ _ fun i => hG _
  have hR0 : PowerSeries.constantCoeff R = 1 := by simp [hR, map_prod, hG0]
  have eP' : P' = lineSer e x₁ * (lineSer e x₀ * R) := by
    rw [hP', hR, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₁),
      ← Finset.mul_prod_erase (Finset.univ.erase j₁) _ (a := j₀) (by simp [hj]), hj₀, hj₁]
  have hGR : IntSer (lineSer e x₀ * R) := fun n => by
    obtain ⟨i, hi⟩ := exists_norm_coeff_lineSer he he0 x₁
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ (hG x₁) (rB _ _ (hG x₀) hRb).2.2 (eP' ▸ hP'm) i n
    have hpos : (0 : ℝ) < max 1 ‖x₁‖ := lt_max_of_lt_left one_pos
    have h4 := mul_le_mul_of_nonneg_right hi
      (norm_nonneg (PowerSeries.coeff n (lineSer e x₀ * R)))
    exact le_of_mul_le_mul_left (by rw [mul_one]; exact h4.trans h3) hpos
  have hGi : IntSer (lineSer e x₀) := fun n => by
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ (hG x₀) hRb hGR n 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0, norm_one, mul_one] at h3
  have hx0 : ‖x₀‖ ≤ 1 := by
    obtain ⟨i, hi⟩ := exists_norm_coeff_lineSer he he0 x₀
    exact (le_max_right _ _).trans (hi.trans (hGi i))
  have hPi : IntSer P := fun n => by
    have hAi : IntSer A := rS _ h _ hGi hh h0
    have h2 : IntSer (P * P) := by
      rw [← sq, ← eA]; exact (rI _ _ hΨi hAi).2.2
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ hPb hPb h2 n 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hP0, norm_one, mul_one] at h3
  refine ⟨GlobalTheory.T.powerSeriesCoeffNormLeOne_functional_equation_padic p f h (lineSer e x₀ ^ k) P (2 * k) hf0 hh h0 h1 hk (int_pow hGi k)
    (by simp [hG0]) hPi hP0 ?_, hx0⟩
  rw [hf, pow_mul, hf2]; ring

end GlobalTheory.EvenTheta
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffNormLeOne_of_isogeny_series_identities : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (e h S f : PowerSeries ℂ_[p]) (x₀ x₁ : ℂ_[p]) (y : Fin k → ℂ_[p]) (y' : Fin (2 * k) → ℂ_[p]), IntSer e → PowerSeries.constantCoeff e = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖((2 * k : ℕ) : ℂ_[p])‖ < 1 → PowerSeries.constantCoeff S = 1 → PowerSeries.constantCoeff f = 1 → f ^ 2 = S * lineSer e x₀ → (PowerSeries.subst h f : PowerSeries ℂ_[p]) = S ^ k * ∏ i, lineSer e (y i) → (PowerSeries.subst h (S * lineSer e x₁) : PowerSeries ℂ_[p]) = S ^ (2 * k) * ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → (∃ j, y' j = x₀) → (∃ j, y' j = x₁) → x₀ ≠ x₁ → IntSer f ∧ ‖x₀‖ ≤ 1 := by
  atlas_forward_decl GlobalTheory.EvenTheta.intSer_of_isogeny_identities
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarSquareQuotient_in_model_parameter : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (sqTh g.abelian₂ v) ∧ g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) := by
  first | exact @GlobalTheory.EvenTheta.Param.sqTh_atU | exact GlobalTheory.EvenTheta.Param.sqTh_atU | (intros; apply GlobalTheory.EvenTheta.Param.sqTh_atU <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  first | exact @GlobalTheory.EvenTheta.Fibres.isogeny_fibres | exact GlobalTheory.EvenTheta.Fibres.isogeny_fibres | (intros; apply GlobalTheory.EvenTheta.Fibres.isogeny_fibres <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  first | exact @GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | exact GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | (intros; apply GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt <;> assumption)
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem IsLat.evenTheta_translate_sq_eq_sigmaStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  intro Λ h t₀ h0 h2 t ht z
  have hsq := (GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ h0 h2).2.2.2.1 (z + t)
  have hσ := (h.sg_eq_zero t).not.2 ht
  rw [h.sqTh_sub h0 ht] at hsq
  have hs : sqTh Λ t (z + t) * sgStar Λ t ^ 2 = -(sgStar Λ (z + 2 * t) * sgStar Λ z) := by
    rw [sqTh, div_mul_cancel₀ _ (pow_ne_zero 2 hσ), show t - (z + t) = -z by ring, h.sg_neg,
      show t + (z + t) = z + 2 * t by ring]
    ring
  simp only [U1, zero_add, mul_pow]
  rw [hsq]
  have he : Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) (2 * t) / ↑(area Λ) -
        ↑Real.pi * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * ↑(area Λ))) =
      Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 *
      Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 := by
    rw [← mul_pow, ← Complex.exp_add, sq, ← Complex.exp_add, map_mul, map_ofNat]
    congr 1
    ring
  rw [he]
  generalize Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = a
  generalize Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = b
  linear_combination a ^ 2 * b ^ 2 * hs

end GlobalTheory.EvenTheta
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.U1_sq_mul_U1_th0_sq_eq_sgStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  atlas_forward_decl GlobalTheory.EvenTheta.IsLat.evenTheta_translate_sq_eq_sigmaStar
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Double

variable {Λ : AddSubgroup ℂ}

theorem exists_evenTheta_translate_mul_sq_comb (h : IsLat Λ) {t s : ℂ} (ht : t ∉ Λ) (h2 : 2 * t ∈ Λ) (hs : s ∉ Λ) :
    ∃ α γ : ℂ, ∀ w, GL3Theta.th0 Λ t (w + s) * GL3Theta.th0 Λ t (w - s) =
      α * GL3Theta.th0 Λ t w ^ 2 + γ * sgStar Λ w ^ 2 := by
  have hs0 := (h.sg_eq_zero s).not.2 hs
  have ht0 := (h.sg_eq_zero t).not.2 ht
  set E : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) t / (area Λ : ℂ) -
    (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) with hE
  set K : ℂ := Complex.exp ((Real.pi : ℂ) * t * (starRingEnd ℂ) t / (area Λ : ℂ)) with hK
  set c : ℂ := U1 Λ t (sgStar Λ) 0 with hc
  have hθ : ∀ u, GL3Theta.th0 Λ t u = sgStar Λ (u + t) * E u * c⁻¹ := fun u => rfl
  refine ⟨-sgStar Λ s ^ 2 * (wpF Λ t - wpF Λ s),
    -sgStar Λ s ^ 2 * c⁻¹ ^ 2 * K / sgStar Λ t ^ 2, fun w => ?_⟩
  have e1 : E (w + s) * E (w - s) = E w ^ 2 := by
    simp only [hE]
    rw [sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : sgStar Λ (w + 2 * t) * E w ^ 2 = -K * sgStar Λ w := by
    have hl := h.sg_law h2 w
    rw [if_neg (by simpa using ht)] at hl
    rw [show -K * sgStar Λ w = (-1 * sgStar Λ w) * K by ring, ← hl]
    simp only [U1, hE, hK]
    rw [mul_assoc (sgStar Λ _), sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    simp only [map_mul, map_ofNat]
    ring
  have e3 := h.sqTh_sub hs ht (w + t)
  rw [sqTh, sqTh, show t + (w + t) = w + 2 * t by ring, show t - (w + t) = -w by ring,
    show s + (w + t) = w + s + t by ring, show s - (w + t) = -(w - s + t) by ring,
    h.sg_neg, h.sg_neg, div_eq_iff (pow_ne_zero 2 hs0)] at e3
  rw [hθ, hθ, hθ]
  linear_combination (sgStar Λ (w + s + t) * sgStar Λ (w - s + t) * c⁻¹ ^ 2) * e1 -
    (E w ^ 2 * c⁻¹ ^ 2) * e3 +
    (sgStar Λ s ^ 2 * c⁻¹ ^ 2 * sgStar Λ w / sgStar Λ t ^ 2) * e2

theorem evenTheta_double_translate_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ s, s ∉ Λ → ∀ z, U1 Λ s (sgStar Λ) 0 ^ 2 * (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) z * GL3Theta.th0 Λ t₀ z) = U1 Λ s (sgStar Λ) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) z ^ 2 + (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) 0 - U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 4) * U1 Λ s (sgStar Λ) z ^ 2 := by
  intro Λ h t ht h2 s hs z
  obtain ⟨α, γ, hp⟩ := exists_evenTheta_translate_mul_sq_comb h ht h2 hs
  obtain ⟨-, h1, hev, -⟩ := evenThetaTwoTorsion_basic_properties Λ h t ht h2
  have hα : α = GL3Theta.th0 Λ t s ^ 2 := by
    have := hp 0
    rw [zero_add, zero_sub, hev, h1, (h.sg_eq_zero 0).2 Λ.zero_mem] at this
    linear_combination -this
  set F : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) s / (area Λ : ℂ) -
    (Real.pi : ℂ) * s * (starRingEnd ℂ) s / (2 * (area Λ : ℂ))) with hF
  have hU : ∀ (G : ℂ → ℂ) u, U1 Λ s G u = G (u + s) * F u := fun _ _ => rfl
  have hU2 : ∀ (G : ℂ → ℂ) u, U1 Λ (2 * s) G u = G (u + s + s) * (F u ^ 2 * F 0 ^ 2) := by
    intro G u
    simp only [U1, hF]
    rw [sq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    · ring
    · simp only [map_mul, map_ofNat]
      ring
  have p1 := hp (z + s)
  have p0 := hp (0 + s)
  rw [add_sub_cancel_right, hα] at p1 p0
  rw [h1] at p0
  simp only [hU, hU2]
  simp only [zero_add] at p0 ⊢
  linear_combination (sgStar Λ s ^ 2 * F 0 ^ 4 * F z ^ 2) * p1 -
    (F 0 ^ 4 * F z ^ 2 * sgStar Λ (z + s) ^ 2) * p0

end GlobalTheory.EvenTheta.Double
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.U1_two_mul_th0_mul_th0_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ s, s ∉ Λ → ∀ z, U1 Λ s (sgStar Λ) 0 ^ 2 * (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) z * GL3Theta.th0 Λ t₀ z) = U1 Λ s (sgStar Λ) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) z ^ 2 + (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) 0 - U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 4) * U1 Λ s (sgStar Λ) z ^ 2 := by
  atlas_forward_decl GlobalTheory.EvenTheta.Double.evenTheta_double_translate_mul
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_eq_one_or_of_add_eq_one {L : Type*} [NormedField L] [IsUltrametricDist L] {b c : L}
    (h : b + c = 1) (hn : ‖b * c‖ < 1) : ‖b‖ = 1 ∨ ‖c‖ = 1 := by
  by_contra hne
  push_neg at hne
  obtain ⟨hb, hc⟩ := hne
  rw [norm_mul] at hn
  have h1 : ‖c‖ = max 1 ‖b‖ := by
    have : c = 1 + -b := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hb.symm)]
    simp
  have h2 : ‖b‖ = max 1 ‖c‖ := by
    have : b = 1 + -c := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hc.symm)]
    simp
  have h3 : 1 ≤ ‖c‖ := h1 ▸ le_max_left _ _
  have h4 : 1 ≤ ‖b‖ := h2 ▸ le_max_left _ _
  nlinarith

theorem norm_two_mul_natCast_lt_one (k : ℕ) : ‖((2 * k : ℕ) : ℂ_[2])‖ < 1 := by
  have h2 : ‖(2 : ℂ_[2])‖ < 1 := by
    have : (2 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] ((2 : ℕ) : ℚ_[2]) := by simp [map_ofNat]
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hk : ‖(k : ℂ_[2])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
  push_cast
  rw [norm_mul]
  nlinarith [norm_nonneg (k : ℂ_[2]), norm_nonneg (2 : ℂ_[2])]

theorem exists_int_trace_one_unit_at_two :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  intro D lam
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by omega⟩
  have hk' : (D.host.d : ℂ) + 1 = 8 * (k : ℂ) := by exact_mod_cast hk
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hw : StandardLatticesGL3.w0 D = (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := rfl
  have hw' : 1 - StandardLatticesGL3.w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by
    rw [hw]; ring
  have hc : starRingEnd ℂ (StandardLatticesGL3.w0 D) = 1 - StandardLatticesGL3.w0 D := by
    rw [hw', hw, map_div₀, map_add, map_mul, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hp : StandardLatticesGL3.w0 D * (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ) := by
    rw [hw', hw]
    push_cast
    linear_combination (1 / 4 : ℂ) * hk' + (1 / 4 : ℂ) * hs
      - (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hQ : StandardLatticesGL3.w0 D ∈ Qbar := ha ▸ hm _
  have hQ' : 1 - StandardLatticesGL3.w0 D ∈ Qbar := Qbar.sub_mem Qbar.one_mem hQ
  have hadd : lamC lam (StandardLatticesGL3.w0 D) + lamC lam (1 - StandardLatticesGL3.w0 D) = 1 := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_add, ← map_one lam]
    congr 1
    apply Subtype.ext
    simp
  have hmul : lamC lam (StandardLatticesGL3.w0 D) * lamC lam (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ_[2]) := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_mul, ← map_natCast lam]
    congr 1
    apply Subtype.ext
    exact hp.trans (by simp; exact Or.inl rfl)
  rcases norm_eq_one_or_of_add_eq_one hadd (hmul ▸ norm_two_mul_natCast_lt_one k) with h | h
  · refine ⟨a, StandardLatticesGL3.w0 D, k, ha, hQ, h, by rw [hc]; ring, by rw [hc, hp], ?_⟩
    intro Λ t ht
    exact ⟨ht.2.1, hw' ▸ ht.2.2⟩
  · refine ⟨1 - a, 1 - StandardLatticesGL3.w0 D, k, ?_, hQ', h, ?_, ?_, ?_⟩
    · rw [← ha]
      simp
    · rw [map_sub, map_one, hc]; ring
    · rw [map_sub, map_one, hc, ← hp]; ring
    · intro Λ t ht
      rw [sub_sub_cancel]
      exact ⟨hw' ▸ ht.2.2, ht.2.1⟩

end GlobalTheory.EvenTheta
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceOne_evenNorm_unit_at_two : ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  first | exact @GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | exact GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | (intros; apply GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.EvenTheta

section General
variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = lam ⟨x, hx⟩ := dif_pos hx

theorem lamC_mul (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [lamC_coe lam hx, lamC_coe lam hy, lamC_coe lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_sub (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x - y) = lamC lam x - lamC lam y := by
  rw [lamC_coe lam hx, lamC_coe lam hy, lamC_coe lam (sub_mem hx hy), ← map_sub]; rfl

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  rw [lamC_coe lam (one_mem _)]; exact map_one lam

theorem lamC_neg_one (lam : Qbar →+* ℂ_[p]) : lamC lam (-1) = -1 := by
  rw [lamC_coe lam (neg_mem (one_mem _)), ← map_one lam, ← map_neg]; rfl

theorem lamC_inj (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (h : lamC lam x = lamC lam y) : x = y := by
  rw [lamC_coe lam hx, lamC_coe lam hy] at h
  exact congrArg Subtype.val (lam.injective h)

theorem xAt_inj (g : GL3Theta.G1 p) {v w : ℂ} (hv : wpF g.abelian₂ v ∈ Qbar) (hw : wpF g.abelian₂ w ∈ Qbar)
    (h : xAt g v = xAt g w) : wpF g.abelian₂ v = wpF g.abelian₂ w := by
  refine lamC_inj g.lam hv hw ?_
  have := mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero _)) h
  linear_combination this

theorem IntSer.bdd {f : PowerSeries ℂ_[p]} (h : IntSer f) : BddSer f := ⟨1, h⟩

theorem IntSer.mul {f g : PowerSeries ℂ_[p]} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 f g hf hg).2.2
theorem IntSer.add {f g : PowerSeries ℂ_[p]} (hf : IntSer f) (hg : IntSer g) : IntSer (f + g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 f g hf hg).1
theorem IntSer.sub {f g : PowerSeries ℂ_[p]} (hf : IntSer f) (hg : IntSer g) : IntSer (f - g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 f g hf hg).2.1
theorem BddSer.mul {f g : PowerSeries ℂ_[p]} (hf : BddSer f) (hg : BddSer g) : BddSer (f * g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f g hf hg).2.2
theorem BddSer.add {f g : PowerSeries ℂ_[p]} (hf : BddSer f) (hg : BddSer g) : BddSer (f + g) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f g hf hg).1
theorem bdd_C (c : ℂ_[p]) : BddSer (PowerSeries.C c) := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1
theorem int_C {c : ℂ_[p]} (h : ‖c‖ ≤ 1) : IntSer (PowerSeries.C c) := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).2 h
theorem int_X : IntSer (PowerSeries.X : PowerSeries ℂ_[p]) := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1
theorem IntSer.inv {f : PowerSeries ℂ_[p]} (hf : IntSer f) (h : ‖PowerSeries.constantCoeff f‖ = 1) :
    IntSer f⁻¹ := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.2.1 f hf h
theorem IntSer.sq {f : PowerSeries ℂ_[p]} (hf : IntSer f) : IntSer (f ^ 2) := by
  rw [_root_.sq]; exact hf.mul hf
theorem intSer_iff {f : PowerSeries ℂ_[p]} : IntegralMv f ↔ IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem int_of_sq {f : PowerSeries ℂ_[p]} (hb : BddSer f) (h : IntSer (f ^ 2)) : IntSer f := by
  intro n
  have := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p f f 1 hb hb (by rw [← _root_.sq]; exact h) n n
  nlinarith [norm_nonneg (PowerSeries.coeff n f)]

theorem int_line {e : PowerSeries ℂ_[p]} {x : ℂ_[p]} (he : IntSer e) :
    IntSer (lineSer e x) ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    have := he.sub h 2
    simpa [lineSer, PowerSeries.coeff_X_pow] using this
  · intro h
    exact he.sub ((int_C h).mul int_X.sq)

variable (g : GL3Theta.G1 p)

theorem atU_mul {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z * G z) ∧ g.atU (fun z => F z * G z) = g.atU F * g.atU G :=
  ((GlobalTheory.SerTransport.transport p g).1 F G hF hG).1
theorem atU_add {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z + G z) ∧ g.atU (fun z => F z + G z) = g.atU F + g.atU G :=
  ((GlobalTheory.SerTransport.transport p g).1 F G hF hG).2
theorem atU_smul {c : ℂ} (hc : c ∈ Qbar) {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => c * F z) ∧ g.atU (fun z => c * F z) = PowerSeries.C (lamC g.lam c) * g.atU F := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 c hc
  rw [← h2]
  exact atU_mul g h1 hF
theorem atU_sq {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => F z ^ 2) ∧ g.atU (fun z => F z ^ 2) = g.atU F ^ 2 := by
  simp only [_root_.sq]
  exact atU_mul g hF hF
theorem atU_prod {ι : Type} (s : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i, AlgEnt (F i)) :
    AlgEnt (fun z => ∏ i ∈ s, F i z) ∧ g.atU (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, g.atU (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
    simp only [Finset.prod_empty]
    exact ⟨h1, by rw [h2, lamC_one, map_one]⟩
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [← ih.2]
    exact atU_mul g (hF a) ih.1

end General

theorem thetaTranslation_zero (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

section Two
variable {g : GL3Theta.G1 2} {t₀ : ℂ} (hok : g.Ok) (hlat : IsLat g.abelian₂) (hdisc : TaylorLogMetric.discr g.abelian₂ = 1)
  (h2 : g2 g.abelian₂ ∈ Qbar) (h3 : g3 g.abelian₂ ∈ Qbar)
  (hwp : ∀ t, InRationalLattice g.abelian₂ t → t ∉ g.abelian₂ → wpF g.abelian₂ t ∈ Qbar)
  (halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)))
  (hnm : t₀ ∉ g.abelian₂) (htwo : 2 * t₀ ∈ g.abelian₂)

theorem rational_lattice_point_zero (Λ : AddSubgroup ℂ) : InRationalLattice Λ 0 := ⟨1, one_pos, by simp⟩

include halg in
theorem alg_sg : AlgEnt (sgStar g.abelian₂) := by
  have := halg 0 (rational_lattice_point_zero _)
  rwa [thetaTranslation_zero] at this

include hlat halg hnm htwo in
theorem alg_th : AlgEnt (GL3Theta.th0 g.abelian₂ t₀) := by
  have := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo 0 (rational_lattice_point_zero _)).1
  rwa [thetaTranslation_zero] at this

include hok hlat h2 h3 hwp halg in
theorem atU_sqTh {v : ℂ} (hv : v ∉ g.abelian₂) (hq : InRationalLattice g.abelian₂ v) :
    AlgEnt (sqTh g.abelian₂ v) ∧
      g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) :=
  GlobalTheory.T.sigmaStarSquareQuotient_in_model_parameter 2 g hok.2.1 hlat h2 h3 (alg_sg halg) v hv (hwp v hq hv)

include hok hlat h2 h3 hwp halg hnm htwo in
theorem atU_th_sq : PowerSeries.constantCoeff (g.atU (GL3Theta.th0 g.abelian₂ t₀)) = 1 ∧
    g.atU (GL3Theta.th0 g.abelian₂ t₀) ^ 2 = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g t₀) := by
  obtain ⟨-, h0, -, hsq, -⟩ := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties g.abelian₂ hlat t₀ hnm htwo
  have ha := alg_th hlat halg hnm htwo
  refine ⟨by rw [((GlobalTheory.SerTransport.transport 2 g).2.2.1 _ ha).2, h0, lamC_one], ?_⟩
  rw [← (atU_sq g ha).2, ← (atU_sqTh hok hlat h2 h3 hwp halg hnm ⟨2, two_pos, by exact_mod_cast htwo⟩).2]
  exact congrArg _ (funext hsq)

include hok hlat hdisc h2 h3 hwp halg hnm htwo in

theorem int_th {β : ℂ} {k : ℕ} (hβ : β ∈ Qbar) (hn : ‖lamC g.lam β‖ = 1)
    (hst : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂) (htr : β + starRingEnd ℂ β = 1)
    (hN : β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ)) (hb1 : β * t₀ ∉ g.abelian₂) (hb2 : (1 - β) * t₀ ∉ g.abelian₂)
    (hint : IntegralMv (g.mulBy (lamC g.lam β) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[2])) :
    IntSer (g.atU (GL3Theta.th0 g.abelian₂ t₀)) ∧ ‖xAt g t₀‖ ≤ 1 := by
  obtain ⟨Q, Q', hQ, hQ', e1, e2, hne, ⟨j0, hj0⟩, ⟨j1, hj1⟩, h01⟩ :=
    GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient g.abelian₂ hlat β t₀ k hst htr hN htwo hb1 hb2
  obtain ⟨h, hh, hh0, hh1, hsub⟩ := (GlobalTheory.SerTransport.transport 2 g).2.2.2 hok β hβ
  obtain ⟨-, hw, hw0, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨hf0, hf2⟩ := atU_th_sq hok hlat h2 h3 hwp halg hnm htwo
  have hq0 : InRationalLattice g.abelian₂ t₀ := ⟨2, two_pos, by exact_mod_cast htwo⟩
  have hq1 : InRationalLattice g.abelian₂ (β * t₀) := ⟨2, two_pos, by
    have := hst _ htwo
    rwa [show β * (2 * t₀) = ((2 : ℕ) : ℂ) * (β * t₀) by push_cast; ring] at this⟩
  have hd := fun v hv hq => atU_sqTh (v := v) hok hlat h2 h3 hwp halg hv hq
  have hxe : ∀ v w, wpF g.abelian₂ v = wpF g.abelian₂ w → xAt g v = xAt g w := fun v w h => by
    simp only [xAt, h]
  refine GlobalTheory.T.coeffNormLeOne_of_isogeny_series_identities 2 k g.wq⁻¹ h (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2) _ (xAt g t₀) (xAt g (β * t₀))
    (fun i => xAt g (Q i)) (fun j => xAt g (Q' j)) hw hw0 (intSer_iff.1 (hh ▸ hint)) hh0 (hh1 ▸ hn) ?_
    (by rw [map_pow, hE, one_pow]) hf0 hf2 ?_ ?_ ?_ ⟨j0, hxe _ _ hj0⟩ ⟨j1, hxe _ _ hj1⟩ ?_
  · rw [Nat.cast_mul, norm_mul]
    have h1 : ‖((2 : ℕ) : ℂ_[2])‖ < 1 := by
      rw [← map_natCast (algebraMap ℚ_[2] ℂ_[2]), norm_algebraMap']
      exact Padic.norm_p_lt_one
    have h4 : ‖(k : ℂ_[2])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    nlinarith [norm_nonneg ((2 : ℕ) : ℂ_[2]), norm_nonneg (k : ℂ_[2])]
  · rw [← (hsub _ (alg_th hlat halg hnm htwo)).2, funext e1,
      (atU_prod g Finset.univ fun i => (hd _ (hQ i).1 (hQ i).2).1).2,
      Finset.prod_congr rfl fun i _ => (hd _ (hQ i).1 (hQ i).2).2, Finset.prod_mul_distrib]
    simp
  · rw [← (hd _ hb1 hq1).2, ← (hsub _ (hd _ hb1 hq1).1).2, funext e2,
      (atU_prod g Finset.univ fun i => (hd _ (hQ' i).1 (hQ' i).2).1).2,
      Finset.prod_congr rfl fun i _ => (hd _ (hQ' i).1 (hQ' i).2).2, Finset.prod_mul_distrib]
    simp
  · exact fun i j h => hne i j (xAt_inj g (hwp _ (hQ i).2 (hQ i).1) (hwp _ (hQ' j).2 (hQ' j).1) h)
  · exact fun h => h01 (xAt_inj g (hwp _ hq0 hnm) (hwp _ hq1 hb1) h)

theorem tors_laQ {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) : InRationalLattice Λ t :=
  let ⟨_, n, hn, _, h⟩ := h; ⟨n, hn, h⟩

theorem tors_neg {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) : GL3Theta.Tors1 2 Λ (-t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  exact ⟨by simpa using h0, n, hn, hc, by simpa using h⟩

theorem tors_two {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) : GL3Theta.Tors1 2 Λ (2 * t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  obtain ⟨m, rfl⟩ : Odd n := by simpa using hc
  refine ⟨fun h' => h0 ?_, _, hn, hc, ?_⟩
  · have := sub_mem h (nsmul_mem h' m)
    convert this using 1
    simp only [nsmul_eq_mul]; push_cast; ring
  · have := add_mem h h
    convert this using 1
    ring

theorem tors_half {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 2 Λ t) :
    ∃ s ω, GL3Theta.Tors1 2 Λ s ∧ ω ∈ Λ ∧ 2 * s = t + ω := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  obtain ⟨m, rfl⟩ : Odd n := by simpa using hc
  have e : 2 * (((m : ℂ) + 1) * t) = t + ((2 * m + 1 : ℕ) : ℂ) * t := by push_cast; ring
  refine ⟨(m + 1) * t, _, ⟨fun h' => h0 ?_, _, hn, hc, ?_⟩, h, e⟩
  · have := sub_mem (add_mem h' h') h
    convert this using 1
    push_cast; ring
  · have := nsmul_mem h (m + 1)
    convert this using 1
    simp only [nsmul_eq_mul]; push_cast; ring

variable (htr : ∀ t : ℂ, GL3Theta.Tors1 2 g.abelian₂ t →
      IntegralMv ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ t (sgStar g.abelian₂))) ∧
      ‖PowerSeries.constantCoeff (g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)))‖ = 1)

include hok hlat hdisc h2 h3 halg htr in
theorem exists_tau {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) : ∃ τ : PowerSeries ℂ_[2], IntSer τ ∧
    ‖PowerSeries.constantCoeff τ‖ = 1 ∧ U1 g.abelian₂ t (sgStar g.abelian₂) 0 ∈ Qbar ∧
    ‖lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0)‖ = 1 ∧
    g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = ePhi1 g.lam g.abelian₂ g.C g.wq * τ := by
  obtain ⟨-, -, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨a, b⟩ := htr t ht
  obtain ⟨c, d⟩ := (GlobalTheory.SerTransport.transport 2 g).2.2.1 _ (halg t (tors_laQ ht))
  refine ⟨_, intSer_iff.1 a, ?_, c, d ▸ b, ?_⟩
  · rw [map_mul, PowerSeries.constantCoeff_inv, hE, inv_one, one_mul, b]
  · rw [← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [hE]; exact one_ne_zero), one_mul]

include hok hlat hdisc h2 h3 hwp halg htr in

theorem norm_xAt_tors {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) : ‖xAt g t‖ ≤ 1 := by
  obtain ⟨-, hw, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨τ, a1, -, a3, a4, a5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr ht
  obtain ⟨τ', b1, -, b3, b4, b5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr (tors_neg ht)
  obtain ⟨c1, c2⟩ := atU_sqTh hok hlat h2 h3 hwp halg ht.1 (tors_laQ ht)
  have e := (atU_smul g (mul_mem a3 b3) c1).2
  rw [funext (hlat.sqTh_mul ht.1), (atU_mul g (halg _ (tors_laQ ht)) (halg _ (tors_laQ (tors_neg ht)))).2,
    a5, b5, c2, lamC_mul _ a3 b3] at e
  set c := lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) * lamC g.lam (U1 g.abelian₂ (-t) (sgStar g.abelian₂) 0) with hc
  have hc1 : ‖c‖ = 1 := by rw [hc, norm_mul, a4, b4, one_mul]
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc1; exact zero_ne_one hc1
  have hE0 : ePhi1 g.lam g.abelian₂ g.C g.wq ≠ 0 := by intro h; rw [h, map_zero] at hE; exact zero_ne_one hE
  have e2 : lineSer g.wq⁻¹ (xAt g t) = PowerSeries.C c⁻¹ * (τ * τ') := by
    have hcc : PowerSeries.C c⁻¹ * PowerSeries.C c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    refine mul_left_cancel₀ (pow_ne_zero 2 hE0) ?_
    linear_combination (-PowerSeries.C c⁻¹) * e -
      (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g t)) * hcc
  rw [← int_line hw, e2]
  exact (int_C (by rw [norm_inv, hc1, inv_one])).mul (a1.mul b1)

variable (hf : IntSer (g.atU (GL3Theta.th0 g.abelian₂ t₀))) (hx : ‖xAt g t₀‖ ≤ 1)

include hok hlat hdisc h2 h3 hwp halg hnm htwo hf hx in
theorem int_E_sq : IntSer (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2) := by
  obtain ⟨-, hw, hw0, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨hf0, hf2⟩ := atU_th_sq hok hlat h2 h3 hwp halg hnm htwo
  have h0 : PowerSeries.constantCoeff (lineSer g.wq⁻¹ (xAt g t₀)) = 1 := by
    simp only [lineSer, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, hw0]; simp
  have := hf.sq.mul (((int_line hw).2 hx).inv (by rw [h0, norm_one]))
  rwa [hf2, mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [h0]; exact one_ne_zero), mul_one] at this

include hok hlat hdisc h2 h3 hwp halg hnm htwo htr hx in

theorem transl_sq {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) : ∃ H : PowerSeries ℂ_[2], IntSer H ∧
    (‖PowerSeries.coeff 0 H‖ = 1 ∨ ‖PowerSeries.coeff 1 H‖ = 1) ∧
    g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀)) ^ 2 = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * H := by
  obtain ⟨hε, hw, -, hE, hσ⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨τ, a1, a2, a3, a4, a5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr ht
  obtain ⟨τ', b1, b2, -, -, b5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr (tors_two ht)
  have hq0 : InRationalLattice g.abelian₂ t₀ := ⟨2, two_pos, by exact_mod_cast htwo⟩
  have w1 := hwp _ (tors_laQ ht) ht.1
  have w0 := hwp _ hq0 hnm
  have hA := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo t (tors_laQ ht)).1
  have hs1 := halg _ (tors_laQ ht)
  have hs2 := halg _ (tors_laQ (tors_two ht))
  have hs0 := alg_sg halg
  have e := (atU_smul g (mul_mem a3 a3) (atU_sq g hA).1).2
  have id1 : (fun z => U1 g.abelian₂ t (sgStar g.abelian₂) 0 * U1 g.abelian₂ t (sgStar g.abelian₂) 0 *
      U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀) z ^ 2) = fun z =>
      (-1) * (U1 g.abelian₂ (2 * t) (sgStar g.abelian₂) z * sgStar g.abelian₂ z) +
      ((wpF g.abelian₂ t - wpF g.abelian₂ t₀) * (U1 g.abelian₂ t (sgStar g.abelian₂) 0 * U1 g.abelian₂ t (sgStar g.abelian₂) 0)) *
        U1 g.abelian₂ t (sgStar g.abelian₂) z ^ 2 := by
    funext z
    linear_combination GlobalTheory.T.U1_sq_mul_U1_th0_sq_eq_sgStar g.abelian₂ hlat t₀ hnm htwo t ht.1 z
  have m1 := atU_smul g (neg_mem (one_mem _)) (atU_mul g hs2 hs0).1
  have m2 := atU_smul g (mul_mem (sub_mem w1 w0) (mul_mem a3 a3)) (atU_sq g hs1).1
  rw [id1, (atU_add g m1.1 m2.1).2, m1.2, m2.2, (atU_mul g hs2 hs0).2, (atU_sq g hs1).2, (atU_sq g hA).2,
    a5, b5, hσ, lamC_neg_one, lamC_mul _ (sub_mem w1 w0) (mul_mem a3 a3), lamC_mul _ a3 a3] at e
  set c := lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) with hc
  set ε := ((g.C.u⁻¹ : ℂ_[2]ˣ) : ℂ_[2]) with hεd
  set κ := lamC g.lam (wpF g.abelian₂ t - wpF g.abelian₂ t₀) with hκ
  have hκ1 : ‖κ‖ ≤ 1 := by
    have e1 : ε ^ 2 * κ = xAt g t - xAt g t₀ := by
      rw [hκ, lamC_sub _ w1 w0, xAt, xAt]; ring
    have e2 : ‖xAt g t - xAt g t₀‖ ≤ 1 := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rwa [norm_neg]))
      exact norm_xAt_tors hok hlat hdisc h2 h3 hwp halg htr ht
    rwa [← e1, norm_mul, norm_pow, hε, one_pow, one_mul] at e2
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at a4; exact zero_ne_one a4
  set μ := -(c * c)⁻¹ * ε with hμ
  have hμ1 : ‖μ‖ = 1 := by simp [hμ, a4, hε]
  refine ⟨PowerSeries.C μ * (PowerSeries.X * τ') + PowerSeries.C κ * τ ^ 2,
    ((int_C hμ1.le).mul (int_X.mul b1)).add ((int_C hκ1).mul a1.sq), ?_, ?_⟩
  · rcases hκ1.eq_or_lt with h | h
    · left
      simp [h, a2]
    · right
      have n1 : ‖μ * PowerSeries.constantCoeff τ'‖ = 1 := by rw [norm_mul, hμ1, b2, one_mul]
      have n2 : ‖κ * PowerSeries.coeff 1 (τ ^ 2)‖ < 1 := by
        rw [norm_mul]
        nlinarith [a1.sq 1, norm_nonneg κ, norm_nonneg (PowerSeries.coeff 1 (τ ^ 2))]
      rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [n1]; exact n2.ne'), n1]
      exact max_eq_left n2.le
  · have hcc : PowerSeries.C (c * c)⁻¹ * PowerSeries.C (c * c) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (mul_ne_zero hc0 hc0), map_one]
    rw [hμ]
    simp only [map_mul, map_neg, map_one] at e hcc ⊢
    linear_combination (-PowerSeries.C (c * c)⁻¹) * e -
      (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀)) ^ 2 -
        PowerSeries.C κ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * τ ^ 2) * hcc

include hok hlat hdisc h2 h3 hwp halg hnm htwo htr hf hx in

theorem transl_bdd {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) :
    BddSer (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀))) := by
  obtain ⟨s, ω, hs, hω, e2⟩ := tors_half ht
  obtain ⟨hA, hsh⟩ := GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo t (tors_laQ ht)
  obtain ⟨κ, hκ, hκ0, hκe⟩ := hsh ω hω
  rw [← e2] at hκe
  have hAs := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo s (tors_laQ hs)).1
  have hA2 := (GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta g.abelian₂ hlat halg t₀ hnm htwo _ (tors_laQ (tors_two hs))).1
  have hA0 := alg_th hlat halg hnm htwo
  have hs1 := halg _ (tors_laQ hs)
  obtain ⟨τ, a1, -, a3, a4, a5⟩ := exists_tau hok hlat hdisc h2 h3 halg htr hs
  obtain ⟨H, b1, -, b2⟩ := transl_sq hok hlat hdisc h2 h3 hwp halg hnm htwo htr hx hs
  have hE2 := int_E_sq hok hlat hdisc h2 h3 hwp halg hnm htwo hf hx
  obtain ⟨hf0, -⟩ := atU_th_sq hok hlat h2 h3 hwp halg hnm htwo
  have q1 := ((GlobalTheory.SerTransport.transport 2 g).2.2.1 _ hAs).1
  have q2 := ((GlobalTheory.SerTransport.transport 2 g).2.2.1 _ hA2).1
  have hc0 : U1 g.abelian₂ s (sgStar g.abelian₂) 0 ≠ 0 := by
    intro h
    rw [h, lamC_coe _ (zero_mem _)] at a4
    exact zero_ne_one ((norm_zero.symm.trans (congrArg norm (map_zero g.lam).symm)).trans a4)
  obtain ⟨c₁, c₂, hc1, hc2, hid⟩ : ∃ c₁ c₂ : ℂ, c₁ ∈ Qbar ∧ c₂ ∈ Qbar ∧ (fun z =>
      U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀) z * GL3Theta.th0 g.abelian₂ t₀ z) = fun z =>
      c₁ * U1 g.abelian₂ s (GL3Theta.th0 g.abelian₂ t₀) z ^ 2 + c₂ * U1 g.abelian₂ s (sgStar g.abelian₂) z ^ 2 := by
    refine ⟨U1 g.abelian₂ s (GL3Theta.th0 g.abelian₂ t₀) 0 ^ 2 / κ, (U1 g.abelian₂ (2 * s) (GL3Theta.th0 g.abelian₂ t₀) 0 -
      U1 g.abelian₂ s (GL3Theta.th0 g.abelian₂ t₀) 0 ^ 4) / (U1 g.abelian₂ s (sgStar g.abelian₂) 0 ^ 2 * κ),
      div_mem (pow_mem q1 _) hκ, div_mem (sub_mem q2 (pow_mem q1 _)) (mul_mem (pow_mem a3 _) hκ),
      funext fun z => ?_⟩
    have := GlobalTheory.T.U1_two_mul_th0_mul_th0_eq g.abelian₂ hlat t₀ hnm htwo s hs.1 z
    rw [hκe z] at this
    field_simp
    linear_combination this
  have e := (atU_mul g hA hA0).2
  have m1 := atU_smul g hc1 (atU_sq g hAs).1
  have m2 := atU_smul g hc2 (atU_sq g hs1).1
  rw [hid, (atU_add g m1.1 m2.1).2, m1.2, m2.2, (atU_sq g hAs).2, (atU_sq g hs1).2, a5, b2, mul_pow] at e
  have hb := (((bdd_C (lamC g.lam c₁)).mul (hE2.mul b1).bdd).add
    ((bdd_C (lamC g.lam c₂)).mul (hE2.mul a1.sq).bdd)).mul (hf.inv (by rw [hf0, norm_one])).bdd
  rwa [e, mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [hf0]; exact one_ne_zero), mul_one] at hb

include hok hlat hdisc h2 h3 hwp halg hnm htwo htr hf hx in

theorem transl_int {t : ℂ} (ht : GL3Theta.Tors1 2 g.abelian₂ t) :
    IntSer (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀))) ∧
      ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ n, ‖PowerSeries.coeff n (g.atU (U1 g.abelian₂ t (GL3Theta.th0 g.abelian₂ t₀)))‖ ≤ ρ := by
  obtain ⟨-, -, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic 2 g hok hlat h2 h3 hdisc
  obtain ⟨H, b1, b3, b2⟩ := transl_sq hok hlat hdisc h2 h3 hwp halg hnm htwo htr hx ht
  have hE2 := int_E_sq hok hlat hdisc h2 h3 hwp halg hnm htwo hf hx
  have hi := int_of_sq (transl_bdd hok hlat hdisc h2 h3 hwp halg hnm htwo htr hf hx ht)
    (by rw [b2]; exact hE2.mul b1)
  refine ⟨hi, ?_⟩
  rintro ⟨ρ, hρ, h⟩
  have h0 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2) = 1 := by rw [map_pow, hE, one_pow]
  have k1 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws 2).2.2.2.2.2.2 _ _ _ _ hi h
  have k2 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws 2).2.2.2.2.2.2 _ _ _ _ (hE2.inv (by rw [h0, norm_one])) k1
  rw [← _root_.sq, b2, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [h0]; exact one_ne_zero),
    one_mul] at k2
  rcases b3 with b | b
  · linarith [k2 0]
  · linarith [k2 1]

end Two

theorem atTwo : ∀ D : D7, GL3Theta.atTwo D := by
  intro D cc δ g hg t₀ ht₀
  have htr := GlobalTheory.T.cm_theta_torsion_translate_integral_series D 2 cc δ g hg
  have hend := (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).1 2 cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  obtain ⟨a, β, k, ha, hβ, hn, htrc, hN, hb⟩ := GlobalTheory.T.exists_traceOne_evenNorm_unit_at_two D g.lam
  obtain ⟨hb1, hb2⟩ := hb _ _ ht₀
  have hst' : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := fun ω hω => ha ▸ hst a ω hω
  have hnm : t₀ ∉ g.abelian₂ := fun h => hb1 (hst' _ h)
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have hwp' : ∀ t, InRationalLattice g.abelian₂ t → t ∉ g.abelian₂ → wpF g.abelian₂ t ∈ Qbar := fun t h h' => (hwp t h h').1
  have hint := hend _ (subset_closure ⟨a, rfl⟩)
  simp only [GL3Theta.tauK, ha] at hint
  obtain ⟨hf, hx⟩ := int_th hok hlat' hdisc h2 h3 hwp' halg hnm ht₀.1 hβ hn hst' htrc hN hb1 hb2 hint
  obtain ⟨hf0, -⟩ := atU_th_sq hok hlat' h2 h3 hwp' halg hnm ht₀.1
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨e1, e2⟩ := GlobalTheory.ExpLogMv.expMv_neg_logMv_mul 2 Unit (g.atU (GL3Theta.th0 g.abelian₂ t₀)) hf0
    refine ⟨by rw [sub_zero, map_neg, e1, neg_zero], ?_⟩
    rw [sub_zero]
    have e3 : (expMv (-GL3Theta.logMv (g.atU (GL3Theta.th0 g.abelian₂ t₀))) : PowerSeries ℂ_[2]) =
        (g.atU (GL3Theta.th0 g.abelian₂ t₀))⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one (by rw [hf0]; exact one_ne_zero)).2 e2
    exact intSer_iff.2 (e3 ▸ hf.inv (by rw [hf0, norm_one]))
  · obtain ⟨k1, k2⟩ := transl_int hok hlat' hdisc h2 h3 hwp' halg hnm ht₀.1 htr hf hx ht
    exact ⟨intSer_iff.2 k1, k2⟩

end GlobalTheory.EvenTheta
end
end
