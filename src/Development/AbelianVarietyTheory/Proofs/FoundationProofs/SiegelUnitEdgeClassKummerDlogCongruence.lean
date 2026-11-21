import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeCupProps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicElementApproximation
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismOnExtensionPointwise
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismExtensionUniform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerBasisIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesAlgebraicConstant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueAlgebraicPolynomialDivisible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Geofix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalValueOfQuotientAddOfCommonDenominator
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GnFixZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelLogCoordsStatement

section
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5

theorem exists_valuationSubring_isInt_comap :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type)
      [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
      ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧ ∀ x, x ∈ B ↔ IsInt p (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ hC j
  obtain ⟨v, hv, -, -, hp1⟩ := exists_valuation_isInt p Ωl hC
  let w : Valuation Ω NNReal := v.comap j
  refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
      ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
    show v (j ((p : ℕ) : Ω)) < 1
    rw [map_natCast]
    exact hp1
  · rw [Valuation.mem_valuationSubring_iff]
    exact hv (j x)

end GlobalTheory.K5
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_pullback_integral_elements : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧ ∀ x, x ∈ B ↔ IsInt p (j x) := by
  atlas_forward_decl GlobalTheory.K5.exists_valuationSubring_isInt_comap
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  first | exact @GlobalTheory.ValConjClosure.exists_conj_over_prime | exact GlobalTheory.ValConjClosure.exists_conj_over_prime | (intros; apply GlobalTheory.ValConjClosure.exists_conj_over_prime <;> assumption)
end

section
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.DenseAlg

theorem exists_mem_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
    (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a) := by
  intro Ω _ _ _ p _ A Ωl _ _ hclo j hA k e he halg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨a, ha, hc⟩ := GlobalTheory.K5.Dense.exists_cong p Ωl hclo Ω j k e he halg
  exact ⟨a, (hA a).2 ha, hc⟩

end GlobalTheory.K5.DenseAlg
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a) := by
  atlas_forward_decl GlobalTheory.K5.DenseAlg.exists_mem_cong
end

section
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.CuspDown

theorem exists_restrict : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  intro Ω _ _ _ p _ A Ωl _ _ hC j hA g
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
  letI : Algebra Ω Ωl := j.toAlgebra
  haveI : IsScalarTower ℚ Ω Ωl := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ωl), eq_ratCast (algebraMap ℚ Ω), map_ratCast]
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let gq : Ωl ≃ₐ[ℚ] Ωl := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
    simp only [eq_ratCast, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv]
    exact map_ratCast g x)
  have hc : ∀ x, g (j x) = j (gq.restrictNormal Ω x) := fun x => by
    have := AlgEquiv.restrictNormal_commutes gq Ω x
    rw [RingHom.algebraMap_toAlgebra] at this
    rw [this]; rfl
  refine ⟨gq.restrictNormal Ω, fun x => ?_, hc⟩
  rw [hA, hA, ← hc]
  constructor
  · intro h
    have := GlobalTheory.K5.Basic.isInt_gal g.symm h
    rwa [AlgEquiv.symm_apply_apply] at this
  · exact GlobalTheory.K5.Basic.isInt_gal g

end GlobalTheory.CuspDown
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosure_automorphism_restricting_local : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  atlas_forward_decl GlobalTheory.CuspDown.exists_restrict
end

section
section
noncomputable section

namespace GlobalTheory.Glue.CuspUp

open GlobalTheory.K5 GlobalTheory.KZ Polynomial
open scoped NNReal

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
  {v : Valuation Ωl ℝ≥0}

theorem v_alg_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (b : O0 p) : v (algebraMap (O0 p) Ωl b) ≤ 1 :=
  (hv _).2 isIntegral_algebraMap

theorem v_alg_lt_iff (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1) (b : O0 p) :
    v (algebraMap (O0 p) Ωl b) < 1 ↔ (p : O0 p) ∣ b := by
  obtain ⟨_, hd, hirr⟩ := completed_laurent_isDVR p
  constructor
  · intro hb
    rw [← Ideal.mem_span_singleton, ← hirr.maximalIdeal_eq]
    intro hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have h2 : v (algebraMap (O0 p) Ωl b) * v (algebraMap (O0 p) Ωl c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_nonneg_of_lt_one_left zero_le hb (v_alg_le hv c)).ne
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_mul, map_natCast]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (v_alg_le hv c)

theorem exists_red : ∃ φ : O0 p →+* LaurentSeries (ZMod p),
    φ (qO p) = HahnSeries.single (1 : ℤ) (1 : ZMod p) ∧ ∀ b, φ b = 0 ↔ (p : O0 p) ∣ b := by
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk _), he, fun b => ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  exact e.map_eq_zero_iff

theorem isInt_qq (T : K5.Tower p Ωl) (n : ℕ) : IsIntegral (O0 p) (T.qq n) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos n) ?_
  rw [Basic.qq_pow]
  exact isIntegral_algebraMap

theorem v_aeval_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) :
    v (aeval (T.qq n) f) ≤ 1 :=
  (hv _).2 (IsIntegral.of_mem_of_fg _ (isInt_qq T n).fg_adjoin_singleton _
    (aeval_mem_adjoin_singleton _ _))

theorem orth (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (hlt : v (aeval (T.qq n) f) < 1) : C (p : O0 p) ∣ f := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.aeval_qq_pow_sub_lt_one p Ωl h v hv h1 T n f hf
  have h3 : v (aeval (T.qq n) f ^ (p ^ n)) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le hlt (pow_pos hp.out.pos n).ne'
  have h4 := v.map_sub_lt h3 h2
  rw [sub_sub_cancel, v_alg_lt_iff hv h1, ← hφ] at h4
  simp only [map_sum, map_mul, map_pow, hq] at h4
  have h5 := GlobalTheory.laurent_pow_indep_over_prime_pow_powers p n (fun i => φ (f.coeff i)) h4
  rw [C_dvd_iff_dvd_coeff]
  intro i
  by_cases hi : i < p ^ n
  · exact (hφ _).1 (h5 i hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _

theorem res (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (halg : IsAlgebraic ℤ (aeval (T.qq n) f)) : ∃ m : ℤ, v (aeval (T.qq n) f - m) < 1 := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.aeval_qq_pow_sub_lt_one p Ωl h v hv h1 T n f hf
  have hy := v_aeval_le hv T n f
  set y := aeval (T.qq n) f
  set b := ∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.K5.exists_int_poly_root_mod_p p Ωl h v hv h1 (y ^ p ^ n) b (halg.pow _)
    (by rw [map_pow]; exact pow_le_one₀ zero_le hy) h2
  obtain ⟨c, hc⟩ := GlobalTheory.laurentSeries_eq_C_of_root (ZMod p) (φ b) ⟨_, hP0, by
    rw [← (hφ _).2 hP, eval₂_map, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨m, ?_⟩
  have h3 : v (algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n)) < 1 := by
    rw [v_alg_lt_iff hv h1, ← hφ, map_sub, hc, map_pow φ, map_intCast φ,
      ← map_intCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p)), ← map_pow, ZMod.pow_card_pow, sub_self]
  have hm : v (m : Ωl) ≤ 1 := (hv _).2 (Basic.isInt_intCast m)
  let y' : v.integer := ⟨y - m, v.map_sub_le hy hm⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out y' (m : v.integer) n
  have hr' := congrArg (Subtype.val) hr
  simp only [y'] at hr'
  push_cast at hr'
  have h4 : v ((p : Ωl) * (y - m) * m * r) < 1 := by
    rw [mul_assoc, mul_assoc, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (y' * ((m : v.integer) * r)).2
  have h5 := v.map_sub_lt (v.map_add_lt h2 h3) h4
  have h6 : y ^ p ^ n - algebraMap (O0 p) Ωl b + algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n) -
      (p : Ωl) * (y - m) * m * r = (y - m) ^ p ^ n := by
    rw [map_sub, map_pow, map_intCast]
    rw [sub_add_cancel] at hr'
    linear_combination hr'
  rw [h6, map_pow] at h5
  exact lt_of_pow_lt_pow_left₀ (p ^ n) zero_le_one (by rwa [one_pow])

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem approx (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (N : ℕ) : ∀ (f : (O0 p)[X]) (a : Ω), f.natDegree < p ^ n → aeval (T.qq n) f = j a →
      v (j (s a - a)) ≤ v (p : Ωl) ^ N := by
  haveI := Basic.charZero_of_isClo h
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction N with
  | zero =>
    intro f a _ ha
    have h2 := v_aeval_le hv T n f
    rw [ha] at h2
    rw [map_sub, pow_zero]
    exact v.map_sub_le (hs a h2) h2
  | succ N ih =>
    intro f a hf ha
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨m, hm⟩ := res h hv h1 T n f hf (ha ▸ halg.algHom j.toIntAlgHom)
    have hf' : (f - C (m : O0 p)).natDegree < p ^ n := by rwa [natDegree_sub_C]
    obtain ⟨g, hg⟩ := orth h hv h1 T n _ hf' (by simpa using hm)
    have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpl : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpO : (p : O0 p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h3 := ih g ((a - m) / p) (by rwa [hg, natDegree_C_mul hpO] at hf') (by
      have := congrArg (aeval (T.qq n)) hg
      simp only [map_sub, map_mul, aeval_C, map_intCast, map_natCast, ha] at this
      rw [map_div₀, map_sub, map_intCast, map_natCast, this, mul_div_cancel_left₀ _ hpl])
    have h4 : s a - a = p * (s ((a - m) / p) - (a - m) / p) := by
      rw [map_div₀, map_sub, map_intCast, map_natCast]; field_simp; ring
    rw [h4, map_mul, map_mul, map_natCast, pow_succ']
    exact mul_le_mul_right h3 _

theorem fixed (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (f : (O0 p)[X]) (d : O0 p) (hd : d ≠ 0) (a : Ω)
    (ha : aeval (T.qq n) f = algebraMap (O0 p) Ωl d * j a) : s a = a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨_, hdv, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hirr
  have hpos := pow_pos hp.out.pos n
  have hmon : (X ^ (p ^ n) - C (qO p)).Monic := monic_X_pow_sub_C _ hpos.ne'
  have hdeg : ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))).natDegree < p ^ n := by
    have := natDegree_modByMonic_lt (C (↑u⁻¹ : O0 p) * f) hmon (fun h0 => by
      have := congrArg natDegree h0
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      omega)
    rwa [natDegree_X_pow_sub_C] at this
  have hev : aeval (T.qq n) ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))) = j ((p : Ω) ^ m * a) := by
    rw [aeval_modByMonic_eq_self_of_root (by simp [Basic.qq_pow]), map_mul, aeval_C, ha, ← mul_assoc,
      ← map_mul, Units.inv_mul_cancel_left]
    simp
  have h0 : v (j (s ((p : Ω) ^ m * a) - (p : Ω) ^ m * a)) = 0 := by
    by_contra hne
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.2 hne) h1
    exact absurd (approx h hv h1 T n j s hs N _ _ hdeg hev) (not_le.2 hN)
  rw [v.zero_iff, map_eq_zero, sub_eq_zero, map_mul, map_pow, map_natCast] at h0
  exact mul_left_cancel₀ (pow_ne_zero m (by exact_mod_cast hp.out.ne_zero)) h0

theorem up (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  haveI := h.clo
  haveI := h.alg
  haveI := Basic.charZero_of_isClo h
  haveI : FaithfulSMul (O0 p) Ωl := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
  letI : Algebra (FractionRing (O0 p)) Ωl := FractionRing.liftAlgebra (O0 p) Ωl
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ωl := FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ωl :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).1 h.alg
  let K := IntermediateField.adjoin (FractionRing (O0 p)) {T.qq n}
  have hfix : ∀ a : Ω, j a ∈ Set.range (algebraMap K Ωl) → s a = a := by
    rintro a ⟨⟨y, hy⟩, rfl : y = j a⟩
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, hf⟩ := hy
    obtain ⟨d, hd, hdf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (O0 p)) f
    refine fixed h hv h1 T n j s hs
      (IsLocalization.integerNormalization (nonZeroDivisors (O0 p)) f) d (nonZeroDivisors.ne_zero hd) a ?_
    rw [← aeval_map_algebraMap (FractionRing (O0 p)), hdf, ← Algebra.smul_def, ← hf,
      ← algebraMap_smul (FractionRing (O0 p)) d f, map_smul, algebraMap_smul]
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.exists_algEquiv_inducing_of_forall_conj Ω Ωl K j s (GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base Ω Ωl K j s hfix)
  refine ⟨(g.restrictScalars (FractionRing (O0 p))).restrictScalars (O0 p), ?_, hg⟩
  exact g.commutes ⟨T.qq n, IntermediateField.mem_adjoin_simple_self _ _⟩

end Local

theorem exists_gal_fix_qq_of_stab {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (h : IsClo p Ωl) (j : Ω →+* Ωl)
    (hA : ∀ x, x ∈ A ↔ IsInt p (j x)) (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (hs : Stab A s) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  obtain ⟨v, hv, -, -, h1⟩ := exists_valuation_isInt p Ωl h
  exact up h hv h1 T n j s fun x hx => (hv _).2 ((hA _).1 ((hs x).2 ((hA _).2 ((hv _).1 hx))))

end GlobalTheory.Glue.CuspUp
end
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  atlas_forward_decl GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem isAlgZp_map_of_algebraic : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (j : Ω →+* Ωl) (x : Ω), IsAlgZp p (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ j x
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 hx
  obtain ⟨P, hP, hPx⟩ := hz
  refine ⟨P.map (Int.castRingHom ℤ_[p]), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP
  · rw [Polynomial.map_map, Polynomial.aeval_def, Polynomial.eval₂_map]
    have e1 : (algebraMap (O0 p) Ωl).comp ((algebraMap ℤ_[p] (O0 p)).comp (Int.castRingHom ℤ_[p])) = j.comp (algebraMap ℤ Ω) := RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPx, map_zero]

theorem zt_prim_and_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ), 0 < l → IsPrimitiveRoot (zt ε l n) (l ^ n) ∧ zt ε l (n + 1) ^ l = zt ε l n := by
  intro Ω _ _ _ ε l n hl
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hkey : ∀ m : ℕ, ε (zt ε l m) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
    intro m
    have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne'
    have hw : Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
      congr 1; push_cast; ring
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast hN⟩
    haveI : NeZero (l ^ m) := ⟨hN⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hz' : IsPrimitiveRoot (ε z) (l ^ m) := hz.map_of_injective ε.injective
    have hp := Complex.isPrimitiveRoot_exp (l ^ m) hN
    obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one hp.pow_eq_one
    have hex : ∃ y, ε y = Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) :=
      ⟨z ^ i, by rw [map_pow, hi, hw]⟩
    show ε (Function.invFun ε _) = _
    rw [Function.invFun_eq hex, hw]
  refine ⟨?_, ?_⟩
  · rw [← IsPrimitiveRoot.map_iff_of_injective (f := ε) ε.injective, hkey]
    exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hl.ne')
  · apply ε.injective
    rw [map_pow, hkey, hkey, ← Complex.exp_nat_mul]
    congr 1
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
    ring

theorem exists_cusp_embedding : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∃ (Ωl : Type) (_ : Field Ωl) (_ : Algebra (O0 p) Ωl), IsClo p Ωl ∧ ∃ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j := by
  intro Ω _ _ _ ε X _ p _ _ A hA
  let Ωl := AlgebraicClosure (FractionRing (O0 p))
  have hcl : IsClo p Ωl := GlobalTheory.K5.Basic.isClo_algebraicClosure p
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hcl
  haveI : IsAlgClosed Ωl := hcl.clo
  let j0 : Ω →+* Ωl := (IsAlgClosed.lift : Ω →ₐ[ℚ] Ωl).toRingHom
  obtain ⟨B, hBp, hB⟩ := GlobalTheory.T.exists_valuationSubring_pullback_integral_elements p Ωl hcl j0
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime p A B hA hBp
  let j : Ω →+* Ωl := j0.comp σ.toRingEquiv.toRingHom
  have hint : ∀ x, x ∈ A ↔ IsInt p (j x) := fun x => (hσ x).symm.trans (hB _)
  have hl : 0 < p := (Fact.out : p.Prime).pos
  let T0 := (GlobalTheory.K5.Basic.nonempty_tower hcl).some
  let T : GlobalTheory.K5.Tower p Ωl :=
    { ζ := fun n => j (zt ε p n), qq := T0.qq,
      prim := fun n => (zt_prim_and_pow ε p n hl).1.map_of_injective j.injective,
      ζpow := fun n => by simp only [← map_pow, (zt_prim_and_pow ε p n hl).2],
      q0 := T0.q0, qpow := T0.qpow }
  refine ⟨Ωl, inferInstance, inferInstance, hcl, T, j, ?_⟩
  exact { int := hint, alg := isAlgZp_map_of_algebraic p Ωl j, root := fun n => rfl,
          dense := GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow p A Ωl hcl j hint, down := GlobalTheory.T.exists_algClosure_automorphism_restricting_local p A Ωl hcl j hint,
          up := fun n s hs => GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes p A Ωl hcl j hint T n s hs }

end GlobalTheory.Glue
end

section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphism_on_extension_pointwise : ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ a : Ω, j a ∈ Set.range (algebraMap K L) → s a = a) → ∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x) := by
  first | exact @GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base | exact GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base | (intros; apply GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base <;> assumption)
end

section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphism_extension_uniform : ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x)) → ∃ g : L ≃ₐ[K] L, ∀ x : Ω, g (j x) = j (s x) := by
  first | exact @GlobalTheory.exists_algEquiv_inducing_of_forall_conj | exact GlobalTheory.exists_algEquiv_inducing_of_forall_conj | (intros; apply GlobalTheory.exists_algEquiv_inducing_of_forall_conj <;> assumption)
end

section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_power_basis_independent : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (c : ℕ → LaurentSeries (ZMod p)), ∑ i ∈ Finset.range (p ^ n), c i ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ i = 0 → ∀ i < p ^ n, c i = 0 := by
  first | exact @GlobalTheory.laurent_pow_indep_over_prime_pow_powers | exact GlobalTheory.laurent_pow_indep_over_prime_pow_powers | (intros; apply GlobalTheory.laurent_pow_indep_over_prime_pow_powers <;> assumption)
end

section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_power_reduction_congruence : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) → v (p : Ωl) < 1 → ∀ (T : Tower p Ωl) (n : ℕ) (f : (O0 p)[X]), f.natDegree < p ^ n → v (aeval (T.qq n) f ^ (p ^ n) - algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i)) < 1 := by
  first | exact @GlobalTheory.aeval_qq_pow_sub_lt_one | exact GlobalTheory.aeval_qq_pow_sub_lt_one | (intros; apply GlobalTheory.aeval_qq_pow_sub_lt_one <;> assumption)
end

section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_series_algebraic_constant : ∀ (k : Type) [Field k] (f : LaurentSeries k), (∃ P : k[X], P ≠ 0 ∧ eval₂ HahnSeries.C f P = 0) → ∃ c : k, f = HahnSeries.C c := by
  first | exact @GlobalTheory.laurentSeries_eq_C_of_root | exact GlobalTheory.laurentSeries_eq_C_of_root | (intros; apply GlobalTheory.laurentSeries_eq_C_of_root <;> assumption)
end

section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_algebraic_polynomial_divisible : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) → v (p : Ωl) < 1 → ∀ (y : Ωl) (b : O0 p), IsAlgebraic ℤ y → v y ≤ 1 → v (y - algebraMap (O0 p) Ωl b) < 1 → ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
  first | exact @GlobalTheory.K5.exists_int_poly_root_mod_p | exact GlobalTheory.K5.exists_int_poly_root_mod_p | (intros; apply GlobalTheory.K5.exists_int_poly_root_mod_p <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Glue.Cusp

open GlobalTheory.K5 GlobalTheory.KZ Polynomial
open scoped NNReal

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
  {v : Valuation Ωl ℝ≥0}

theorem v_alg_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (b : O0 p) : v (algebraMap (O0 p) Ωl b) ≤ 1 :=
  (hv _).2 isIntegral_algebraMap

theorem v_alg_lt_iff (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1) (b : O0 p) :
    v (algebraMap (O0 p) Ωl b) < 1 ↔ (p : O0 p) ∣ b := by
  obtain ⟨_, hd, hirr⟩ := completed_laurent_isDVR p
  constructor
  · intro hb
    rw [← Ideal.mem_span_singleton, ← hirr.maximalIdeal_eq]
    intro hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have h2 : v (algebraMap (O0 p) Ωl b) * v (algebraMap (O0 p) Ωl c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_nonneg_of_lt_one_left zero_le hb (v_alg_le hv c)).ne
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_mul, map_natCast]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (v_alg_le hv c)

theorem exists_red : ∃ φ : O0 p →+* LaurentSeries (ZMod p),
    φ (qO p) = HahnSeries.single (1 : ℤ) (1 : ZMod p) ∧ ∀ b, φ b = 0 ↔ (p : O0 p) ∣ b := by
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk _), he, fun b => ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  exact e.map_eq_zero_iff

theorem isInt_qq (T : K5.Tower p Ωl) (n : ℕ) : IsIntegral (O0 p) (T.qq n) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos n) ?_
  rw [Basic.qq_pow]
  exact isIntegral_algebraMap

theorem v_aeval_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) :
    v (aeval (T.qq n) f) ≤ 1 :=
  (hv _).2 (IsIntegral.of_mem_of_fg _ (isInt_qq T n).fg_adjoin_singleton _
    (aeval_mem_adjoin_singleton _ _))

theorem orth (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (hlt : v (aeval (T.qq n) f) < 1) : C (p : O0 p) ∣ f := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.T.frobenius_power_reduction_congruence p Ωl h v hv h1 T n f hf
  have h3 : v (aeval (T.qq n) f ^ (p ^ n)) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le hlt (pow_pos hp.out.pos n).ne'
  have h4 := v.map_sub_lt h3 h2
  rw [sub_sub_cancel, v_alg_lt_iff hv h1, ← hφ] at h4
  simp only [map_sum, map_mul, map_pow, hq] at h4
  have h5 := GlobalTheory.T.frobenius_power_basis_independent p n (fun i => φ (f.coeff i)) h4
  rw [C_dvd_iff_dvd_coeff]
  intro i
  by_cases hi : i < p ^ n
  · exact (hφ _).1 (h5 i hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _

theorem res (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (halg : IsAlgebraic ℤ (aeval (T.qq n) f)) : ∃ m : ℤ, v (aeval (T.qq n) f - m) < 1 := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.T.frobenius_power_reduction_congruence p Ωl h v hv h1 T n f hf
  have hy := v_aeval_le hv T n f
  set y := aeval (T.qq n) f
  set b := ∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.T.residue_algebraic_polynomial_divisible p Ωl h v hv h1 (y ^ p ^ n) b (halg.pow _)
    (by rw [map_pow]; exact pow_le_one₀ zero_le hy) h2
  obtain ⟨c, hc⟩ := GlobalTheory.T.laurent_series_algebraic_constant (ZMod p) (φ b) ⟨_, hP0, by
    rw [← (hφ _).2 hP, eval₂_map, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨m, ?_⟩
  have h3 : v (algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n)) < 1 := by
    rw [v_alg_lt_iff hv h1, ← hφ, map_sub, hc, map_pow φ, map_intCast φ,
      ← map_intCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p)), ← map_pow, ZMod.pow_card_pow, sub_self]
  have hm : v (m : Ωl) ≤ 1 := (hv _).2 (Basic.isInt_intCast m)
  let y' : v.integer := ⟨y - m, v.map_sub_le hy hm⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out y' (m : v.integer) n
  have hr' := congrArg (Subtype.val) hr
  simp only [y'] at hr'
  push_cast at hr'
  have h4 : v ((p : Ωl) * (y - m) * m * r) < 1 := by
    rw [mul_assoc, mul_assoc, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (y' * ((m : v.integer) * r)).2
  have h5 := v.map_sub_lt (v.map_add_lt h2 h3) h4
  have h6 : y ^ p ^ n - algebraMap (O0 p) Ωl b + algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n) -
      (p : Ωl) * (y - m) * m * r = (y - m) ^ p ^ n := by
    rw [map_sub, map_pow, map_intCast]
    rw [sub_add_cancel] at hr'
    linear_combination hr'
  rw [h6, map_pow] at h5
  exact lt_of_pow_lt_pow_left₀ (p ^ n) zero_le_one (by rwa [one_pow])

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem approx (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (N : ℕ) : ∀ (f : (O0 p)[X]) (a : Ω), f.natDegree < p ^ n → aeval (T.qq n) f = j a →
      v (j (s a - a)) ≤ v (p : Ωl) ^ N := by
  haveI := Basic.charZero_of_isClo h
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction N with
  | zero =>
    intro f a _ ha
    have h2 := v_aeval_le hv T n f
    rw [ha] at h2
    rw [map_sub, pow_zero]
    exact v.map_sub_le (hs a h2) h2
  | succ N ih =>
    intro f a hf ha
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨m, hm⟩ := res h hv h1 T n f hf (ha ▸ halg.algHom j.toIntAlgHom)
    have hf' : (f - C (m : O0 p)).natDegree < p ^ n := by rwa [natDegree_sub_C]
    obtain ⟨g, hg⟩ := orth h hv h1 T n _ hf' (by simpa using hm)
    have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpl : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpO : (p : O0 p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h3 := ih g ((a - m) / p) (by rwa [hg, natDegree_C_mul hpO] at hf') (by
      have := congrArg (aeval (T.qq n)) hg
      simp only [map_sub, map_mul, aeval_C, map_intCast, map_natCast, ha] at this
      rw [map_div₀, map_sub, map_intCast, map_natCast, this, mul_div_cancel_left₀ _ hpl])
    have h4 : s a - a = p * (s ((a - m) / p) - (a - m) / p) := by
      rw [map_div₀, map_sub, map_intCast, map_natCast]; field_simp; ring
    rw [h4, map_mul, map_mul, map_natCast, pow_succ']
    exact mul_le_mul_right h3 _

theorem fixed (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (f : (O0 p)[X]) (d : O0 p) (hd : d ≠ 0) (a : Ω)
    (ha : aeval (T.qq n) f = algebraMap (O0 p) Ωl d * j a) : s a = a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨_, hdv, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hirr
  have hpos := pow_pos hp.out.pos n
  have hmon : (X ^ (p ^ n) - C (qO p)).Monic := monic_X_pow_sub_C _ hpos.ne'
  have hdeg : ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))).natDegree < p ^ n := by
    have := natDegree_modByMonic_lt (C (↑u⁻¹ : O0 p) * f) hmon (fun h0 => by
      have := congrArg natDegree h0
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      omega)
    rwa [natDegree_X_pow_sub_C] at this
  have hev : aeval (T.qq n) ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))) = j ((p : Ω) ^ m * a) := by
    rw [aeval_modByMonic_eq_self_of_root (by simp [Basic.qq_pow]), map_mul, aeval_C, ha, ← mul_assoc,
      ← map_mul, Units.inv_mul_cancel_left]
    simp
  have h0 : v (j (s ((p : Ω) ^ m * a) - (p : Ω) ^ m * a)) = 0 := by
    by_contra hne
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.2 hne) h1
    exact absurd (approx h hv h1 T n j s hs N _ _ hdeg hev) (not_le.2 hN)
  rw [v.zero_iff, map_eq_zero, sub_eq_zero, map_mul, map_pow, map_natCast] at h0
  exact mul_left_cancel₀ (pow_ne_zero m (by exact_mod_cast hp.out.ne_zero)) h0

theorem up (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  haveI := h.clo
  haveI := h.alg
  haveI := Basic.charZero_of_isClo h
  haveI : FaithfulSMul (O0 p) Ωl := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
  letI : Algebra (FractionRing (O0 p)) Ωl := FractionRing.liftAlgebra (O0 p) Ωl
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ωl := FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ωl :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).1 h.alg
  let K := IntermediateField.adjoin (FractionRing (O0 p)) {T.qq n}
  have hfix : ∀ a : Ω, j a ∈ Set.range (algebraMap K Ωl) → s a = a := by
    rintro a ⟨⟨y, hy⟩, rfl : y = j a⟩
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, hf⟩ := hy
    obtain ⟨d, hd, hdf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (O0 p)) f
    refine fixed h hv h1 T n j s hs
      (IsLocalization.integerNormalization (nonZeroDivisors (O0 p)) f) d (nonZeroDivisors.ne_zero hd) a ?_
    rw [← aeval_map_algebraMap (FractionRing (O0 p)), hdf, ← Algebra.smul_def, ← hf,
      ← algebraMap_smul (FractionRing (O0 p)) d f, map_smul, algebraMap_smul]
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.T.automorphism_extension_uniform Ω Ωl K j s (GlobalTheory.T.automorphism_on_extension_pointwise Ω Ωl K j s hfix)
  refine ⟨(g.restrictScalars (FractionRing (O0 p))).restrictScalars (O0 p), ?_, hg⟩
  exact g.commutes ⟨T.qq n, IntermediateField.mem_adjoin_simple_self _ _⟩

end Local

end GlobalTheory.Glue.Cusp
end
end

section
noncomputable section

namespace GlobalTheory.Glue.IoInh

open GlobalTheory.K5 GlobalTheory.KZ

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

theorem ev_single (ψ : O0 p →+* Ωl) (e : Ωl) (h1 : IsInt p e) (h2 : IsAlgZp p e) (a : Lau p) (c : ℤ → Ωl)
    (hc : ∀ r, c r = e * zp Ωl (a.coeff r)) :
    Ev ψ c (e * ψ (algebraMap (Lau p) (O0 p) a)) (e * ψ (algebraMap (Lau p) (O0 p) (thL a))) :=
  ⟨1, fun _ => e, fun _ => a, fun _ => ⟨h1, h2⟩, fun r => by simp [hc], by simp, by simp⟩

theorem zp_intCast (m : ℤ) : zp Ωl (m : ℤ_[p]) = (m : Ωl) := by
  rw [zp, ← HahnSeries.C_apply, map_intCast, map_intCast, map_intCast]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem const_mem (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : algebraMap Ω X.K c ∈ KT X L :=
  (X.sl _).commutes c

theorem exp_const (X : GlobalTheory.KZ.Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ}
  {ψ : O0 p →+* Ωl} {io : KT X (p ^ n) →+* Ωl}

theorem io_const_of_mem (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) (hA : c ∈ A) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  classical
  obtain ⟨x', hx⟩ := hio.ev ⟨algebraMap Ω X.K c, const_mem X _ c⟩ {c} (fun r => by
    simp only [exp_const]
    split_ifs
    · exact ⟨hA, IntermediateField.subset_adjoin _ _ (by simp)⟩
    · exact ⟨zero_mem _, zero_mem _⟩)
  have hp0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have h2 := ev_single ψ (j c) ((hc.int c).1 hA) (hc.alg c) 1
    (fun r : ℤ => j ((X.exp (algebraMap Ω X.K c)).coeff ((r : ℚ) / (p : ℚ) ^ n))) (fun r => by
      simp only [exp_const]
      by_cases hr : r = 0
      · subst hr
        have : zp Ωl (1 : ℤ_[p]) = 1 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 1
        simp [this]
      · have : zp Ωl (0 : ℤ_[p]) = 0 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 0
        have h3 : (r : ℚ) / (p : ℚ) ^ n ≠ 0 := div_ne_zero (by exact_mod_cast hr) hp0
        simp [this, h3, HahnSeries.coeff_one, hr])
  have := (GlobalTheory.EvUniq.ev_unique p Ωl h T n ψ hψ _ _ _ _ _ hx h2).1
  rwa [map_one, map_one, mul_one] at this

theorem io_const (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  rcases A.mem_or_inv_mem c with hA | hA
  · exact io_const_of_mem h hc hψ hio c hA
  · have h1 := io_const_of_mem h hc hψ hio c⁻¹ hA
    have h2 : (⟨algebraMap Ω X.K c⁻¹, const_mem X _ c⁻¹⟩ : KT X (p ^ n)) = ⟨algebraMap Ω X.K c, const_mem X _ c⟩⁻¹ :=
      Subtype.ext (map_inv₀ _ _)
    rw [h2, map_inv₀, map_inv₀] at h1
    exact inv_injective h1

end Local

end GlobalTheory.Glue.IoInh
end
end

section
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.PairTop

theorem extend_to_closure (K Ω' Ωl : Type) [Field K] [Field Ω'] [Field Ωl] [Algebra K Ω'] [IsAlgClosure K Ω'] [IsAlgClosed Ωl]
    (f : K →+* Ωl) : ∃ E : Ω' →+* Ωl, ∀ k, E (algebraMap K Ω' k) = f k := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : Ω' →ₐ[K] Ωl).toRingHom, fun k => (IsAlgClosed.lift : Ω' →ₐ[K] Ωl).commutes k⟩

theorem restrict_aut (F K Ω' Ωl : Type) [Field F] [Field K] [Field Ω'] [Field Ωl] [Algebra F K] [Algebra F Ω'] [Algebra K Ω']
    [IsScalarTower F K Ω'] [IsAlgClosure K Ω'] [Normal F K] (E : Ω' →+* Ωl) (g : Ωl ≃+* Ωl)
    (hg : ∀ f : F, g (E (algebraMap F Ω' f)) = E (algebraMap F Ω' f)) : ∃ τ : Ω' ≃ₐ[F] Ω', ∀ x, E (τ x) = g (E x) := by
  haveI : Algebra.IsAlgebraic F Ω' := Algebra.IsAlgebraic.trans F K Ω'
  haveI : IsAlgClosure F Ω' := ⟨IsAlgClosure.isAlgClosed K, inferInstance⟩
  haveI : Normal F Ω' := IsAlgClosure.normal F Ω'
  letI : Algebra Ω' Ωl := E.toAlgebra
  letI : Algebra F Ωl := (E.comp (algebraMap F Ω')).toAlgebra
  haveI : IsScalarTower F Ω' Ωl := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g' : Ωl ≃ₐ[F] Ωl := AlgEquiv.ofRingEquiv (f := g) hg
  exact ⟨g'.restrictNormal Ω', fun x => g'.restrictNormal_commutes Ω' x⟩

theorem locconst_finset {F Ω' : Type} [Field F] [Field Ω'] [Algebra F Ω'] (H : Subgroup (Ω' ≃ₐ[F] Ω')) {Z : Type}
    (η : (Ω' ≃ₐ[F] Ω') → Z) (hη : IsLocallyConstant (fun t : H => η t)) (g : Ω' ≃ₐ[F] Ω') (hg : g ∈ H) :
    ∃ S : Finset Ω', ∀ h ∈ H, (∀ z ∈ S, h z = g z) → η h = η g := by
  classical
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 (hη.isOpen_fiber (η g))
  have hmem : ∀ t : H, (t : Ω' ≃ₐ[F] Ω') ∈ U ↔ η t = η g := fun t => by
    have := Set.ext_iff.1 hUe t
    simpa using this
  have hV : (fun t => g * t) ⁻¹' U ∈ nhds (1 : Ω' ≃ₐ[F] Ω') :=
    (hU.preimage (continuous_mul_left g)).mem_nhds (by simpa using (hmem ⟨g, hg⟩).2 rfl)
  obtain ⟨M, hM, hsub⟩ := (krullTopology_mem_nhds_one_iff F Ω' _).1 hV
  let b := Module.finBasis F M
  refine ⟨Finset.univ.image (fun i => (b i : Ω')), fun h hh hS => ?_⟩
  have hlin : h.toLinearMap ∘ₗ M.val.toLinearMap = g.toLinearMap ∘ₗ M.val.toLinearMap :=
    b.ext fun i => hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have h1 : g⁻¹ * h ∈ M.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h2 : h x = g x := LinearMap.congr_fun hlin ⟨x, hx⟩
    rw [AlgEquiv.mul_apply, h2]
    exact g.symm_apply_apply x
  have h3 := hsub h1
  refine (hmem ⟨h, hh⟩).1 ?_
  simpa using h3

theorem cmul_hahn {Ω Ωl : Type} [Field Ω] [CharZero Ω] [Field Ωl] (j : Ω →+* Ωl) (f g : ℕ → Ω) (C D : HahnSeries ℤ Ωl)
    (hC : C.coeff = fun m => if 0 ≤ m then j (f m.toNat) else 0) (hD : D.coeff = fun m => if 0 ≤ m then j (g m.toNat) else 0)
    (m : ℤ) : (C * D).coeff m = if 0 ≤ m then j (cmul f g m.toNat) else 0 := by
  have key : ∀ (u : PowerSeries Ωl) (i : ℤ), (HahnSeries.ofPowerSeries ℤ Ωl u).coeff i =
      if 0 ≤ i then PowerSeries.coeff i.toNat u else 0 := by
    intro u i
    rw [PowerSeries.coeff_coe]
    by_cases hi : 0 ≤ i
    · rw [if_neg (not_lt.2 hi), if_pos hi]
      congr 2
      omega
    · rw [if_pos (not_le.1 hi), if_neg hi]
  have e1 : C = HahnSeries.ofPowerSeries ℤ Ωl (PowerSeries.mk fun k => j (f k)) := by
    ext i; rw [key, hC, PowerSeries.coeff_mk]
  have e2 : D = HahnSeries.ofPowerSeries ℤ Ωl (PowerSeries.mk fun k => j (g k)) := by
    ext i; rw [key, hD, PowerSeries.coeff_mk]
  rw [e1, e2, ← map_mul, key]
  split_ifs
  · rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, cmul, map_sum]
    simp only [PowerSeries.coeff_mk, map_mul]
  · rfl

section Loc

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

theorem algZp_int (u : ℤ) : IsAlgZp p (u : Ωl) :=
  ⟨Polynomial.X - Polynomial.C (u : ℤ_[p]), Polynomial.X_sub_C_ne_zero _, by simp⟩

theorem cong_le {k k' : ℕ} (h : k' ≤ k) {x y : Ωl} (hc : Cong p k x y) : Cong p k' x y := by
  obtain ⟨z, hz, e⟩ := hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨(p : Ωl) ^ d * z, IsIntegral.mul (GlobalTheory.EdgeLoc.pint d) hz, by rw [e]; ring⟩

theorem ev_coeff {ψ : O0 p →+* Ωl} {c : ℤ → Ωl} {x x' : Ωl} (h : Ev ψ c x x') (m : ℤ) : IsInt p (c m) ∧ IsAlgZp p (c m) := by
  obtain ⟨d, e, a, he, hc, -, -⟩ := h
  rw [hc m]
  refine Finset.sum_induction _ (fun y => IsInt p y ∧ IsAlgZp p y)
    (fun a b ha hb => ⟨IsIntegral.add ha.1 hb.1, GlobalTheory.GeoFix.isAlgZp_add ha.2 hb.2⟩)
    ⟨isIntegral_zero, by simpa using algZp_int (p := p) (Ωl := Ωl) 0⟩ (fun t _ => ?_)
  exact ⟨IsIntegral.mul (he t).1 isIntegral_algebraMap, EvRing.isAlgZp_mul (he t).2 (GlobalTheory.GeoFix.isAlgZp_zp _)⟩

theorem cong_coeff_mul {n : ℕ} {U V : HahnSeries ℤ Ωl} (hU : ∀ i, Cong p n (U.coeff i) 0) (hV : ∀ i, IsInt p (V.coeff i))
    (m : ℤ) : Cong p n ((U * V).coeff m) 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun y => Cong p n y 0) (fun a b ha hb => ?_) (Basic.cong_refl n 0) (fun t _ => ?_)
  · simpa using Basic.cong_add ha hb
  · simpa using Basic.cong_mul_right (hU t.1) (hV t.2)

theorem value_cong {n c0 : ℕ} {Q go o gx x Ia Ja Ib Jb za zb : Ωl} {A₁ g B₁ h : ℤ} {t : ℕ}
    (hlaw : Cong p n ((p : Ωl) ^ c0 * Q) (go - o - (p : Ωl) ^ c0 * (Ia * Jb - Ja * Ib) * (t : Ωl)))
    (h2 : Cong p n ((p : Ωl) * o) x) (h3 : Cong p n ((p : Ωl) * go) gx)
    (ha : Cong p n Ia (-(A₁ : Ωl) * za)) (hja : Cong p n ((p : Ωl) * Ja) (-(p : Ωl) * (g : Ωl) * za))
    (hb : Cong p n Ib (-(B₁ : Ωl) * zb)) (hjb : Cong p n ((p : Ωl) * Jb) (-(p : Ωl) * (h : Ωl) * zb))
    (iIa : IsInt p Ia) (iIb : IsInt p Ib) (iza : IsInt p za) (izb : IsInt p zb) :
    Cong p n ((p : Ωl) ^ (c0 + 1) * Q)
      (gx - x - (((p : ℤ) ^ (c0 + 1) * (A₁ * h - g * B₁) * (t : ℤ) : ℤ) : Ωl) * (za * zb)) := by
  obtain ⟨z1, i1, e1⟩ := hlaw
  obtain ⟨z2, i2, e2⟩ := h2
  obtain ⟨z3, i3, e3⟩ := h3
  obtain ⟨w1, j1, f1⟩ := ha
  obtain ⟨w2, j2, f2⟩ := hja
  obtain ⟨w3, j3, f3⟩ := hb
  obtain ⟨w4, j4, f4⟩ := hjb
  have ii : ∀ m : ℤ, IsIntegral (O0 p) (m : Ωl) := Basic.isInt_intCast
  refine ⟨((p : ℤ) : Ωl) * z1 + z3 - z2 - (((p : ℤ) ^ c0 * (t : ℤ) : ℤ) : Ωl) *
    (Ia * w4 - (((p : ℤ) * h : ℤ) : Ωl) * zb * w1 - Ib * w2 + (((p : ℤ) * g : ℤ) : Ωl) * za * w3), ?_, ?_⟩
  · exact ((((ii _).mul i1).add i3).sub i2).sub ((ii _).mul ((((IsIntegral.mul iIa j4).sub (((ii _).mul izb).mul j1)).sub
      (IsIntegral.mul iIb j2)).add (((ii _).mul iza).mul j3)))
  · push_cast
    linear_combination (p : Ωl) * e1 + e3 - e2 - (p : Ωl) ^ c0 * (t : Ωl) *
      (Ia * f4 - (p : Ωl) * (h : Ωl) * zb * f1 - Ib * f2 + (p : Ωl) * (g : Ωl) * za * f3)

theorem exists_xi {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (j : Ω →+* Ωl) (n L : ℕ)
    (hd : ∀ e : Ωl, IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p n e (j a)) (C : HahnSeries ℤ Ωl)
    (hC : ∀ m, IsInt p (C.coeff m) ∧ IsAlgZp p (C.coeff m)) :
    ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ (∀ r, ξ r ≠ 0 → ∃ m : ℤ, C.order ≤ m ∧ r = (m : ℚ) / (p : ℚ) ^ L) ∧
      ∀ m : ℤ, Cong p n (C.coeff m) (j (ξ ((m : ℚ) / (p : ℚ) ^ L))) := by
  classical
  have h1 : ∀ m : ℤ, ∃ a ∈ A, Cong p n (C.coeff m) (j a) ∧ (C.coeff m = 0 → a = 0) := by
    intro m
    by_cases h : C.coeff m = 0
    · exact ⟨0, zero_mem A, by rw [h, map_zero]; exact Basic.cong_refl n 0, fun _ => rfl⟩
    · obtain ⟨a, ha, hc⟩ := hd _ (hC m).1 (hC m).2
      exact ⟨a, ha, hc, fun h' => absurd h' h⟩
  choose a ha hc h0 using h1
  have hp0 : (p : ℚ) ^ L ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  refine ⟨fun r => if h : ∃ m : ℤ, r = (m : ℚ) / (p : ℚ) ^ L then a h.choose else 0, fun r => ?_, fun r hr => ?_, fun m => ?_⟩
  · dsimp only
    split_ifs
    · exact ha _
    · exact zero_mem A
  · dsimp only at hr
    split_ifs at hr with h
    · exact ⟨h.choose, HahnSeries.order_le_of_coeff_ne_zero (fun h' => hr (h0 _ h')), h.choose_spec⟩
    · exact absurd rfl hr
  · have h : ∃ m' : ℤ, (m : ℚ) / (p : ℚ) ^ L = (m' : ℚ) / (p : ℚ) ^ L := ⟨m, rfl⟩
    have e : h.choose = m := by
      have := (div_left_inj' hp0).1 h.choose_spec
      exact_mod_cast this.symm
    dsimp only
    rw [dif_pos h, e]
    exact hc m

theorem coef_bridge {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hpA : ((p : ℕ) : Ω) ∈ A.nonunits) (hclo : IsClo p Ωl) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl)
    (hint : ∀ x, x ∈ A ↔ IsInt p (j x)) (L n K0 : ℕ) (ψ : O0 p →+* Ωl) (hψ : IsReb T L ψ)
    (PA PB φ : HahnSeries ℚ Ω) (hPA : Prim A PA) (hPB : Prim A PB)
    (sA : GlobalTheory.DlEx.Sp (p ^ L) PA) (sB : GlobalTheory.DlEx.Sp (p ^ L) PB) (sφ : GlobalTheory.DlEx.Sp (p ^ L) φ) (hφA : ∀ r, φ.coeff r ∈ A)
    (hφ : ∀ r, CgA A p n ((φ * PA * PB).coeff r)
      ((theta ((p ^ L : ℕ) : ℚ) PA * PB - PA * theta ((p ^ L : ℕ) : ℚ) PB).coeff r))
    (a a' b b' : Ωl) (hEa : Ev ψ (fun m : ℤ => j (PA.coeff ((m : ℚ) / (p : ℚ) ^ L))) a a')
    (hEb : Ev ψ (fun m : ℤ => j (PB.coeff ((m : ℚ) / (p : ℚ) ^ L))) b b') (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (D : ℚ → Ω) (m0 : ℤ) (hDA : ∀ r, D r ∈ A) (hDs : ∀ r, D r ≠ 0 → ∃ m : ℤ, m0 ≤ m ∧ r = (m : ℚ) / (p : ℚ) ^ L)
    (DL : HahnSeries ℤ Ωl) (dv dv' : Ωl) (hED : Ev ψ DL.coeff dv dv')
    (hDc : ∀ m : ℤ, Cong p n (DL.coeff m) (j (D ((m : ℚ) / (p : ℚ) ^ L))))
    (hv : Cong p n ((p : Ωl) ^ K0 * (a' / a - b' / b)) dv) (r : ℚ) :
    CgA A p n ((p : Ω) ^ K0 * φ.coeff r) (D r) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hM : 0 < p ^ L := pow_pos hp.out.pos L
  have cM : ((p ^ L : ℕ) : ℚ) = (p : ℚ) ^ L := by push_cast; rfl
  have hp0 : (0 : ℚ) < (p : ℚ) ^ L := cM ▸ (by exact_mod_cast hM)
  have R := EvRing.ev_ring p Ωl hclo T L ψ hψ
  obtain ⟨ia, -, ⟨CA, hCA⟩, ⟨a'', hTA⟩, -⟩ := R.2 _ _ _ hEa
  obtain ⟨ib, -, ⟨CB, hCB⟩, ⟨b'', hTB⟩, -⟩ := R.2 _ _ _ hEb
  obtain ⟨TA, hTA'⟩ := (R.2 _ _ _ hTA).2.2.1
  obtain ⟨TB, hTB'⟩ := (R.2 _ _ _ hTB).2.2.1
  rw [← hCA] at hEa
  rw [← hCB] at hEb
  rw [← hTA'] at hTA
  rw [← hTB'] at hTB
  have hU := (R.1 _ _ _ _ _ _ (R.1 _ _ _ _ _ _ hTA hEb).1 (R.1 _ _ _ _ _ _ hEa hTB).1).2.2
  have hU2 := (R.2 _ _ _ hU).2.2.2.2.1 (((p : ℤ) ^ K0 : ℤ) : Ωl) (Basic.isInt_intCast _) (algZp_int _)
  obtain ⟨U2, hU2'⟩ := (R.2 _ _ _ hU2).2.2.1
  rw [← hU2'] at hU2
  have hW := (R.1 _ _ _ _ _ _ hU2 (R.1 _ _ _ _ _ _ hED (R.1 _ _ _ _ _ _ hEa hEb).1).1).2.2
  have hW0 := (ev_cong_iff_and_unit p Ωl hclo T L ψ hψ n _ _ _ hW).1.1 (by
    obtain ⟨z, hz, e⟩ := hv
    refine ⟨z * (a * b), IsIntegral.mul hz (IsIntegral.mul ia ib), ?_⟩
    have e2 : a' * b - a * b' = (a' / a - b' / b) * (a * b) := by field_simp
    rw [e2]
    push_cast
    linear_combination (a * b) * e)
  let Dh : HahnSeries ℚ Ω := ⟨D, by
    have h1 : (Set.Ici m0).IsPWO := Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt bddBelow_Ici)
    refine (h1.image_of_monotone (f := fun m : ℤ => (m : ℚ) / (p : ℚ) ^ L) (fun x y hxy => ?_)).mono (fun q hq => ?_)
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hxy) hp0.le
    · obtain ⟨m, hm, rfl⟩ := hDs q hq
      exact ⟨m, hm, rfl⟩⟩
  have sD : GlobalTheory.DlEx.Sp (p ^ L) Dh := by
    intro q hq
    obtain ⟨m, -, rfl⟩ := hDs q hq
    rw [cM, div_mul_cancel₀ _ hp0.ne']
    simp
  have sP := GlobalTheory.DlEx.sp_mul sA sB
  have sE : GlobalTheory.DlEx.Sp (p ^ L) ((p : Ω) ^ K0 • φ - Dh) :=
    GlobalTheory.DlEx.sp_sub (fun q hq => sφ q (fun h0 => hq (by simp [h0]))) sD
  have hP : Prim A (PA * PB) := Prim.mul A _ _ hPA hPB
  have cA : ∀ m : ℤ, CA.coeff m = j (PA.coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) := fun m => by rw [hCA, cM]
  have cB : ∀ m : ℤ, CB.coeff m = j (PB.coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) := fun m => by rw [hCB, cM]
  have cT : ∀ (P : HahnSeries ℚ Ω) (m : ℤ), j ((theta ((p ^ L : ℕ) : ℚ) P).coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) =
      (m : Ωl) * j (P.coeff ((m : ℚ) / (p : ℚ) ^ L)) := fun P m => by
    show j (algebraMap ℚ Ω (((p ^ L : ℕ) : ℚ) * ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) * P.coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) = _
    rw [cM, mul_div_cancel₀ _ hp0.ne', map_intCast, map_mul, map_intCast]
  have cTA : ∀ m : ℤ, TA.coeff m = j ((theta ((p ^ L : ℕ) : ℚ) PA).coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) :=
    fun m => by rw [hTA', cT]
  have cTB : ∀ m : ℤ, TB.coeff m = j ((theta ((p ^ L : ℕ) : ℚ) PB).coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) :=
    fun m => by rw [hTB', cT]
  have cP := GlobalTheory.IoEx.restrict_mul j hM PA PB CA CB sA sB cA cB
  obtain ⟨D0, hD0⟩ := GlobalTheory.IoEx.exists_restrict hM Dh
  have cD : ∀ m : ℤ, (D0.map j).coeff m = j (Dh.coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ))) := fun m => by
    rw [HahnSeries.map_coeff, hD0]
  have key := GlobalTheory.primCan p A hpA n (p ^ L) (PA * PB) ((p : Ω) ^ K0 • φ - Dh) hM hP sP (fun q => by
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_smul, smul_eq_mul]
      exact sub_mem (mul_mem (pow_mem (natCast_mem A p) _) (hφA q)) (hDA q)) (fun q => by
    by_cases hq : (q * ((p ^ L : ℕ) : ℚ)).den = 1
    · obtain ⟨m, rfl⟩ : ∃ m : ℤ, q = (m : ℚ) / ((p ^ L : ℕ) : ℚ) :=
        ⟨(q * ((p ^ L : ℕ) : ℚ)).num, by rw [(Rat.den_eq_one_iff _).1 hq, mul_div_cancel_right₀ _ (cM ▸ hp0.ne')]⟩
      obtain ⟨z, hz, ez⟩ := hφ ((m : ℚ) / ((p ^ L : ℕ) : ℚ))
      obtain ⟨w, hw, ew⟩ := hW0 m
      obtain ⟨y, hy, ey⟩ := cong_coeff_mul (p := p) (n := n) (U := DL - D0.map j) (V := CA * CB) (fun i => by
        obtain ⟨y, hy, ey⟩ := hDc i
        refine ⟨y, hy, ?_⟩
        rw [HahnSeries.coeff_sub, cD, cM, sub_zero]
        exact ey) (fun i => by rw [cP]; exact (hint _).1 (hP.1 _)) m
      rw [sub_mul, HahnSeries.coeff_sub, GlobalTheory.IoEx.restrict_mul j hM Dh (PA * PB) _ _ sD sP cD cP] at ey
      rw [HahnSeries.coeff_sub, hU2'] at ew
      dsimp only at ew
      rw [HahnSeries.coeff_sub, GlobalTheory.IoEx.restrict_mul j hM _ PB _ _ (GlobalTheory.DlEx.sp_theta _ sA) sB cTA cB,
        GlobalTheory.IoEx.restrict_mul j hM PA _ _ _ sA (GlobalTheory.DlEx.sp_theta _ sB) cA cTB] at ew
      rw [HahnSeries.coeff_sub] at ez
      have ez' := congrArg j ez
      have e0 : ((p : Ω) ^ K0 • φ - Dh) * (PA * PB) = (p : Ω) ^ K0 • (φ * PA * PB) - Dh * (PA * PB) := by
        rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]; ring
      rw [e0, HahnSeries.coeff_sub, HahnSeries.coeff_smul, smul_eq_mul]
      have hpn : (p : Ω) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      have hpn' : (p : Ωl) ^ n ≠ 0 := by
        have := (map_ne_zero j).2 hpn
        rwa [map_pow, map_natCast] at this
      generalize (φ * PA * PB).coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ)) = X1 at ez' ⊢
      generalize (Dh * (PA * PB)).coeff ((m : ℚ) / ((p ^ L : ℕ) : ℚ)) = X2 at ey ⊢
      refine ⟨((p : Ω) ^ K0 * X1 - X2) / (p : Ω) ^ n, (hint _).2 ?_, by field_simp; ring⟩
      have e5 : j (((p : Ω) ^ K0 * X1 - X2) / (p : Ω) ^ n) = (p : Ωl) ^ K0 * j z + w + y := by
        simp only [map_div₀, map_sub, map_mul, map_pow, map_natCast] at ez' ⊢
        rw [div_eq_iff hpn']
        rw [Int.cast_pow, Int.cast_natCast] at ew
        linear_combination (p : Ωl) ^ K0 * ez' + ew + ey
      rw [e5]
      exact ((IsIntegral.mul (GlobalTheory.EdgeLoc.pint K0) ((hint z).1 hz)).add hw).add hy
    · have : (((p : Ω) ^ K0 • φ - Dh) * (PA * PB)).coeff q = 0 := by
        by_contra h0
        exact hq (GlobalTheory.DlEx.sp_mul sE sP q h0)
      rw [this]
      exact ⟨0, zero_mem A, by simp⟩) r
  obtain ⟨z, hz, ez⟩ := key
  refine ⟨z, hz, ?_⟩
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_smul, smul_eq_mul, sub_zero] at ez
  exact ez

end Loc

open GlobalTheory.DlEx in

theorem dl_pres {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (hl : ((l : ℕ) : Ω) ∈ A.nonunits) (n L : ℕ) (f : X.K) (hL : 0 < L) (hf : f ≠ 0) (hfK : f ∈ KT X L) :
    ∃ (a b : X.K) (κ : Ω) (S : Finset Ω) (φ : HahnSeries ℚ Ω), κ ≠ 0 ∧ a ∈ KT X L ∧ b ∈ KT X L ∧
      f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧
      (∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
        (X.exp b).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) ∧
      (∀ r, φ.coeff r ∈ A) ∧ Sp L φ ∧
      ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta L (X.exp a) * X.exp b - X.exp a * theta L (X.exp b)).coeff r) := by
  obtain ⟨a, b, κ, S, hκ, hfb, ha, hb, hbinv, hS⟩ := GlobalTheory.exists_prim_frac_level_one ε X hj l A hl f hf
  have hbK : b ∈ KT X L := (RingHom.mem_eqLocusField).2 (hbinv _)
  have hcK : algebraMap Ω X.K κ ∈ KT X L := (RingHom.mem_eqLocusField).2 ((X.sl _).commutes κ)
  have haK : a ∈ KT X L := by
    have e : a = (algebraMap Ω X.K κ)⁻¹ * (f * b) := by
      rw [hfb, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 hκ), one_mul]
    rw [e]; exact (KT X L).mul_mem ((KT X L).inv_mem hcK) ((KT X L).mul_mem hfK hbK)
  have hsa : Sp L (X.exp a) := (KTExp.mem_KT_iff ε X L hL a).1 haK
  have hsb : Sp L (X.exp b) := (KTExp.mem_KT_iff ε X L hL b).1 hbK
  have hP : Prim A (X.exp a * X.exp b) := Prim.mul A _ _ ha hb
  obtain ⟨Q, hQA, hQs, hQP⟩ := GlobalTheory.prim_inv_mod_pow l A hl n L (X.exp a * X.exp b) hL hP (sp_mul hsa hsb)
  have hDA : ∀ r, (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)).coeff r ∈ A :=
    intA_sub A (intA_mul A (intA_theta A ha.1 hsa) hb.1) (intA_mul A ha.1 (intA_theta A hb.1 hsb))
  have hDs : Sp L (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)) :=
    sp_sub (sp_mul (sp_theta _ hsa) hsb) (sp_mul hsa (sp_theta _ hsb))
  refine ⟨a, b, κ, S, Q * (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)),
    hκ, haK, hbK, hfb, ha, hb, hS, intA_mul A hQA hDA, sp_mul hQs hDs, ?_⟩
  intro r
  generalize theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b) = D at hDA ⊢
  choose z hzA hz using hQP
  have e : (Q * D * X.exp a * X.exp b).coeff r - D.coeff r = (D * (Q * (X.exp a * X.exp b) - 1)).coeff r := by
    rw [show Q * D * X.exp a * X.exp b = D * (Q * (X.exp a * X.exp b)) by ring, mul_sub, mul_one,
      HahnSeries.coeff_sub]
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support (Q * (X.exp a * X.exp b) - 1).isPWO_support r,
    D.coeff ij.1 * z ij.2, Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hDA _) (hzA _)), ?_⟩
  rw [e, HahnSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ij _ => ?_)
  rw [HahnSeries.coeff_sub, hz ij.2]; ring

open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB in

theorem galois_side {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl] (T : GlobalTheory.K5.Tower p Ωl) (L n : ℕ)
    {F K Ω' : Type} [Field F] [Field K] [Field Ω'] [Algebra F K] [Algebra F Ω'] [Algebra K Ω'] [IsScalarTower F K Ω']
    [IsAlgClosure K Ω'] [Normal F K] (E : Ω' →+* Ωl) (ζ α β : Ω') (hζ : E ζ = T.ζ n)
    (hfix : ∀ g ∈ Ggeo p Ωl ⊓ Gn T L, ∀ k : K, g (E (algebraMap K Ω' k)) = E (algebraMap K Ω' k))
    (hα0 : E α ≠ 0) (hβ0 : E β ≠ 0) (xl yl : Gal p Ωl → ZMod (p ^ n))
    (hxl : IsKum T n (Gn T L) (E α) xl) (hyl : IsKum T n (Gn T L) (E β) yl)
    (x y : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod (p ^ n)))
    (hx : ∀ t, (x t).toAdd = kum (K := F) (N := p ^ n) ζ α t) (hy : ∀ t, (y t).toAdd = kum (K := F) (N := p ^ n) ζ β t)
    (η : (Ω' ≃ₐ[F] Ω') → ZMod (p ^ n)) (hη : CobOn (geo F K Ω') x y η)
    (hlc : IsLocallyConstant (fun t : geo F K Ω' => η t)) :
    ∃ ηl : Gal p Ωl → ZMod (p ^ n),
      (∀ g ∈ (Ggeo p Ωl ⊓ Gn T L), ∀ h ∈ (Ggeo p Ωl ⊓ Gn T L), xl g * yl h = ηl h - ηl (g * h) + ηl g) ∧
      (∀ g ∈ (Ggeo p Ωl ⊓ Gn T L), ∃ S : Finset Ωl, ∀ h ∈ (Ggeo p Ωl ⊓ Gn T L), (∀ z ∈ S, h z = g z) → ηl h = ηl g) ∧
      ∀ g0 ∈ Gn T L, (∀ f : F, g0 (E (algebraMap F Ω' f)) = E (algebraMap F Ω' f)) →
      ∀ σ : Ω' ≃ₐ[F] Ω', (∀ k k' : K, g0 (E (algebraMap K Ω' k)) = E (algebraMap K Ω' k') →
        σ (algebraMap K Ω' k) = algebraMap K Ω' k') →
      ∀ (w : K) (θ : Ω'), w ≠ 0 → θ ^ (p ^ n) = algebraMap K Ω' w →
        (∀ g ∈ geo F K Ω', kum (K := F) (N := p ^ n) ζ θ g = edge x y η σ g) →
        IsKum T n (Ggeo p Ωl ⊓ Gn T L) (E θ) (fun h => ηl (g0 * h * g0⁻¹) - ηl h - xl h * yl g0 + xl g0 * yl h) := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hEinj : Function.Injective E := E.injective
  have hζp : IsPrimitiveRoot ζ (p ^ n) := (IsPrimitiveRoot.map_iff_of_injective hEinj).1 (hζ ▸ T.prim n)
  let Fx : Gal p Ωl → Prop := fun g => ∀ f : F, g (E (algebraMap F Ω' f)) = E (algebraMap F Ω' f)
  have hex : ∀ g : Gal p Ωl, ∃ τ : Ω' ≃ₐ[F] Ω', Fx g → ∀ z, E (τ z) = g (E z) := by
    intro g
    by_cases hg : Fx g
    · obtain ⟨τ, hτ⟩ := restrict_aut F K Ω' Ωl E g.toRingEquiv hg
      exact ⟨τ, fun _ => hτ⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose res hres using hex
  have huniq : ∀ g τ, Fx g → (∀ z, E (τ z) = g (E z)) → res g = τ := fun g τ hg h =>
    AlgEquiv.ext fun z => hEinj ((hres g hg z).trans (h z).symm)
  have hFx : ∀ g ∈ Ggeo p Ωl ⊓ Gn T L, Fx g := fun g hg f => by
    rw [IsScalarTower.algebraMap_apply F K Ω']; exact hfix g hg _
  have hgeo : ∀ g ∈ Ggeo p Ωl ⊓ Gn T L, res g ∈ geo F K Ω' := fun g hg =>
    (TopW.mem_geo _).2 fun k => hEinj ((hres g (hFx g hg) _).trans (hfix g hg k))
  have hk : ∀ (γ : Ω') (zl : Gal p Ωl → ZMod (p ^ n)), E γ ≠ 0 → IsKum T n (Gn T L) (E γ) zl →
      ∀ g ∈ Gn T L, Fx g → kum (K := F) (N := p ^ n) ζ γ (res g) = zl g := by
    intro γ zl h0 hz g hg hF
    refine kum_eq_of hζp (fun h => h0 (by rw [h, map_zero])) _ (hEinj ?_)
    rw [hres g hF, hz g hg, map_mul, map_pow, hζ]
  have hxe : ∀ g ∈ Gn T L, Fx g → (x (res g)).toAdd = xl g := fun g hg hF => (hx _).trans (hk α xl hα0 hxl g hg hF)
  have hye : ∀ g ∈ Gn T L, Fx g → (y (res g)).toAdd = yl g := fun g hg hF => (hy _).trans (hk β yl hβ0 hyl g hg hF)
  refine ⟨fun g => η (res g), fun g hg h hh => ?_, fun g hg => ?_, ?_⟩
  · have e : res (g * h) = res g * res h := huniq _ _ (hFx _ (Subgroup.mul_mem _ hg hh)) fun z => by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hres g (hFx g hg), hres h (hFx h hh)]
    have := hη _ (hgeo g hg) _ (hgeo h hh)
    rw [hxe g hg.2 (hFx g hg), hye h hh.2 (hFx h hh), ← e] at this
    exact this
  · obtain ⟨S, hS⟩ := locconst_finset _ η hlc (res g) (hgeo g hg)
    refine ⟨S.image E, fun h hh hz => hS _ (hgeo h hh) fun z hzS => hEinj ?_⟩
    rw [hres g (hFx g hg), hres h (hFx h hh)]
    exact hz _ (Finset.mem_image_of_mem _ hzS)
  · intro g0 hg0 hF0 σ hσ w θ hw0 hθ hkum h hh
    haveI : (geo F K Ω').Normal := ⟨fun m hm s => TopW.conj_mem_geo s hm⟩
    obtain ⟨P1, P2, P3⟩ := edge_cup_props _ (p ^ n) (geo F K Ω') x y η hη
    have hinv : ∀ z, E ((res g0)⁻¹ z) = g0⁻¹ (E z) := fun z => by
      have h1 := hres g0 hF0 ((res g0)⁻¹ z)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h1
      rw [h1, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hF1 : Fx (g0 * h * g0⁻¹) := fun f => by
      have h1 : g0⁻¹ (E (algebraMap F Ω' f)) = E (algebraMap F Ω' f) := by rw [← hinv, AlgEquiv.commutes]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hFx h hh f, hF0 f]
    have e1 : res (g0 * h * g0⁻¹) = res g0 * res h * (res g0)⁻¹ := huniq _ _ hF1 fun z => by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hres g0 hF0, hres h (hFx h hh), hinv]
    have h0 : σ⁻¹ * res g0 ∈ geo F K Ω' := (TopW.mem_geo _).2 fun k => by
      have h1 := (res g0).restrictNormal_commutes K k
      have h2 := hσ k ((res g0).restrictNormal K k) (by rw [h1, hres g0 hF0])
      rw [AlgEquiv.mul_apply, ← h1, ← h2, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 : edge x y η (res g0) (res h) = edge x y η σ (res h) := by
      have hm := hgeo h hh
      have hc : σ⁻¹ * res g0 * res h * (σ⁻¹ * res g0)⁻¹ ∈ geo F K Ω' := TopW.conj_mem_geo _ hm
      have a1 := P2 σ (σ⁻¹ * res g0) (res h) hm
      rw [mul_inv_cancel_left, P3 _ h0 _ hm, add_zero] at a1
      have a2 := P1 σ _ hc _ h0
      rw [inv_mul_cancel_right, P1 σ _ h0 _ hm] at a2
      rw [a1]
      linear_combination -a2
    have e3 := TopW.apply_eq_kum (F := F) hζp hw0 hθ (hgeo h hh)
    rw [hkum _ (hgeo h hh), ← e2] at e3
    have e4 := congrArg E e3
    rw [hres h (hFx h hh), map_mul, map_pow, hζ] at e4
    rw [e4]
    dsimp only
    rw [e1, ← hxe h hh.2 (hFx h hh), ← hye h hh.2 (hFx h hh), ← hxe g0 hg0 hF0, ← hye g0 hg0 hF0]
    rfl

theorem unit_val {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl] {Ω : Type} [Field Ω]
    (hclo : IsClo p Ωl) {T : GlobalTheory.K5.Tower p Ωl} {n : ℕ} {ψ : O0 p →+* Ωl} (hreb : IsReb T n ψ) {A : ValuationSubring Ω}
    {j : Ω →+* Ωl} (hint : ∀ z, z ∈ A ↔ IsInt p (j z)) {φ : HahnSeries ℚ Ω} {x x' : Ωl}
    (hP : Prim A φ) (hs : GlobalTheory.DlEx.Sp (p ^ n) φ) (hx : Ev ψ (fun r : ℤ => j (φ.coeff ((r : ℚ) / (p : ℚ) ^ n))) x x') :
    x ≠ 0 ∧ IsInt p x⁻¹ := by
  obtain ⟨-, r0, h0, hinv⟩ := hP
  have hd := hs r0 h0
  have hpn : ((p ^ n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (pow_pos hp.out.pos n).ne'
  have hm : (((r0 * ((p ^ n : ℕ) : ℚ)).num : ℤ) : ℚ) / (p : ℚ) ^ n = r0 := by
    rw [← GlobalTheory.IoEx.castM, (Rat.den_eq_one_iff _).1 hd, mul_div_cancel_right₀ _ hpn]
  refine (ev_cong_iff_and_unit p Ωl hclo T n ψ hreb 0 _ x x' hx).2 ⟨(r0 * ((p ^ n : ℕ) : ℚ)).num, ?_, ?_⟩
  · simp only [hm]; exact (map_ne_zero j).2 h0
  · simp only [hm]; rw [← map_inv₀]; exact (hint _).1 hinv

theorem coefQ_div {Ω : Type} [Field Ω] (p L : ℕ) (hp : 0 < p) (f : ℕ → Ω) (m : ℤ) :
    coefQ (p ^ L) f ((m : ℚ) / (p : ℚ) ^ L) = if 0 ≤ m then f m.toNat else 0 := by
  have hp0 : (0 : ℚ) < (p : ℚ) ^ L := pow_pos (by exact_mod_cast hp) L
  have e : (m : ℚ) / (p : ℚ) ^ L * ((p ^ L : ℕ) : ℚ) = m := by
    rw [GlobalTheory.IoEx.castM, div_mul_cancel₀ _ hp0.ne']
  have e2 : 0 ≤ (m : ℚ) / (p : ℚ) ^ L ↔ 0 ≤ m := by
    rw [le_div_iff₀ hp0, zero_mul]; exact Int.cast_nonneg_iff
  simp only [coefQ, e, e2, Rat.den_intCast, Rat.num_intCast, and_true]

theorem coefQ_supp {Ω : Type} [Field Ω] (p L : ℕ) (hp : 0 < p) (f : ℕ → Ω) (r : ℚ) (h : coefQ (p ^ L) f r ≠ 0) :
    ∃ m : ℤ, 0 ≤ m ∧ r = (m : ℚ) / (p : ℚ) ^ L := by
  have hp0 : (0 : ℚ) < (p : ℚ) ^ L := pow_pos (by exact_mod_cast hp) L
  have h1 : 0 ≤ r ∧ (r * ((p ^ L : ℕ) : ℚ)).den = 1 := by
    by_contra h2
    exact h (if_neg h2)
  refine ⟨(r * ((p ^ L : ℕ) : ℚ)).num, Rat.num_nonneg.2 (mul_nonneg h1.1 (Nat.cast_nonneg _)), ?_⟩
  rw [(Rat.den_eq_one_iff _).1 h1.2, GlobalTheory.IoEx.castM, mul_div_cancel_right₀ _ hp0.ne']

end GlobalTheory.PairTop

open GlobalTheory.PairTop in

theorem GlobalTheory.pair_edge_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n N c d : ℕ) (A₁ a₂ g B₁ b₂ h : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → b₂ ≡ N * h [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → (N : ℤ) ∣ b₂ → 1 ≤ n → n ≤ L → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → 1 < d → Nat.Coprime d (6 * N * p) →
    ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ B₁) →
  ∀ (F K Ω' : Type) [Field F] [Field K] [Field Ω'] [Algebra F K] [Algebra F Ω'] [Algebra K Ω'] [IsScalarTower F K Ω'] [IsAlgClosure K Ω'] [Normal F K]
    (e : K →+* X.K), (∀ y, e y ∈ KT X (p ^ L)) →
  ∀ (z a b : K) (ζ α β : Ω'), e z = algebraMap Ω X.K (zt ε p n) → ζ = algebraMap K Ω' z →
    e a = sgN X c N (N * p ^ L) (A₁, a₂) → e b = sgN X d N (N * p ^ L) (B₁, b₂) →
    α ^ (p ^ n) = algebraMap K Ω' a → β ^ (p ^ n) = algebraMap K Ω' b →
  ∀ (x y : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod (p ^ n))), (∀ t, (x t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ α t) → (∀ t, (y t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ β t) →
  ∀ η : (Ω' ≃ₐ[F] Ω') → ZMod (p ^ n), GlobalTheory.KEdge.CobOn (GlobalTheory.K4.geo F K Ω') x y η → IsLocallyConstant (fun t : GlobalTheory.K4.geo F K Ω' => η t) →
  ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, Stab A s → s (zt ε p L) = zt ε p L → (∀ f : F, X.gal s (e (algebraMap F K f)) = e (algebraMap F K f)) →
    ∀ σ : Ω' ≃ₐ[F] Ω', (∀ k k' : K, e k' = X.gal s (e k) → σ (algebraMap K Ω' k) = algebraMap K Ω' k') →
    ∀ (w : K) (φ : HahnSeries ℚ Ω) (t : ZMod (p ^ n)), GlobalTheory.K4.IsTopW ζ x y η σ w → IsDl X A p n ((p : ℚ) ^ L) (e w) φ →
      s (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n) →
      ∀ r : ℚ, CgA A p n ((p : Ω) ^ cc * φ.coeff r)
        (s.symm (ξ r) - ξ r - (p : Ω) ^ cc * ((A₁ * h - g * B₁ : ℤ) : Ω) * (t.val : Ω) *
          coefQ (p ^ L) (cmul (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂) (smF d 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) B₁ b₂)) r) := by
  intro p _ hp2
  obtain ⟨c0, hc0⟩ := GlobalTheory.EdgeLoc.edge_dlog p hp2
  refine ⟨c0 + 1, ?_⟩
  intro Ω _ _ _ ε X hj A hpA L n N c d A₁ a₂ g B₁ b₂ h ha₂ hb₂ hNa hNb hn1 hnL hN hNp hc1 hcc hd1 hdc hA₁ hB₁
    F K Ω' _ _ _ _ _ _ _ _ _ e he z a b ζ α β hz hζ ha hb hα hβ x y hx hy η hη hηlc
  have hp : p.Prime := Fact.out
  have hL1 : 1 ≤ L := le_trans hn1 hnL
  have hM : 0 < p ^ L := pow_pos hp.pos L
  obtain ⟨Ωl, _, _, hclo, T, j, hcusp⟩ := exists_cusp_embedding ε X hj p hp2 A hpA
  haveI : IsAlgClosed Ωl := hclo.clo
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ψ, hψ⟩ := exists_isReb p Ωl hclo T L
  obtain ⟨io, hio⟩ := GlobalTheory.IoEx.exists_isIo ε X hj p hp2 A hpA Ωl hclo T j hcusp L ψ hψ
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T L
  obtain ⟨u, αa, βa, za, za', hdla, hua, hEva, hαa, hβa⟩ := GlobalTheory.T.siegel_logCoords_alt ε X hj p hp2 A hpA Ωl hclo T j hcusp L ψ io hL1 hψ hio
    ι hι N c A₁ a₂ g ha₂ hNa hN hNp hc1 hcc hA₁ ⟨e a, he a⟩ ha
  obtain ⟨v, αb, βb, zb, zb', hdlb, hvb, hEvb, hαb, hβb⟩ := GlobalTheory.T.siegel_logCoords_alt ε X hj p hp2 A hpA Ωl hclo T j hcusp L ψ io hL1 hψ hio
    ι hι N d B₁ b₂ h hb₂ hNb hN hNp hd1 hdc hB₁ ⟨e b, he b⟩ hb
  obtain ⟨E, hEK⟩ := extend_to_closure K Ω' Ωl (io.comp (e.codRestrict (KT X (p ^ L)) he))
  replace hEK : ∀ k, E (algebraMap K Ω' k) = io ⟨e k, he k⟩ := hEK
  have hconst := IoInh.io_const hclo hcusp hψ hio
  have hEζ : E ζ = T.ζ n := by
    rw [hζ, hEK, ← hcusp.root, ← hconst]
    exact congrArg io (Subtype.ext hz)
  have hfix : ∀ g' ∈ Ggeo p Ωl ⊓ Gn T L, ∀ k : K, g' (E (algebraMap K Ω' k)) = E (algebraMap K Ω' k) := by
    intro g' hg' k
    rw [hEK]
    refine hio.gal g' 1 ((Basic.mem_gn T L g').1 hg'.2).2 (fun x => hg'.1 _ (hcusp.alg x)) _ _ ?_
    apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
    ext r
    exact (X.gal_exp 1 _ r).symm
  have hrα : E α ^ (p ^ n) = ι u := by rw [← map_pow, hα, hEK, hua]
  have hrβ : E β ^ (p ^ n) = ι v := by rw [← map_pow, hβ, hEK, hvb]
  have hα0 : E α ≠ 0 := fun h0 => (u.isUnit.map ι).ne_zero (by rw [← hrα, h0, zero_pow (pow_ne_zero _ hp.ne_zero)])
  have hβ0 : E β ≠ 0 := fun h0 => (v.isUnit.map ι).ne_zero (by rw [← hrβ, h0, zero_pow (pow_ne_zero _ hp.ne_zero)])
  obtain ⟨xl, hxl⟩ := Basic.exists_isKum T n (Gn T L) hα0 (fun g' hg' => by rw [hrα]; exact GlobalTheory.EdgeLoc.emb_fix T hι hg' _)
  obtain ⟨yl, hyl⟩ := Basic.exists_isKum T n (Gn T L) hβ0 (fun g' hg' => by rw [hrβ]; exact GlobalTheory.EdgeLoc.emb_fix T hι hg' _)
  have hζ0 : T.ζ (L + n) ≠ 0 := (T.prim _).ne_zero (pow_ne_zero _ hp.ne_zero)
  obtain ⟨lz, hlz⟩ := Basic.exists_isKum T n (Gn T L) hζ0 (fun g' hg' => by
    rw [GlobalTheory.EdgeLoc.pow_chain T.ζ T.ζpow]; exact ((Basic.mem_gn T L g').1 hg').1)
  obtain ⟨ηl, hcoc, hlc, hedge⟩ := galois_side (K := K) T L n E ζ α β hEζ hfix hα0 hβ0 xl yl hxl hyl x y hx hy η hη hηlc
  obtain ⟨o, hoi, hof, hlaw⟩ := hc0 Ωl hclo T L n hnL hn1 ψ hψ ι hι u v αa βa αb βb hdla hdlb _ _ hrα hrβ xl yl lz ηl
    hxl hyl hlz hcoc hlc
  have ip : IsInt p (p : Ωl) := by simpa using GlobalTheory.EdgeLoc.pint (p := p) (Ω := Ωl) 1
  obtain ⟨cξ, xo, xo', hEo, hco⟩ := GlobalTheory.GeoFix.geofix p Ωl hclo T L ψ hψ n ((p : Ωl) * o) (IsIntegral.mul ip hoi)
    (fun g' hg' => by rw [map_mul, map_natCast, hof g' hg'])
  have R := EvRing.ev_ring p Ωl hclo T L ψ hψ
  obtain ⟨Cξ, rfl⟩ := (R.2 _ _ _ hEo).2.2.1
  obtain ⟨ξ, hξA, hξs, hξc⟩ := exists_xi A j n L (hcusp.dense n) Cξ (ev_coeff hEo)
  refine ⟨ξ, hξA, ?_⟩
  intro s hsA hsL hsF σ hσ w φ t hw hφ ht r
  obtain ⟨g0, hg0q, hg0j⟩ := hcusp.up L s hsA
  have hg0 : g0 ∈ Gn T L := (Basic.mem_gn T L g0).2 ⟨by rw [← hcusp.root, hg0j, hsL], hg0q⟩
  obtain ⟨hw0, θ, hθ, hθk⟩ := hw
  have hkum := hedge g0 hg0 (fun f => by
      rw [IsScalarTower.algebraMap_apply F K Ω', hEK]
      exact hio.gal g0 s hg0q hg0j _ _ (hsF f).symm) σ (fun k k' hkk => by
      have hm : X.gal s (e k) ∈ KT X (p ^ L) := by
        rw [KTExp.mem_KT_iff ε X _ hM]
        intro q hq
        rw [X.gal_exp] at hq
        exact (KTExp.mem_KT_iff ε X _ hM _).1 (he k) q (fun h0 => hq (by rw [h0, map_zero]))
      rw [hEK, hEK, hio.gal g0 s hg0q hg0j ⟨e k, he k⟩ ⟨_, hm⟩ rfl] at hkk
      exact hσ k k' (congrArg Subtype.val (io.injective hkk)).symm) w θ hw0 hθ hθk
  obtain ⟨Aw, Bw, κ, S, φ2, hκ, hAK, hBK, hpres, hPA, hPB, hS, hφ2A, hφ2s, hφ2c⟩ :=
    dl_pres ε X hj p A hpA n (p ^ L) (e w) hM ((map_ne_zero e).2 hw0) (he w)
  have sA : GlobalTheory.DlEx.Sp (p ^ L) (X.exp Aw) := (KTExp.mem_KT_iff ε X _ hM _).1 hAK
  have sB : GlobalTheory.DlEx.Sp (p ^ L) (X.exp Bw) := (KTExp.mem_KT_iff ε X _ hM _).1 hBK
  obtain ⟨a', hEa⟩ := hio.ev ⟨Aw, hAK⟩ S (fun q => ⟨hPA.1 q, (hS q).1⟩)
  obtain ⟨b', hEb⟩ := hio.ev ⟨Bw, hBK⟩ S (fun q => ⟨hPB.1 q, (hS q).2⟩)
  obtain ⟨ha0, hai⟩ := unit_val hclo hψ hcusp.int hPA sA hEa
  obtain ⟨hb0, hbi⟩ := unit_val hclo hψ hcusp.int hPB sB hEb
  have hl := hlaw g0 hg0 (E θ) (j κ) _ a' _ b' _ _ hkum ((map_ne_zero j).2 hκ) (hcusp.alg κ) (by
    rw [← map_pow, hθ, hEK, ← hconst, ← map_mul, ← map_mul]
    exact congrArg io (Subtype.ext hpres)) hEa hEb ha0 hai hb0 hbi
  have hlt : lz g0 = t := by
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have e1 := hlz g0 hg0
    have e2 : g0 (T.ζ (L + n)) = T.ζ n ^ t.val * T.ζ (L + n) := by
      rw [← hcusp.root, hg0j, ht, map_mul, map_pow, hcusp.root]
    have e3 := mul_right_cancel₀ hζ0 (e1.symm.trans e2)
    rw [Basic.zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e3
    simpa using e3
  rw [hlt, map_sub, map_mul, map_mul] at hl
  obtain ⟨iza, -, ⟨Ca, hCa⟩, -⟩ := R.2 _ _ _ hEva
  obtain ⟨izb, -, ⟨Cb, hCb⟩, -⟩ := R.2 _ _ _ hEvb
  have hval := value_cong hl hco (by simpa only [map_mul, map_natCast] using Basic.cong_gal g0⁻¹ hco)
    (cong_le hnL hαa) (cong_le hnL hβa) (cong_le hnL hαb) (cong_le hnL hβb)
    (GlobalTheory.EdgeLoc.emb_int L ι _) (GlobalTheory.EdgeLoc.emb_int L ι _) iza izb
  have hq' : g0⁻¹ (T.qq L) = T.qq L := ((Basic.mem_gn T L _).1 ((Gn T L).inv_mem hg0)).2
  have hG := (R.2 _ _ _ hEo).2.2.2.2.2 g0⁻¹ hq'
  obtain ⟨CG, hCG⟩ := (R.2 _ _ _ hG).2.2.1
  rw [← hCG] at hG
  rw [← hCa] at hEva
  rw [← hCb] at hEvb
  have hZ0 := (R.1 _ _ _ _ _ _ hEva hEvb).1
  have hZ := (R.2 _ _ _ hZ0).2.2.2.2.1 (((p : ℤ) ^ (c0 + 1) * (A₁ * h - g * B₁) * (t.val : ℤ) : ℤ) : Ωl)
    (Basic.isInt_intCast _) (algZp_int _)
  obtain ⟨CZ, hCZ⟩ := (R.2 _ _ _ hZ).2.2.1
  rw [← hCZ] at hZ
  have hD := (R.1 _ _ _ _ _ _ (R.1 _ _ _ _ _ _ hG hEo).2.2 hZ).2.2
  have hmul := cmul_hahn j _ _ Ca Cb hCa hCb
  generalize cmul (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂)
    (smF d 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) B₁ b₂) = f at hmul ⊢
  have hjf : ∀ m : ℤ, j (coefQ (p ^ L) f ((m : ℚ) / (p : ℚ) ^ L)) = (Ca * Cb).coeff m := fun m => by
    rw [coefQ_div p L hp.pos, hmul]
    split_ifs
    · rfl
    · exact map_zero j
  have hbr := coef_bridge A hpA hclo T j hcusp.int L n (c0 + 1) ψ hψ _ _ φ2 hPA hPB sA sB hφ2s hφ2A hφ2c _ a' _ b' hEa hEb ha0 hb0
    (fun r => s.symm (ξ r) - ξ r - (p : Ω) ^ (c0 + 1) * ((A₁ * h - g * B₁ : ℤ) : Ω) * (t.val : Ω) * coefQ (p ^ L) f r)
    (min Cξ.order 0) (fun q => by
      refine sub_mem (sub_mem ((hsA _).1 (by rw [s.apply_symm_apply]; exact hξA q)) (hξA q))
        (mul_mem (mul_mem (mul_mem (pow_mem (natCast_mem A p) _) (intCast_mem A _)) (natCast_mem A _)) ?_)
      by_cases h0 : coefQ (p ^ L) f q = 0
      · rw [h0]; exact zero_mem A
      · obtain ⟨m, -, rfl⟩ := coefQ_supp p L hp.pos f q h0
        rw [hcusp.int, hjf]
        exact (ev_coeff hZ0 m).1) (fun q hq => by
      by_cases h1 : ξ q = 0
      · obtain ⟨m, hm, e1⟩ := coefQ_supp p L hp.pos f q (fun h0 => hq (by simp [h1, h0]))
        exact ⟨m, (min_le_right _ _).trans hm, e1⟩
      · obtain ⟨m, hm, e1⟩ := hξs q h1
        exact ⟨m, (min_le_left _ _).trans hm, e1⟩) _ _ _ hD (fun m => by
      have e1 : ∀ y, j (s.symm y) = g0⁻¹ (j y) := fun y => by
        conv_rhs => rw [← s.apply_symm_apply y, ← hg0j, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_sub, hCG, hCZ, map_sub, map_sub, e1, map_mul, hjf]
      refine Basic.cong_sub (Basic.cong_sub (Basic.cong_gal _ (hξc m)) (hξc m)) ?_
      simp only [map_mul, map_pow, map_natCast, map_intCast]
      push_cast
      exact Basic.cong_refl _ _) hval r
  have hdl : IsDl X A p n ((p : ℚ) ^ L) (e w) φ2 := by
    rw [← GlobalTheory.IoEx.castM]
    exact ⟨hφ2A, Aw, Bw, κ, hκ, hpres, hPA, hPB, hφ2c⟩
  obtain ⟨z1, hz1, e1⟩ := isDl_unique ε X hj p A hpA n _ _ φ φ2 hφ hdl r
  obtain ⟨z2, hz2, e2⟩ := hbr
  exact ⟨(p : Ω) ^ (c0 + 1) * z1 + z2, add_mem (mul_mem (pow_mem (natCast_mem A p) _) hz1) hz2, by
    linear_combination (p : Ω) ^ (c0 + 1) * e1 + e2⟩
end
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnit_edgeClass_kummer_dlog_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n N c d : ℕ) (A₁ a₂ g B₁ b₂ h : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → b₂ ≡ N * h [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → (N : ℤ) ∣ b₂ → 1 ≤ n → n ≤ L → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → 1 < d → Nat.Coprime d (6 * N * p) →
    ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ B₁) →
  ∀ (F K Ω' : Type) [Field F] [Field K] [Field Ω'] [Algebra F K] [Algebra F Ω'] [Algebra K Ω'] [IsScalarTower F K Ω'] [IsAlgClosure K Ω'] [Normal F K]
    (e : K →+* X.K), (∀ y, e y ∈ KT X (p ^ L)) →
  ∀ (z a b : K) (ζ α β : Ω'), e z = algebraMap Ω X.K (zt ε p n) → ζ = algebraMap K Ω' z →
    e a = sgN X c N (N * p ^ L) (A₁, a₂) → e b = sgN X d N (N * p ^ L) (B₁, b₂) →
    α ^ (p ^ n) = algebraMap K Ω' a → β ^ (p ^ n) = algebraMap K Ω' b →
  ∀ (x y : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod (p ^ n))), (∀ t, (x t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ α t) → (∀ t, (y t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ β t) →
  ∀ η : (Ω' ≃ₐ[F] Ω') → ZMod (p ^ n), GlobalTheory.KEdge.CobOn (GlobalTheory.K4.geo F K Ω') x y η → IsLocallyConstant (fun t : GlobalTheory.K4.geo F K Ω' => η t) →
  ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, Stab A s → s (zt ε p L) = zt ε p L → (∀ f : F, X.gal s (e (algebraMap F K f)) = e (algebraMap F K f)) →
    ∀ σ : Ω' ≃ₐ[F] Ω', (∀ k k' : K, e k' = X.gal s (e k) → σ (algebraMap K Ω' k) = algebraMap K Ω' k') →
    ∀ (w : K) (φ : HahnSeries ℚ Ω) (t : ZMod (p ^ n)), GlobalTheory.K4.IsTopW ζ x y η σ w → IsDl X A p n ((p : ℚ) ^ L) (e w) φ →
      s (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n) →
      ∀ r : ℚ, CgA A p n ((p : Ω) ^ cc * φ.coeff r)
        (s.symm (ξ r) - ξ r - (p : Ω) ^ cc * ((A₁ * h - g * B₁ : ℤ) : Ω) * (t.val : Ω) *
          coefQ (p ^ L) (cmul (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂) (smF d 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) B₁ b₂)) r) := by
  atlas_forward_decl GlobalTheory.pair_edge_dlog
end
