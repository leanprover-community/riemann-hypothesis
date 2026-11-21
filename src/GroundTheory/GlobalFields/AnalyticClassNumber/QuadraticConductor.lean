import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticLegendre
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke
import GroundTheory.GlobalFields.Artin.ConductorInduction
import GroundTheory.GlobalFields.Artin.ConductorOneDim

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology WithZero
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

section Norm

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem padicRingEquiv_uniformizer (v : HeightOneSpectrum (𝓞 ℚ)) :
    padicRingEquiv v (uniformizer v : v.adicCompletion ℚ) = (prime v : ℚ_[prime v]) := by
  rw [uniformizer, padicRingEquiv_finiteProj_diagonal, coe_primeRat]
  push_cast
  rfl

theorem mem_adicCompletionIntegers_iff_norm_le (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ ‖padicRingEquiv v x‖ ≤ 1 :=
  ⟨fun h ↦ (PadicInt.mem_subring_iff _).1
    ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h),
    mem_adicCompletionIntegers_of_norm_le v⟩

theorem valued_le_exp_neg_iff (x : v.adicCompletion ℚ) (n : ℕ) :
    Valued.v x ≤ exp (-(n : ℤ)) ↔ ‖padicRingEquiv v x‖ ≤ ((prime v : ℝ) ^ n)⁻¹ := by
  set u : v.adicCompletion ℚ := (uniformizer v : v.adicCompletion ℚ)
  have hval : Valued.v (x * (u ^ n)⁻¹) = Valued.v x * exp (n : ℤ) := by
    rw [map_mul, map_inv₀, map_pow, valued_uniformizer, ← exp_nsmul, ← exp_neg]
    congr 2
    simp
  have hnorm : ‖padicRingEquiv v (x * (u ^ n)⁻¹)‖ = ‖padicRingEquiv v x‖ * (prime v : ℝ) ^ n := by
    rw [map_mul, map_inv₀, map_pow, padicRingEquiv_uniformizer, norm_mul, norm_inv, norm_pow,
      Padic.norm_p, inv_pow, inv_inv]
  have h1 := mem_adicCompletionIntegers_iff_norm_le (x * (u ^ n)⁻¹)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, hnorm] at h1
  have hp : (0 : ℝ) < (prime v : ℝ) ^ n := by
    have := (Fact.out : (prime v).Prime).pos
    positivity
  have hexp : Valued.v x ≤ exp (-(n : ℤ)) ↔ Valued.v x * exp (n : ℤ) ≤ 1 := by
    have e : exp (-(n : ℤ)) * exp (n : ℤ) = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    constructor
    · intro h
      calc Valued.v x * exp (n : ℤ) ≤ exp (-(n : ℤ)) * exp (n : ℤ) := by gcongr
        _ = 1 := e
    · intro h
      calc Valued.v x = Valued.v x * exp (n : ℤ) * exp (-(n : ℤ)) := by
            rw [mul_assoc, mul_comm (exp _), e, mul_one]
        _ ≤ 1 * exp (-(n : ℤ)) := by gcongr
        _ = exp (-(n : ℤ)) := one_mul _
  rw [hexp, h1, inv_eq_one_div, le_div_iff₀ hp]

theorem mem_unitsLevel_iff (a : (v.adicCompletion ℚ)ˣ) (n : ℕ) :
    a ∈ unitsLevel v n ↔ ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 ∧
      ‖padicRingEquiv v (a : v.adicCompletion ℚ) - 1‖ ≤ ((prime v : ℝ) ^ n)⁻¹ := by
  rw [mem_unitsLevel, ← map_one (padicRingEquiv v), ← map_sub, ← valued_le_exp_neg_iff]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine norm_padicRingEquiv_eq_one ?_
    rw [← unitsLevel_zero, mem_unitsLevel]
    refine ⟨h, ?_⟩
    refine (Valuation.map_sub _ _ _).trans ?_
    rw [h, map_one, max_self]
    simp
  · have h0 := mem_units_of_norm_padicRingEquiv_eq_one h
    rw [← unitsLevel_zero, mem_unitsLevel] at h0
    exact h0.1

end Norm

section Padic

variable {p : ℕ} [Fact p.Prime]

theorem coe_units_inv (u : ℤ_[p]ˣ) :
    (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p])⁻¹ := by
  have e : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  exact eq_inv_of_mul_eq_one_left e

theorem norm_inv_sub_one {x : ℚ_[p]} (hx : ‖x‖ = 1) : ‖x⁻¹ - 1‖ = ‖x - 1‖ := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)
  rw [show x⁻¹ - 1 = x⁻¹ * (1 - x) by field_simp, norm_mul, norm_inv, hx, inv_one, one_mul,
    norm_sub_rev]

theorem toZModPow_eq_one_of_norm_le {u : ℤ_[p]} {k : ℕ}
    (h : ‖(u : ℚ_[p]) - 1‖ ≤ ((p : ℝ) ^ k)⁻¹) : PadicInt.toZModPow k u = 1 := by
  have hmem : u - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, zpow_neg, zpow_natCast]
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
    exact h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  exact hmem

end Padic

section Local

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem localComponent_heckeCharacter_eq_one (v : HeightOneSpectrum (𝓞 ℚ))
    {a : (v.adicCompletion ℚ)ˣ} (ha : a ∈ unitsLevel v (N.factorization (prime v))) :
    (heckeCharacter χ).localComponent v a = 1 := by
  rw [mem_unitsLevel_iff] at ha
  obtain ⟨ha1, ha2⟩ := ha
  rw [HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]
  refine Circle.ext ?_
  rw [Circle.coe_one, ← map_one χ]
  refine coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup ha1⟩
    fun w hw ↦ ?_
  rw [map_one]
  by_cases hwv : w = v
  · subst hwv
    have hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup ha1⟩ w : ℤ_[prime w]ˣ) :
        ℤ_[prime w]) : ℚ_[prime w]) = padicRingEquiv w (a : w.adicCompletion ℚ) := by
      rw [coe_unitAt]
      change padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _
      rw [finiteProj_finiteEmbedding]
    apply toZModPow_eq_one_of_norm_le
    rw [coe_units_inv, hu, norm_inv_sub_one ha1]
    exact ha2
  · rw [unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]

theorem coe_heckeCharacter_finiteEmbedding_inv_val {v : HeightOneSpectrum (𝓞 ℚ)} (hv : prime v ∣ N)
    (b : (ZMod N)ˣ) (hb : ZMod.unitsMap (Nat.ordCompl_dvd N (prime v)) b = 1)
    {a : (v.adicCompletion ℚ)ˣ}
    (ha : padicRingEquiv v (a : v.adicCompletion ℚ) = (((b : ZMod N).val : ℕ) : ℚ_[prime v])⁻¹) :
    ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 ∧
      (heckeCharacter χ (IdeleClassGroup.mk ℚ (finiteEmbedding v a)) : ℂ) = χ b := by
  set m : ℕ := (b : ZMod N).val with hm
  have hcop : (prime v).Coprime m :=
    (Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm
  have hnm : ‖(m : ℚ_[prime v])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hcop
  have hm0 : (m : ℚ_[prime v]) ≠ 0 := norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)
  have hnorm : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 := by
    rw [ha, norm_inv, hnm, inv_one]
  refine ⟨hnorm, coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩
    fun w hw ↦ ?_⟩
  by_cases hwv : w = v
  · subst hwv
    have hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩ w : ℤ_[prime w]ˣ) :
        ℤ_[prime w]) : ℚ_[prime w]) = (m : ℚ_[prime w])⁻¹ := by
      rw [coe_unitAt]
      change padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _
      rw [finiteProj_finiteEmbedding, ha]
    rw [coe_inv_eq_natCast hm0 hu, map_natCast]
    conv_rhs => rw [← ZMod.natCast_zmod_val (b : ZMod N), ← hm]
    rw [map_natCast]
  · rw [unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]
    have hcp : Nat.Coprime (prime w ^ N.factorization (prime w))
        (prime v ^ N.factorization (prime v)) :=
      Nat.Coprime.pow _ _ (coprime_prime hwv)
    have h1 : prime w ^ N.factorization (prime w) ∣
        prime v ^ N.factorization (prime v) * (N / prime v ^ N.factorization (prime v)) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
      exact Nat.ordProj_dvd _ _
    have hdvd := hcp.dvd_of_dvd_mul_left h1
    rw [← castHom_castHom hdvd (Nat.ordCompl_dvd N (prime v)) (Nat.ordProj_dvd N (prime w))]
    have hb' : ZMod.castHom (Nat.ordCompl_dvd N (prime v))
        (ZMod (N / prime v ^ N.factorization (prime v))) (b : ZMod N) = 1 := congrArg Units.val hb
    rw [hb', map_one]

theorem continuous_localComponent (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) :=
  ((heckeCharacter χ).localComponent v).continuous

theorem conductorExponent_localComponent_le (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponent v ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) ≤
      N.factorization (prime v) :=
  (unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ (continuous_localComponent χ v)).1
    fun _ ha ↦ localComponent_heckeCharacter_eq_one χ v ha

theorem le_conductorExponent_localComponent (hχ : χ.IsPrimitive) (v : HeightOneSpectrum (𝓞 ℚ)) :
    N.factorization (prime v) ≤
      conductorExponent v ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) := by
  set p := prime v with hp
  set k := N.factorization p with hk
  have hpp : p.Prime := Fact.out
  by_cases hv : p ∣ N
  swap
  · rw [hk, Nat.factorization_eq_zero_of_not_dvd hv]
    exact Nat.zero_le _
  have hk1 : 1 ≤ k := hpp.factorization_pos_of_dvd (NeZero.ne N) hv
  by_contra hlt
  push Not at hlt
  have hker : unitsLevel v (k - 1) ≤
      ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle).ker :=
    (unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ (continuous_localComponent χ v)).2 (by omega)
  have hdvd : N / p ∣ N := Nat.div_dvd_of_dvd hv
  have hpow : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk1]
  have he : N / p = p ^ (k - 1) * (N / p ^ k) := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N p]
    rw [← hk, hpow, mul_assoc, Nat.mul_div_cancel_left _ hpp.pos]
  have hpk : p ^ (k - 1) ∣ N / p := he ▸ dvd_mul_right _ _
  have hcompl : N / p ^ k ∣ N / p := he ▸ dvd_mul_left _ _
  have hf : χ.FactorsThrough (N / p) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).2 fun b hb ↦ ?_
    have hbN : ZMod.castHom hdvd (ZMod (N / p)) (b : ZMod N) = 1 := congrArg Units.val hb
    set m : ℕ := (b : ZMod N).val with hm
    have hcop : p.Coprime m :=
      (Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm
    have hnm : ‖(m : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hcop
    have hm0 : (m : ℚ_[p]) ≠ 0 := norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)
    have hmN : ((N / p : ℕ) : ℤ) ∣ (m : ℤ) - 1 := by
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub 1 m (N / p)).1 ?_
      rw [Int.cast_one, Int.cast_natCast, hm, ← map_natCast (ZMod.castHom hdvd (ZMod (N / p))),
        ZMod.natCast_zmod_val, hbN]
    have hb' : ZMod.unitsMap (Nat.ordCompl_dvd N p) b = 1 := by
      refine Units.ext ?_
      change ZMod.castHom (Nat.ordCompl_dvd N p) (ZMod (N / p ^ k)) (b : ZMod N) = 1
      rw [← ZMod.natCast_zmod_val (b : ZMod N), map_natCast, ← hm]
      have h := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (m : ℤ) (N / p ^ k)).2
        ((Int.natCast_dvd_natCast.2 hcompl).trans hmN)
      rw [Int.cast_one, Int.cast_natCast] at h
      exact h.symm
    have hmp : ((p : ℤ) ^ (k - 1)) ∣ (m : ℤ) - 1 :=
      (Int.natCast_dvd_natCast.2 hpk).trans (by exact_mod_cast hmN)
    have hnorm1 : ‖(m : ℚ_[p]) - 1‖ ≤ ((p : ℝ) ^ (k - 1))⁻¹ := by
      have h := (Padic.norm_int_le_pow_iff_dvd ((m : ℤ) - 1) (k - 1)).2 hmp
      rw [zpow_neg, zpow_natCast] at h
      exact_mod_cast h
    let a : (v.adicCompletion ℚ)ˣ :=
      Units.map (padicRingEquiv v).symm.toMonoidHom (Units.mk0 (m : ℚ_[p]) hm0)⁻¹
    have ha : padicRingEquiv v (a : v.adicCompletion ℚ) = (m : ℚ_[p])⁻¹ := by
      simp only [a, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact RingEquiv.apply_symm_apply _ _
    obtain ⟨-, hval⟩ := coe_heckeCharacter_finiteEmbedding_inv_val χ hv b hb' ha
    have hmem : a ∈ unitsLevel v (k - 1) := by
      rw [mem_unitsLevel_iff, ha, norm_inv, hnm, inv_one, norm_inv_sub_one hnm]
      exact ⟨rfl, hnorm1⟩
    have h1 : (heckeCharacter χ).localComponent v a = 1 := hker hmem
    rw [HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply] at h1
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, ← hval, h1,
      Circle.coe_one]
  have hc := χ.conductor_dvd_of_mem_conductorSet hf
  rw [hχ] at hc
  have hle := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hv) hpp.pos) hc
  have hlt' := Nat.div_lt_self (Nat.pos_of_neZero N) hpp.one_lt
  omega

theorem conductorExponent_localComponent_heckeCharacter (hχ : χ.IsPrimitive)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponent v ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) =
      N.factorization (prime v) :=
  le_antisymm (conductorExponent_localComponent_le χ v) (le_conductorExponent_localComponent χ hχ v)

theorem conductorExponentAt_heckeCharacter (hχ : χ.IsPrimitive) (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponentAt ((heckeCharacter χ).toIdele.comp ofFinite) v = N.factorization (prime v) := by
  have h : ((heckeCharacter χ).toIdele.comp ofFinite).comp (finiteUnitsSingle v) =
      ((heckeCharacter χ).localComponent v : (v.adicCompletion ℚ)ˣ →* Circle) := by
    ext a
    simp only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]
    rfl
  rw [conductorExponentAt, h, conductorExponent_localComponent_heckeCharacter χ hχ]

end Local

theorem asIdeal_pow_dvd_span_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n m : ℕ) :
    v.asIdeal ^ n ∣ Ideal.span {(m : 𝓞 ℚ)} ↔ prime v ^ n ∣ m := by
  rw [asIdeal_eq_span, Ideal.span_singleton_pow, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_span_singleton, ← Nat.cast_pow, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast,
    Int.natCast_dvd_natCast]

theorem span_natCast_dvd_span_iff (m n : ℕ) :
    Ideal.span {(m : 𝓞 ℚ)} ∣ Ideal.span {(n : 𝓞 ℚ)} ↔ m ∣ n := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv,
    map_natCast, map_natCast, Int.natCast_dvd_natCast]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem conductor_heckeCharacter (hχ : χ.IsPrimitive) :
    (heckeCharacter χ).conductor = Ideal.span {(N : 𝓞 ℚ)} := by
  have hcont : Continuous ((heckeCharacter χ).toIdele.comp ofFinite) :=
    (heckeCharacter χ).continuous_toIdele.comp continuous_ofFinite
  have hfun : conductorExponentAt ((heckeCharacter χ).toIdele.comp ofFinite) =
      fun v ↦ N.factorization (prime v) :=
    funext (conductorExponentAt_heckeCharacter χ hχ)
  have hsupp : (Function.support fun v : HeightOneSpectrum (𝓞 ℚ) ↦ N.factorization (prime v)).Finite := by
    rw [← hfun]
    exact finite_support_conductorExponentAt Circle.noSmallSubgroups _ hcont
  have hcond : (heckeCharacter χ).conductor =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ^ N.factorization (prime v) := by
    rw [HeckeCharacter.conductor, IdeleGroup.conductor, hfun]
  obtain ⟨m, hm⟩ := exists_eq_span_natCast (heckeCharacter χ).conductor
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply (heckeCharacter χ).conductor_ne_bot
    rw [hm, Nat.cast_zero, Ideal.span_singleton_eq_bot]
  have hN0 : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact NeZero.ne N

  have hle := (finprod_asIdeal_pow_dvd_iff hsupp (heckeCharacter χ).conductor_ne_bot).1
    (hcond ▸ dvd_rfl)
  have hNm : N ∣ m := by
    refine (Nat.factorization_le_iff_dvd (NeZero.ne N) hm0).1 fun q ↦ ?_
    by_cases hq : q.Prime
    · have hv := prime_placeOf (⟨q, hq⟩ : Nat.Primes)
      have h1 := pow_dvd_of_le_multiplicity (hle (placeOf ⟨q, hq⟩))
      rw [hm, asIdeal_pow_dvd_span_iff, hv] at h1
      exact (hq.pow_dvd_iff_le_factorization hm0).1 h1
    · rw [Nat.factorization_eq_zero_of_not_prime N hq]
      exact Nat.zero_le _

  have hdvd : (heckeCharacter χ).conductor ∣ Ideal.span {(N : 𝓞 ℚ)} := by
    rw [hcond]
    refine (finprod_asIdeal_pow_dvd_iff hsupp hN0).2 fun v ↦ ?_
    refine (FiniteMultiplicity.of_prime_left (HeightOneSpectrum.prime v) hN0).le_multiplicity_of_pow_dvd ?_
    rw [asIdeal_pow_dvd_span_iff]
    exact Nat.ordProj_dvd N (prime v)
  rw [hm, span_natCast_dvd_span_iff] at hdvd
  rw [hm, Nat.dvd_antisymm hdvd hNm]

theorem absNorm_conductor_heckeCharacter (hχ : χ.IsPrimitive) :
    Ideal.absNorm (heckeCharacter χ).conductor = N := by
  rw [conductor_heckeCharacter χ hχ, absNorm_span_natCast]

end DirichletHecke

end

end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open Complex HurwitzZeta Filter Topology Set

namespace GroundTheory.Global.Quadratic




def hurwitzCombTerm (x : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n : ℝ) + x : ℝ) : ℂ) ^ (-s) + ((1 - 2 * x : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) +
    ((2 * x - 2 : ℝ) : ℂ) * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s)

def hurwitzComb (x : ℝ) (s : ℂ) : ℂ :=
  hurwitzZeta x s + ((1 - 2 * x : ℝ) : ℂ) * hurwitzZeta (1 : ℝ) s +
    ((2 * x - 2 : ℝ) : ℂ) * hurwitzZeta (1 / 2 : ℝ) s












end Quadratic

end GroundTheory.Global
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Module GroundTheory.LocalField NumberField.InfinitePlace NumberField.Units
open scoped Real

namespace GroundTheory.Global

section Congr

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem artinExponent_congr_character {ρ : Representation ℂ Gal(L/K) V}
    {ρ' : Representation ℂ Gal(L/K) W} (h : ρ.character = ρ'.character)
    (v : HeightOneSpectrum (𝓞 K)) : artinExponent v ρ = artinExponent v ρ' := by
  apply Nat.cast_injective (R := ℂ)
  rw [natCast_artinExponent v ρ (placeAbove v), natCast_artinExponent v ρ' (placeAbove v), h]

theorem artinConductorIdeal_congr_character {ρ : Representation ℂ Gal(L/K) V}
    {ρ' : Representation ℂ Gal(L/K) W} (h : ρ.character = ρ'.character) :
    artinConductorIdeal ρ = artinConductorIdeal ρ' :=
  finprod_congr fun v ↦ by rw [artinExponent_congr_character h v]

end Congr

namespace Quadratic

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem character_ind_trivial :
    ((Representation.trivial ℂ Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ).ind
      (AlgEquiv.restrictScalarsHom ℚ)).character =
      ((Representation.trivial ℂ Gal(K/ℚ) ℂ).prod (charRep (galChar K))).character := by
  classical
  have := Fintype.ofFinite Gal(K/ℚ)
  have := Fintype.ofFinite Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ)))
  have hH : Nat.card Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, IntermediateField.finrank_fixedField_eq_card,
      Subgroup.card_bot]
  have hsub : ∀ h : Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))), h = 1 :=
    fun h ↦ (Nat.card_eq_one_iff_unique.1 hH).1.elim h 1
  funext g
  rw [character_ind, indFun_apply, character_prod, character_charRep, hH]
  simp only [Nat.cast_one, inv_one, one_mul]
  have htriv : ∀ h, (Representation.trivial ℂ
      Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ).character h = 1 := fun h ↦ by
    simp [Representation.character]
  have htriv' : (Representation.trivial ℂ Gal(K/ℚ) ℂ).character g = 1 := by
    simp [Representation.character]
  rw [htriv']
  have hinner : ∀ t : Gal(K/ℚ), (∑ h : Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))),
      if (AlgEquiv.restrictScalarsHom ℚ) h = t⁻¹ * g * t then
        (Representation.trivial ℂ _ ℂ).character h else 0) = if g = 1 then 1 else 0 := fun t ↦ by
    rw [Fintype.sum_eq_single 1 (fun h hh ↦ absurd (hsub h) hh), map_one, htriv]
    by_cases hg : g = 1
    · simp [hg]
    · rw [if_neg hg, if_neg]
      intro h1
      apply hg
      have : t * (t⁻¹ * g * t) * t⁻¹ = g := by group
      rw [← this, ← h1]
      group
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, card_gal]
  by_cases hg : g = 1
  · subst hg
    rw [if_pos rfl, galChar_one_apply]
    norm_num
  · rw [if_neg hg, galChar_apply_of_ne_one K hg]
    norm_num

theorem artinConductorIdeal_galChar :
    artinConductorIdeal (charRep (galChar K)) =
      relDiscr ℚ (IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) := by
  have h1 := artinConductorIdeal_ind (K := ℚ) (L := K) ⊥
    (Representation.trivial ℂ Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ)
  rw [artinConductorIdeal_eq_top_of_forall_eq_one
      (Representation.trivial ℂ Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ)
      (fun _ ↦ rfl), Module.finrank_self, pow_one,
    ← Ideal.one_eq_top, map_one, mul_one] at h1
  have h2 := artinConductorIdeal_congr_character (character_ind_trivial K)
  rw [artinConductorIdeal_prod, artinConductorIdeal_eq_top_of_forall_eq_one
      (Representation.trivial ℂ Gal(K/ℚ) ℂ) (fun _ ↦ rfl), ← Ideal.one_eq_top, one_mul] at h2
  exact h2.symm.trans h1

theorem absNorm_artinConductorIdeal_galChar :
    Ideal.absNorm (artinConductorIdeal (charRep (galChar K))) = (discr K).natAbs := by
  rw [artinConductorIdeal_galChar, absNorm_relDiscr_rat, discr_eq_discr_of_algEquiv _
    ((IntermediateField.equivOfEq (IntermediateField.fixedField_bot (F := ℚ) (E := K))).trans
      IntermediateField.topEquiv)]

theorem level_eq : level K = (discr K).natAbs := by
  have h1 := DirichletHecke.absNorm_conductor_heckeCharacter (kronecker K) (isPrimitive_kronecker K)
  rw [← heckeCharacterOfChar_galChar, ← artinConductorIdeal_charRep_eq_conductor,
    absNorm_artinConductorIdeal_galChar] at h1
  exact h1.symm

section Transport

variable {N M : ℕ} (h : N = M) (χ : DirichletCharacter ℂ N)

theorem changeLevel_of_eq_apply (n : ℕ) : DirichletCharacter.changeLevel (dvd_of_eq h) χ n = χ n := by
  subst h
  rw [DirichletCharacter.changeLevel_self]


theorem LFunction_changeLevel_of_eq [NeZero N] [NeZero M] (s : ℂ) :
    DirichletCharacter.LFunction (DirichletCharacter.changeLevel (dvd_of_eq h) χ) s =
      DirichletCharacter.LFunction χ s := by
  subst h
  rw [DirichletCharacter.changeLevel_self]



end Transport

instance : NeZero (discr K).natAbs :=
  ⟨Int.natAbs_ne_zero.2 (discr_ne_zero K)⟩

def kroneckerChar : DirichletCharacter ℂ (discr K).natAbs :=
  DirichletCharacter.changeLevel (dvd_of_eq (level_eq K)) (kronecker K)




theorem kroneckerChar_apply (n : ℕ) : kroneckerChar K n = kronecker K n :=
  changeLevel_of_eq_apply (level_eq K) _ n

theorem LFunction_kroneckerChar (s : ℂ) :
    DirichletCharacter.LFunction (kroneckerChar K) s = DirichletCharacter.LFunction (kronecker K) s :=
  LFunction_changeLevel_of_eq (level_eq K) _ s


theorem kroneckerChar_apply_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    kroneckerChar K p = (legendreSym p (discr K) : ℂ) := by
  rw [kroneckerChar_apply, kronecker_apply_prime K p hp]





end Quadratic

end GroundTheory.Global
end
end
