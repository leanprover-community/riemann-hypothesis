import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.ProdNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.IntCrit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfTwoHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetShalikaRigidityHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPlaceCompletionIsoImports
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IntK
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports

section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem locK_level (κ : HChar E) (v : HeightOneSpectrum (𝓞 E)) :
    ∃ n : ℕ, ∀ y : Eˣ, v.valuation E ((y : E) - 1) ≤ WithZero.exp (-(n : ℤ)) → κ.locK v y = 1 := by
  obtain ⟨-, hlev, -⟩ := GlobalTheory.HeckeSplit.continuous_char_factor E κ.1 κ.2.1
  obtain ⟨n, hn⟩ := hlev v
  refine ⟨n, fun y hy => hn (atFin v y) ?_⟩
  have e : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
      algebraMap E (v.adicCompletion E) ((y : E) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [e]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).le.trans hy

private theorem pow_congr_one (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 E, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal ^ (n + 1) := by
  set J := v.asIdeal ^ (n + 1) with hJ
  have hfin : Finite (𝓞 E ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  refine ⟨Nat.card (𝓞 E ⧸ J)ˣ, Nat.card_pos, fun r hr => ?_⟩
  obtain ⟨y, i, hi, e⟩ := v.isMaximal.exists_inv hr
  have hunit : IsUnit (Ideal.Quotient.mk J r) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (y * ∑ j ∈ Finset.range (n + 1), i ^ j)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    have hg := mul_neg_geom_sum i (n + 1)
    have hyr : y * r = 1 - i := by linear_combination e
    have hval : r * (y * ∑ j ∈ Finset.range (n + 1), i ^ j) - 1 = -(i ^ (n + 1)) := by
      calc r * (y * ∑ j ∈ Finset.range (n + 1), i ^ j) - 1
          = (y * r) * (∑ j ∈ Finset.range (n + 1), i ^ j) - 1 := by ring
        _ = -(i ^ (n + 1)) := by rw [hyr, hg]; ring
    rw [hval]
    exact neg_mem (Ideal.pow_mem_pow hi _)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := hunit.unit))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h1

private theorem locK_finite_order (κ : HChar E) (v : HeightOneSpectrum (𝓞 E)) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Eˣ, v.valuation E (u : E) = 1 → κ.locK v u ^ m = 1 := by
  obtain ⟨n, hn⟩ := locK_level κ v
  obtain ⟨m, hm, H⟩ := pow_congr_one v n
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := (GlobalTheory.UnramCompletion.intAt_iff v (u : E)).2 hu.le
  have hs1 : v.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hr1 : v.valuation E (algebraMap (𝓞 E) E r) = 1 := by
    rw [← hrs, map_mul, hs1, hu, one_mul]
  have hr : r ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).1 hr1
  have hmem : r ^ m - s ^ m ∈ v.asIdeal ^ (n + 1) := by
    simpa using (v.asIdeal ^ (n + 1)).sub_mem (H r hr) (H s hs)
  have hle : v.valuation E (algebraMap (𝓞 E) E (r ^ m - s ^ m)) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem _ _).2 hmem
  have e : algebraMap (𝓞 E) E (r ^ m - s ^ m) = algebraMap (𝓞 E) E s ^ m * (((u ^ m : Eˣ) : E) - 1) := by
    rw [map_sub, map_pow, map_pow, ← hrs, Units.val_pow_eq_pow_val]
    ring
  rw [e, map_mul, map_pow, hs1, one_pow, one_mul] at hle
  rw [← map_pow]
  refine hn _ (hle.trans ?_)
  rw [WithZero.exp_le_exp]
  push_cast
  omega

private theorem isUnitAt_atFin (v : HeightOneSpectrum (𝓞 E)) (y : Eˣ) (hy : v.valuation E (y : E) = 1) :
    IsUnitAt v (atFin v y) :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (y : E)).trans hy

end SlopeTestRemainingChoices

section Nu

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private noncomputable def nuHom : ℂ →*₀ ℝ where
  toFun := nu ι
  map_zero' := by simp [nu]
  map_one' := by simp [nu]
  map_mul' x y := by simp [nu]

private theorem nuHom_apply (x : ℂ) : nuHom ι x = nu ι x := rfl

private theorem nu_eq_one {E : Type} [Field E] [NumberField E] {φ : E →+* ℂ}
    {u : HeightOneSpectrum (𝓞 E)} {ψ : u.adicCompletion E →+* ℂ}
    (hψ : ∀ x : E, ψ (algebraMap E _ x) = φ x) (hb : ∀ x, nu ι (ψ x) ≤ 1 ↔ Valued.v x ≤ 1)
    (y : Eˣ) (hy : u.valuation E (y : E) = 1) : nu ι (φ (y : E)) = 1 := by
  have hle : ∀ t : Eˣ, u.valuation E (t : E) = 1 → nu ι (φ (t : E)) ≤ 1 := fun t ht => by
    rw [← hψ]
    exact (hb _).2 (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u (t : E) ▸ ht.le)
  have h1 := hle y hy
  have h2 := hle y⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  have h3 : nu ι (φ (y : E)) * nu ι (φ ((y⁻¹ : Eˣ) : E)) = 1 := by
    rw [← nuHom_apply, ← nuHom_apply, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h4 : 0 ≤ nu ι (φ (y : E)) := norm_nonneg _
  nlinarith

end Nu

end UpperTheory.V.Z.Int

theorem UpperTheory.V.Z.Int.charVal :
    UpperTheory.V.Z.Int.CharVal := by
  intro l _ ι E _ _ _ κ m hκ w hw

  obtain ⟨h, a, hh, haw, hav⟩ := GlobalTheory.TamePow.exists_gen w
  choose o ho hou using fun v => locK_finite_order κ v
  have hfinS := Filter.eventually_cofinite.mp (Formalism.L2.Fam.IdTrans.unrAe κ)
  set S := hfinS.toFinset with hS
  set M := ∏ v ∈ S, o v with hM
  have hMpos : 0 < M := Finset.prod_pos fun v _ => ho v
  set N := h * M with hN
  have hNpos : 0 < N := Nat.mul_pos hh hMpos
  set z : Eˣ := a ^ M with hz

  have hzv : ∀ v, v ≠ w → v.valuation E (z : E) = 1 := fun v hv => by
    rw [hz, Units.val_pow_eq_pow_val, map_pow, hav v hv, one_pow]
  have hunif : w.valuation E ((unif w : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans (unif_spec w)
  set y : Eˣ := z / unif w ^ N with hy
  have hyw : w.valuation E (y : E) = 1 := by
    rw [hy, Units.val_div_eq_div_val, map_div₀, hz, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      map_pow, map_pow, haw, hunif, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, hN]
    rw [div_eq_one_iff_eq (by simp)]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hzy : z = y * unif w ^ N := by rw [hy, div_mul_cancel]

  have hloc : ∀ v, v ≠ w → κ.locK v z = 1 := fun v hv => by
    by_cases hvS : v ∈ S
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem o hvS
      have hva : v.valuation E (a : E) = 1 := hav v hv
      rw [hz, map_pow, hM, hc, pow_mul, hou v a hva, one_pow]
    · have hU : κ.UnrAt v := by
        by_contra hn
        exact hvS (by rw [hS, Set.Finite.mem_toFinset]; exact hn)
      exact hU _ (isUnitAt_atFin v z (hzv v hv))
  have hlocw : κ.locK w z = κ.val w ^ N := by
    have e : κ.locK w y = 1 := hw _ (isUnitAt_atFin w y hyw)
    rw [hzy, map_mul, map_pow, e, one_mul]
    rfl
  obtain ⟨-, hp⟩ := GlobalTheory.HCharUnit.finprod_locK_mul_inf E κ z
  rw [finprod_eq_single _ w fun v hv => hloc v hv, hlocw] at hp
  have hC : (κ.val w : ℂ) ^ N * ∏ φ : E →+* ℂ, φ (z : E) ^ m φ = 1 := by
    have := congrArg Units.val hp
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hκ z, Units.val_one] at this
    exact this

  have hterm : ∀ φ : E →+* ℂ, nu ι (φ (z : E)) ^ m φ =
      if φ ∈ Ov ι w then (nu ι (φ ((unif w : Eˣ) : E)) ^ m φ) ^ N else 1 := fun φ => by
    obtain ⟨u, ψ, hψ, hb, hOv⟩ := placeHom l ι E φ
    split_ifs with hφ
    · have hu : w = u := (hOv w).1 hφ
      subst hu
      have h1 := nu_eq_one ι hψ hb y hyw
      have h2 : nu ι (φ (z : E)) = nu ι (φ ((unif w : Eˣ) : E)) ^ N := by
        rw [hzy, ← nuHom_apply, Units.val_mul, map_mul, map_mul, nuHom_apply, h1, one_mul,
          Units.val_pow_eq_pow_val, map_pow, map_pow, nuHom_apply]
      rw [h2, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    · have hu : u ≠ w := fun e => hφ ((hOv w).2 e.symm)
      rw [nu_eq_one ι hψ hb z (hzv u hu), _root_.one_zpow]
  have hR : (nu ι (κ.val w : ℂ) * ∏ τ ∈ Ov ι w, nu ι (τ ((unif w : Eˣ) : E)) ^ m τ) ^ N = 1 := by
    have h1 := congrArg (nuHom ι) hC
    rw [map_mul, map_pow, map_prod, map_one] at h1
    simp only [map_zpow₀, nuHom_apply] at h1
    rw [Finset.prod_congr rfl fun φ _ => hterm φ, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_pow] at h1
    rw [mul_pow]
    exact h1
  have hnn : 0 ≤ nu ι (κ.val w : ℂ) * ∏ τ ∈ Ov ι w, nu ι (τ ((unif w : Eˣ) : E)) ^ m τ :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _)
  exact (pow_eq_one_iff_of_nonneg hnn hNpos.ne').1 hR
end

section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

private theorem nu_mul {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x y : ℂ) :
    nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu, map_mul, norm_mul]

private theorem nu_inv {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x : ℂ) :
    nu ι x⁻¹ = (nu ι x)⁻¹ := by
  simp [nu, map_inv₀, norm_inv]

private theorem algSat_map (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem prod_zpow_add {α : Type} (s : Finset α) (p : α → ℝ) (hp : ∀ t ∈ s, 0 < p t) (a c : α → ℤ) :
    ∏ t ∈ s, p t ^ (a t + c t) = (∏ t ∈ s, p t ^ a t) * ∏ t ∈ s, p t ^ c t := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t ht => zpow_add₀ (hp t ht).ne' _ _

private theorem prod_zpow_neg {α : Type} (s : Finset α) (p : α → ℝ) (a : α → ℤ) :
    ∏ t ∈ s, p t ^ (-a t) = (∏ t ∈ s, p t ^ a t)⁻¹ := by
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun t _ => zpow_neg _ _

private theorem bnd_untwist {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (hp : ∀ τ ∈ Ov ι w, 0 < nu ι (τ (unif w : E)))
    (m lo hi : (E →+* ℂ) → ℤ) (e b : ℂ)
    (he : nu ι e * ∏ τ ∈ Ov ι w, nu ι (τ (unif w : E)) ^ m τ = 1)
    (h1 : Bnd ι w (fun τ => hi τ + m τ) (b * e))
    (h2 : Bnd ι w (fun τ => -(lo τ + m τ)) (b * e)⁻¹) :
    Bnd ι w hi b ∧ Bnd ι w (fun τ => -lo τ) b⁻¹ := by
  unfold Bnd at *
  set p : (E →+* ℂ) → ℝ := fun τ => nu ι (τ (unif w : E)) with hpdef
  set M := ∏ τ ∈ Ov ι w, p τ ^ m τ with hM
  constructor
  · rw [prod_zpow_add _ p hp hi m, nu_mul] at h1
    calc _ = nu ι b * (∏ τ ∈ Ov ι w, p τ ^ hi τ) * (nu ι e * M) := by rw [he, mul_one]
      _ = _ := by ring
      _ ≤ 1 := h1
  · have e1 : ∏ τ ∈ Ov ι w, p τ ^ (-(lo τ + m τ)) = (∏ τ ∈ Ov ι w, p τ ^ (-lo τ)) * M⁻¹ := by
      rw [prod_zpow_neg, prod_zpow_add _ p hp lo m, mul_inv, ← prod_zpow_neg]
    rw [e1] at h2
    have e2 : (nu ι e)⁻¹ * M⁻¹ = 1 := by rw [← mul_inv, he, inv_one]
    calc _ = nu ι b⁻¹ * (∏ τ ∈ Ov ι w, p τ ^ (-lo τ)) * ((nu ι e)⁻¹ * M⁻¹) := by rw [e2, mul_one]
      _ = nu ι (b * e)⁻¹ * ((∏ τ ∈ Ov ι w, p τ ^ (-lo τ)) * M⁻¹) := by
        rw [nu_inv, nu_inv, nu_mul, mul_inv]; ring
      _ ≤ 1 := h2

end UpperTheory.V.Z.Int

theorem UpperTheory.V.Z.Int.slopeGood :
    UpperTheory.V.Z.Int.SlopeOn .csd → UpperTheory.V.Z.Int.SlopeOn .good := by
  intro hC l _ ι E _ _ _ l' n hl' hn π χ hS w hw B hB lo hi hW b hb
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified GlobalTheory.automorphicFormsFiniteGL E l' n hn π χ hS w hw
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E n π κ w B hu hB
  have hinf : ∀ τ, (CG.mk (π.twist κ)).infChar τ = ((CG.mk π).infChar τ).map (· + (m τ : ℂ)) := by
    intro τ
    rw [← (GlobalTheory.CuspRep.InfType.expo_of_infType E κ).1 m hκ τ]
    exact ((GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) _).twist κ).infChar_eq
  have hW' : ∀ τ, Within n ((CG.mk (π.twist κ)).infChar τ) (lo τ + m τ) (hi τ + m τ) := by
    intro τ z hz
    rw [hinf, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨k, rfl, h1, h2⟩ := hW τ y hy
    exact ⟨k + m τ, by push_cast; ring, by omega, by omega⟩
  have hb' : b * (κ.val w : ℂ) ∈ algSat n (normV w) (B.map (· * κ.val w)) := by
    rw [algSat_map] at hb ⊢
    rw [Multiset.mem_map] at hb
    obtain ⟨α, hα, rfl⟩ := hb
    rw [Multiset.map_map, Multiset.mem_map]
    exact ⟨α, hα, by simp [mul_assoc]⟩
  obtain ⟨h1, h2⟩ := hC l ι E l' n hl' hn (π.twist κ) _ hS' w hw _ hB' _ _ hW' _ hb'
  exact bnd_untwist ι w (fun τ hτ => ((prodNorm l ι E w).1 τ hτ).1) m lo hi _ b
    (charVal l ι E κ m hκ w hu) h1 h2
end

section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

open scoped WithZero

namespace UpperTheory.V.Z.Int

private theorem pow_tendsto {A : Type} [Field A] [Valued A ℤᵐ⁰] {x : A} (h : Valued.v x < 1) :
    Filter.Tendsto (fun k : ℕ => x ^ k) Filter.atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero A ℤᵐ⁰).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h (Units.mk0 _ h0)
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact (pow_le_pow_right_of_le_one' h.le hk).trans_lt hN

private theorem map_lt_one {A C : Type} [Field A] [Field C] [Valued A ℤᵐ⁰] [Valued C ℤᵐ⁰] (i : A ≃+* C)
    (hi : Continuous i) {x : A} (h : Valued.v x < 1) : Valued.v (i x) < 1 := by
  have h1 : Filter.Tendsto (fun k : ℕ => (i x) ^ k) Filter.atTop (nhds 0) := by
    have h2 := (hi.tendsto 0).comp (pow_tendsto h)
    simpa [Function.comp_def] using h2
  have h3 := (Valued.hasBasis_nhds_zero C ℤᵐ⁰).mem_of_mem (i := 1) trivial
  obtain ⟨k, hk⟩ := (h1.eventually h3).exists
  by_contra hc
  have h4 : Valued.v ((i x) ^ k) < 1 := by
    have h5 := hk
    rw [Valuation.restrict_lt_iff_lt_embedding] at h5
    simpa using h5
  rw [map_pow] at h4
  exact absurd h4 (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

private theorem le_one_of_map {A C : Type} [Field A] [Field C] [Valued A ℤᵐ⁰] [Valued C ℤᵐ⁰] (i : A ≃+* C)
    (hi : Continuous i) {x : A} (h : Valued.v (i x) ≤ 1) : Valued.v x ≤ 1 := by
  by_contra hc
  have hc' := not_le.1 hc
  have h0 : x ≠ 0 := fun e => by simp [e] at hc'
  have h1 : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hc'
  have h2 := map_lt_one i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h3 : Valued.v (i x) ≠ 0 := by simpa using h0
  exact absurd h2 (not_lt.2 ((one_le_inv₀ (zero_lt_iff.2 h3)).2 h))



private theorem normV_eq_of_iso {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) [hl : w.asIdeal.LiesOver v.asIdeal]
    (i : v.adicCompletion F ≃+* w.adicCompletion K) (hi : Continuous i)
    (hloc : ∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x)) : normV w = normV v := by
  open GroundTheory.Global.SemiLocal in
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hp0 : algebraMap (𝓞 F) (v.adicCompletion F) a ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    simpa using ha0
  have hp := (valued_algebraMap_int_lt_one_iff v a).2 ha
  have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [hl.over]
  let g := Ideal.quotientMap w.asIdeal (algebraMap (𝓞 F) (𝓞 K)) hle
  letI := Ideal.Quotient.field v.asIdeal
  have hinj : Function.Injective g := g.injective
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have e1 : Valued.v (i (i.symm (algebraMap (𝓞 K) (w.adicCompletion K) y))) ≤ 1 := by
      simpa using valued_algebraMap_int_le_one w y
    obtain ⟨r, hr⟩ := exists_int_valued_sub_lt_one v _ (le_one_of_map i hi e1)
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    have e2 := map_lt_one i hi hr
    rw [map_sub, RingEquiv.apply_symm_apply, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), hloc] at e2
    have e3 : algebraMap K (w.adicCompletion K) (algebraMap F K (r : F)) =
        algebraMap (𝓞 K) (w.adicCompletion K) (algebraMap (𝓞 F) (𝓞 K) r) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K (w.adicCompletion K)]
      rfl
    rw [e3, ← map_sub, valued_algebraMap_int_lt_one_iff] at e2
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 e2).symm
  exact (Nat.card_eq_of_bijective g ⟨hinj, hsurj⟩).symm

private theorem slopesIn_of_slope {K : Type} [Field K] [NumberField K] {n : ℕ} (m : Fin n → ℤ)
    (u : HeightOneSpectrum (𝓞 K)) (inf : (K →+* ℂ) → Multiset ℂ) (hinf : ∀ τ, inf τ = infOf m)
    (B : Multiset ℂˣ) (h : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), Slope ι n u inf B) :
    SlopesIn (normV u) m (algSat n (normV u) B) := by
  have hW : ∀ lo hi : ℤ, (∀ i, lo ≤ m i ∧ m i ≤ hi) → ∀ τ, Within n (inf τ) lo hi := by
    intro lo hi hb τ z hz
    rw [hinf] at hz
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, rfl, (hb i).1, (hb i).2⟩
  obtain ⟨c, hc⟩ := (Set.finite_range m).bddBelow
  obtain ⟨d, hd⟩ := (Set.finite_range m).bddAbove
  have hp : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℤ),
      ∏ τ ∈ Ov ι u, nu ι (τ (unif u : K)) ^ a = nu ι (normV u : ℂ) ^ a := by
    intro l _ ι a
    rw [Finset.prod_zpow, (prodNorm l ι K u).2]
  intro b hb
  refine ⟨fun a ha => UpperTheory.V.Lib.isIntegral_of_norm_le _ fun l _ ι => ?_,
    fun a ha => UpperTheory.V.Lib.isIntegral_of_norm_le _ fun l _ ι => ?_⟩
  · have h1 := (h l ι (fun _ => -a) (fun _ => d)
      (fun τ => hW (-a) d (fun i => ⟨ha i, hd ⟨i, rfl⟩⟩) τ) b hb).2
    unfold Bnd at h1
    simp only [neg_neg] at h1
    rw [hp] at h1
    simpa [nu, mul_comm] using h1
  · have h1 := (h l ι (fun _ => c) (fun _ => a)
      (fun τ => hW c a (fun i => ⟨hc ⟨i, rfl⟩, ha i⟩) τ) b hb).1
    unfold Bnd at h1
    rw [hp] at h1
    simpa [nu, mul_comm] using h1

end UpperTheory.V.Z.Int

theorem UpperTheory.V.Z.Int.slopeAllOf :
    GlobalTheory.GalCut.QuadLift → UpperTheory.V.Z.Int.SlopeOn .good → UpperTheory.V.Z.Int.SlopeAll := by
  intro hQL hS E _ _ _ n hn m hm π hinf ⟨χ, hpol⟩ w B hB
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  have hJS := GlobalTheory.JSW.jacquetShalikaRigidity_holds
  have hGK := GlobalTheory.GelfandKazhdanTop.gelfandKazhdanDual_of_jacquetShalika (PositivityTheory.JacquetShalikaLocal.jacquetShalika_of hJS) hAF
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := (GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split hAF E (AlgebraicClosure E) 2 n π w).nonempty
  obtain ⟨P, hP⟩ := hQL E Q.K Q.two n hn π hQ3
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight hAF hJS hGK E Q.K 2 n hn π χ P hP ⟨hreg, hpol, trivial⟩
  have hin : GlobalTheory.GalCut.InScope .good 2 P χ' := ⟨hχ'.1, hχ'.2.1, hQ4 P hP⟩
  have hA := ReciprocityTheory.Gal.isPlaceOver_placeOf (AlgebraicClosure E) w
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso E (AlgebraicClosure E) Q.K w _ hA (hQ1 _ hA)
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  have hlo := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
  have hq := normV_eq_of_iso w w' i hi.cont hi.loc
  have hsat : (CG.mk P).HasSat w' B := by
    have h1 := hP.sat w' 1 B (by rw [hund, pow_one, hq]) (by rw [hund]; exact hB)
    simpa using h1
  have hinf' : ∀ τ, (CG.mk P).infChar τ = infOf m := fun τ => by rw [hP.inf, hic]
  have hfin := slopesIn_of_slope m w' _ hinf' B fun l _ ι =>
    hS l ι Q.K 2 n Nat.prime_two hn P χ' hin w' (hQ2 w' hund) B hsat
  rwa [hq] at hfin
end

section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

theorem slopeAll (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : SlopeAll := slopeAllOf hL (slopeGood (slopeCsd hD))

theorem intP (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Br.IntP :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1 hπ.2.1 w B hB

theorem intK (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : IntK :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1
    ⟨quadChar K ^ n, fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hπ.2.1⟩ w B hB

end UpperTheory.V.Z.Int
end

section
namespace UpperTheory.V.Z.Int

theorem intP_of_desc (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Br.IntP := intP UpperTheory.ConvolutionTheory.Sph.quadLift hD

theorem intK_of_desc (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Af.IntK := intK UpperTheory.ConvolutionTheory.Sph.quadLift hD

end UpperTheory.V.Z.Int
end

section
namespace UpperTheory.V.Z.Int

theorem intP_holds : UpperTheory.V.Br.IntP := intP_of_desc UpperTheory.Gal.Desc.descOffT

theorem intK_holds : UpperTheory.V.Af.IntK := intK_of_desc UpperTheory.Gal.Desc.descOffT

theorem intP' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := fun _ => intP_holds

theorem intK' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := fun _ => intK_holds

example : type_of% @UpperTheory.V.Af.intK := @intK'

example : type_of% @UpperTheory.V.Br.intP := @intP'

end UpperTheory.V.Z.Int
end
