import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity

section
open NumberField IsDedekindDomain GlobalTheory.SUVol
open Matrix

namespace GlobalTheory.SUVol

theorem ncard_image_lifts_eq_card_specialUnitaryGroup {O : Type*} [CommRing O] (w : Ideal O)
    [StarRing (O ⧸ w)] (c : O → O)
    (hc : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x)) (r : ℕ) :
    Set.ncard ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Nat.card (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w)) := by
  have key : ∀ g : Matrix (Fin r) (Fin r) O,
      (g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w) ↔
        (g.map (Ideal.Quotient.mk w))ᵀ ∈ Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) := by
    intro g
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.det_transpose,
      and_comm]
    refine and_congr ?_ ?_
    · rw [← Matrix.ext_iff]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]
      have e1 : Ideal.Quotient.mk w ((gᵀ * g.map c) a b) =
          ((g.map (Ideal.Quotient.mk w))ᵀ * star (g.map (Ideal.Quotient.mk w))ᵀ) a b := by
        simp [Matrix.mul_apply, Matrix.star_apply, hc]
      have e2 : Ideal.Quotient.mk w ((1 : Matrix (Fin r) (Fin r) O) a b) =
          (1 : Matrix (Fin r) (Fin r) (O ⧸ w)) a b := by
        simp only [Matrix.one_apply]; split_ifs <;> simp
      rw [e1, e2]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_one, RingHom.map_det,
        RingHom.mapMatrix_apply]
  have himg : ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Matrix.transpose '' (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) : Set _) := by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, (key g).1 hg, Matrix.transpose_transpose _⟩
    · rintro ⟨B, hB, rfl⟩
      choose s hs using Ideal.Quotient.mk_surjective (I := w)
      have e : (Bᵀ.map s).map (Ideal.Quotient.mk w) = Bᵀ := by
        ext a b; simp [hs]
      refine ⟨Bᵀ.map s, (key _).2 ?_, e⟩
      rw [e, Matrix.transpose_transpose]; exact hB
  rw [himg, Set.ncard_image_of_injective _ Matrix.transpose_injective, ← Nat.card_coe_set_eq]
  rfl

theorem exists_star_ne_of_not_surjective {K A : Type*} [Field K] [Finite K] [StarRing K]
    (f : A → K) (hadd : ∀ x : K, ∃ a, f a = x + star x) (hmul : ∀ x : K, ∃ a, f a = x * star x)
    (hf : ¬ Function.Surjective f) : ∃ a : K, star a ≠ a := by
  by_contra h
  push Not at h
  apply hf
  intro x
  by_cases h2 : (2 : K) = 0
  · have hinj : Function.Injective (fun y : K => y * y) := by
      intro y z hyz
      simp only at hyz
      have : (y - z) * (y - z) = 0 := by linear_combination hyz + (z * z - y * z) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj x
    obtain ⟨a, ha⟩ := hmul y
    exact ⟨a, by rw [ha, h y]; exact hy⟩
  · obtain ⟨a, ha⟩ := hadd (x / 2)
    exact ⟨a, by rw [ha, h]; field_simp; ring⟩

theorem prod_le_locFactor_of_isPrime (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r)
    (hw : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime) :
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  classical
  unfold locFactor resOrder
  rw [if_pos hw]
  set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef
  set c := IsCMField.ringOfIntegersComplexConj E with hcdef
  have hcc : ∀ x, c (c x) = x := fun x => by
    ext; simp [hcdef]
  have hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a :=
    fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩
  have hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E) := by
    rw [hwdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c _ ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  have hw0 : w ≠ ⊥ := by
    rw [hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  haveI hmax : w.IsMaximal := hw.isMaximal hw0
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  let σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w) := Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle
  have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := fun x => rfl
  letI : StarRing (𝓞 E ⧸ w) :=
    { star := σ
      star_involutive := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change σ (σ _) = _
        rw [hσ, hσ, hcc]
      star_mul := fun x y => by
        change σ (x * y) = σ y * σ x
        rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := hσ
  rw [ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]
  set q := Ideal.absNorm v.asIdeal with hq
  have hK : Nat.card (𝓞 E ⧸ w) = q ^ 2 := by
    have h := Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal
    rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _),
      Submodule.cardQuot_apply] at h
    exact h
  have hq2 : 2 ≤ q := GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK
  have hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a := by
    let f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w) :=
      Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map
    have hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a) :=
      fun a => rfl
    refine exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1
        (by change c _ = _; rw [map_add, hcc, add_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add]⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1
        (by change c _ = _; rw [map_mul, hcc, mul_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩
    · haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
      have h1 := Nat.card_le_card_of_surjective f hsurj
      have h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q := by
        rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hK, h2] at h1
      nlinarith
  have h := GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  rw [le_div_iff₀ (by positivity)]
  refine le_of_le_of_eq ?_ h'.symm
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_))
    (by positivity)
  · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hq1))
  · have hp : (0 : ℝ) ≤ ((q : ℝ) ^ i)⁻¹ := by positivity
    rcases neg_one_pow_eq_or ℝ i with h1 | h1 <;> rw [h1] <;> linarith

end GlobalTheory.SUVol
end

section
open NumberField IsDedekindDomain GlobalTheory.SUVol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  first | exact @GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | exact GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | (intros; apply GlobalTheory.SUVol.prod_le_locFactor_of_isPrime <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.EulerLocVol

noncomputable def invPowHom (i : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ i)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_pow, mul_inv]

theorem inv_zeta_le_prod_primes : ∀ (i : ℕ), 2 ≤ i → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := by
  intro i hi P hP
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
    simpa using this
  have hs' : Summable (invPowHom i) := by
    have := Real.summable_one_div_nat_pow.2 (by omega : 1 < i)
    simpa [invPowHom] using this
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invPowHom i p‖ < 1 := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
    simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, norm_pow, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt P).2
  have hfilt : P.filter Nat.Prime = P := Finset.filter_true_of_mem hP
  rw [hfilt] at hE
  have hfac : ∀ p ∈ P, 0 < 1 - ((p : ℝ) ^ i)⁻¹ := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast (hP p hp).one_lt) (by omega)
    exact sub_pos.2 (inv_lt_one_of_one_lt₀ h1)
  have hpos : 0 < ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := Finset.prod_pos hfac
  have hle : ∏ p ∈ P, (1 - invPowHom i p)⁻¹ ≤ ∑' n : ℕ, invPowHom i n := by
    rw [← hE.tsum_eq]
    exact Summable.tsum_subtype_le (⇑(invPowHom i)) _ (fun n => by change 0 ≤ ((n : ℝ) ^ i)⁻¹; positivity) hs'
  have hz : ∑' n : ℕ, invPowHom i n = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    rw [hs'.tsum_eq_zero_add]
    simp [invPowHom, show i ≠ 0 by omega]
  rw [hz, Finset.prod_inv_distrib] at hle
  simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hle
  calc (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ((∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹))⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.2 hpos) hle
    _ = _ := inv_inv _

theorem le_locFactor_of_not_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    ¬ (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  intro E _ _ _ r v hr hnp
  let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  unfold locFactor resOrder
  rw [if_neg hnp]
  have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at this
    exact this
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]

theorem tprod_locFactor_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (locFactor E r) → 0 < ∏' v, locFactor E r v ∧
      (∏' v, locFactor E r v)⁻¹ ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, g (Ideal.absNorm v.asIdeal) ≤ locFactor E r v := by
    intro v
    by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
    · exact GlobalTheory.T.local_factor_lower_bound E r v (by omega) hp
    · exact le_locFactor_of_not_prime E r v (by omega) hp
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, locFactor E r v := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, locFactor E r v := by
      refine Finset.prod_le_prod (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => (g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)).trans (hloc v)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
      refine inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
      _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
      _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
      _ ≤ _ := s3
      _ = _ := s2.symm
      _ ≤ _ := s1
  have hle : (Z ^ fdeg E)⁻¹ ≤ ∏' v, locFactor E r v :=
    ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)
  have hpos : 0 < (Z ^ fdeg E)⁻¹ := by positivity
  refine ⟨hpos.trans_le hle, ?_⟩
  calc (∏' v, locFactor E r v)⁻¹ ≤ ((Z ^ fdeg E)⁻¹)⁻¹ := inv_anti₀ hpos hle
    _ = Z ^ fdeg E := inv_inv _

end GlobalTheory.EulerLocVol
end
