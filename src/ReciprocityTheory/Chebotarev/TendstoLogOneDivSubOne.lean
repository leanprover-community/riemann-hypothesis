import ReciprocityTheory.Chebotarev.CycStatement
import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import Mathlib
import ReciprocityTheory.Chebotarev.NZIdeal
import ReciprocityTheory.Chebotarev.ChebyshevLambdaSubPsiBounded
import ReciprocityTheory.Chebotarev.KHoldA
import ReciprocityTheory.Chebotarev.Ucoord
import ReciprocityTheory.Chebotarev.SplitA
import ReciprocityTheory.Chebotarev.SplitF
import ReciprocityTheory.Chebotarev.SplitDef

section
namespace ReciprocityTheory.Cheb

open Filter Topology Set Complex

theorem isDiscrete_exp_fiber (c : ℂ) : IsDiscrete {w : ℂ | Complex.exp w = c} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  refine ⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩
  ext w
  simp only [mem_inter_iff, Metric.mem_ball, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hw, hwc⟩
    have hexp : Complex.exp w = Complex.exp y := hwc.trans hy.symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      simpa using hn
    have hd : dist w y = |(n : ℝ)| * (2 * Real.pi) := by
      rw [dist_eq_norm, hn, add_sub_cancel_left, norm_mul, Complex.norm_intCast]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have := Real.pi_gt_three
    nlinarith
  · rintro rfl
    exact ⟨Metric.mem_ball_self one_pos, hy⟩

theorem bounded_of_tendsto_exp {abelian₂ : ℝ → ℂ} {L1 : ℂ} (hcont : ContinuousOn abelian₂ (Ioc 1 2))
    (hL1 : L1 ≠ 0) (hlim : Tendsto (fun s => Complex.exp (abelian₂ s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C, ∀ s ∈ Ioc (1 : ℝ) 2, ‖abelian₂ s‖ ≤ C := by

  have hslitB : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), z ∈ slitPlane := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    exact mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_le.mp (this.trans hz)).1]))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (f := Complex.log) (fun z hz => (continuousAt_clog (hslitB z hz)).continuousWithinAt)

  have hlim' : Tendsto (fun s => Complex.exp (abelian₂ s) / L1) (𝓝[>] 1) (𝓝 1) := by
    simpa [div_self hL1] using hlim.div_const L1
  have hev := hlim'.eventually (Metric.closedBall_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu1 : (1 : ℝ) < u := hu1
  set t : ℝ := min ((1 + u) / 2) 2 with ht
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  have hSsub : Ioc 1 t ⊆ Ioc (1 : ℝ) 2 := Ioc_subset_Ioc_right ht2
  have hball : ∀ s ∈ Ioc 1 t, Complex.exp (abelian₂ s) / L1 ∈ Metric.closedBall (1 : ℂ) (1 / 2) :=
    fun s hs => hu ⟨hs.1, lt_of_le_of_lt hs.2 htu⟩

  set g : ℝ → ℂ := fun s => abelian₂ s - Complex.log (Complex.exp (abelian₂ s) / L1) with hg
  have hgc : ContinuousOn g (Ioc 1 t) := by
    intro s hs
    have h1 : ContinuousWithinAt abelian₂ (Ioc 1 t) s := (hcont s (hSsub hs)).mono hSsub
    have h2 : ContinuousWithinAt (fun s => Complex.exp (abelian₂ s) / L1) (Ioc 1 t) s :=
      (Complex.continuous_exp.continuousAt.comp_continuousWithinAt h1).div_const L1
    have h3 : ContinuousWithinAt (fun s => Complex.log (Complex.exp (abelian₂ s) / L1)) (Ioc 1 t) s :=
      (continuousAt_clog (hslitB _ (hball s hs))).comp_continuousWithinAt
        (f := fun s => Complex.exp (abelian₂ s) / L1) h2
    exact h1.sub h3
  have hmaps : MapsTo g (Ioc 1 t) {w : ℂ | Complex.exp w = L1} := by
    intro s _
    have hne : Complex.exp (abelian₂ s) / L1 ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hL1
    simp only [mem_ofPred_eq, hg, Complex.exp_sub, Complex.exp_log hne]
    field_simp [Complex.exp_ne_zero]
  obtain ⟨c, -, hc⟩ := isPreconnected_Ioc.eqOn_const_of_mapsTo (isDiscrete_exp_fiber L1) hgc hmaps
    ⟨Complex.log L1, Complex.exp_log hL1⟩

  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact (Icc t 2)).exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ioc_iff ht2 |>.mpr ⟨ht1, le_rfl⟩))
  refine ⟨max (‖c‖ + B) C2, fun s hs => ?_⟩
  rcases le_or_gt s t with hst | hst
  · have hs' : s ∈ Ioc 1 t := ⟨hs.1, hst⟩
    have hgs : g s = c := hc hs'
    have hL : abelian₂ s = c + Complex.log (Complex.exp (abelian₂ s) / L1) := by
      rw [← hgs, hg]; ring
    calc ‖abelian₂ s‖ = ‖c + Complex.log (Complex.exp (abelian₂ s) / L1)‖ := by rw [← hL]
      _ ≤ ‖c‖ + ‖Complex.log (Complex.exp (abelian₂ s) / L1)‖ := norm_add_le _ _
      _ ≤ ‖c‖ + B := by gcongr; exact hB _ (hball s hs')
      _ ≤ _ := le_max_left _ _
  · exact (hC2 s ⟨hst.le, hs.2⟩).trans (le_max_right _ _)

theorem bdd_of_exp_tendsto (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 1)) (L1 : ℂ) (hL : L1 ≠ 0)
    (h : Tendsto (fun s => Complex.exp (f s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := bounded_of_tendsto_exp (hf.mono Set.Ioc_subset_Ioi_self) hL h
  exact ⟨C, Filter.mem_of_superset (Ioc_mem_nhdsGT one_lt_two) hC⟩

end ReciprocityTheory.Cheb
end

section
open NumberField

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem cyor_nrm_pos (q : Prm E) : 0 < Nrm q := by
  unfold Nrm
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact q.ne_bot

theorem cyor_norm_cpow (q : Prm E) (s : ℝ) :
    ‖((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ = ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_pos (cyor_nrm_pos q)]
  simp

theorem cyor_cast_rpow (q : Prm E) (s : ℝ) :
    ((((Nrm q : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) = ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

theorem cyor_term_norm_le {l : ℕ} (χ : DirichletCharacter ℂ l) (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [norm_mul, cyor_norm_cpow]
  have h1 := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]

theorem cyor_summable {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Summable (fun q : Prm E => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) :=
  Summable.of_norm_bounded hS (fun q => cyor_term_norm_le χ q s)

theorem psum_orth (l : ℕ) [NeZero l] (a : (ZMod l)ˣ) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ∑ χ : DirichletCharacter ℂ l, χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s
      = ((Nat.totient l : ℕ) : ℂ) * (Pcl E l (a : ZMod l) s : ℂ) := by
  unfold Psum Pcl
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun χ _ => (cyor_summable χ s hS).mul_left _)]
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  congr 1
  funext q
  have hinv : (((a⁻¹ : (ZMod l)ˣ) : ZMod l)) = ((a : ZMod l))⁻¹ := by
    rw [ZMod.inv_coe_unit]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp_rw [hinv]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
  by_cases h : (a : ZMod l) = ((Nrm q : ℕ) : ZMod l)
  · rw [if_pos h, if_pos h.symm, cyor_cast_rpow]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

theorem norm_psum_le {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ‖Psum E χ s‖ ≤ PE E s := by
  unfold Psum PE
  refine (norm_tsum_le_tsum_norm (cyor_summable χ s hS).norm).trans ?_
  exact Summable.tsum_le_tsum (fun q => cyor_term_norm_le χ q s) (cyor_summable χ s hS).norm hS

theorem pcl_one_le_re_psum_one (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Pcl E l 1 s ≤ (Psum E (1 : DirichletCharacter ℂ l) s).re := by
  unfold Pcl Psum
  rw [Complex.re_tsum (cyor_summable _ s hS)]
  have hS2 : Summable (fun q : Prm E =>
      if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS
    · split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine Summable.tsum_le_tsum (fun q => ?_) hS2 (Complex.reCLM.summable (cyor_summable _ s hS))
  rw [← cyor_cast_rpow]
  split_ifs with h
  · rw [h]; simp
  · by_cases hu : IsUnit ((Nrm q : ℕ) : ZMod l)
    · rw [MulChar.one_apply hu, one_mul, Complex.ofReal_re]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [MulChar.map_nonunit _ hu]; simp

theorem re_psum_one_le (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ PE E s :=
  (Complex.re_le_norm _).trans (norm_psum_le _ s hS)

theorem pcl_nonneg (l : ℕ) (a : ZMod l) (s : ℝ) : 0 ≤ Pcl E l a s := by
  unfold Pcl
  refine tsum_nonneg (fun q => ?_)
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact le_rfl

end ReciprocityTheory.Cheb
end

section
open NumberField IsDedekindDomain

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

noncomputable def primeBelow (q : Prm E) : ℕ := Ideal.absNorm (q.asIdeal.under ℤ)

theorem primeBelow_prime (q : Prm E) : (primeBelow q).Prime := by
  have : NeZero q.asIdeal := ⟨q.ne_bot⟩
  exact Nat.absNorm_under_prime q.asIdeal

theorem nrm_eq_primeBelow_pow (q : Prm E) : ∃ f : ℕ, Nrm q = primeBelow q ^ f :=
  have : q.asIdeal.LiesOver (Ideal.span {((primeBelow q : ℕ) : ℤ)}) := Int.liesOver_span_absNorm q.asIdeal
  ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' q.asIdeal (primeBelow_prime q)⟩

theorem two_le_nrm (q : Prm E) : 2 ≤ Nrm q := by
  have h0 : Nrm q ≠ 0 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot
  have h1 : Nrm q ≠ 1 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_one_iff]; exact q.isPrime.ne_top
  omega

theorem primeBelow_sq_le (q : Prm E) (h : ¬ (Nrm q).Prime) : primeBelow q ^ 2 ≤ Nrm q := by
  obtain ⟨f, hf⟩ := nrm_eq_primeBelow_pow q
  have hp := primeBelow_prime q
  have h1 : Nrm q ≠ 1 := by have := two_le_nrm q; omega
  rw [hf] at h h1 ⊢
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1
  have hf1 : f ≠ 1 := by rintro rfl; simp [hp] at h
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem mem_primesOverFinset_primeBelow (q : Prm E) :
    q.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((primeBelow q : ℕ) : ℤ)}) (𝓞 E) := by
  have hp := primeBelow_prime q
  have : (Ideal.span {((primeBelow q : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  rw [IsDedekindDomain.mem_primesOverFinset_iff (by simp [hp.ne_zero])]
  exact ⟨q.isPrime, Int.liesOver_span_absNorm q.asIdeal⟩

theorem card_primesOverFinset_le (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 E)).card ≤ Module.finrank ℚ E := by
  have : (Ideal.span {(p:ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E (by simp [hp.ne_zero])

theorem card_filter_primeBelow_le (u : Finset (Prm E)) (p : ℕ) (hp : p.Prime) :
    (u.filter fun x => primeBelow x = p).card ≤ Module.finrank ℚ E := by
  classical
  refine le_trans ?_ (card_primesOverFinset_le (E := E) p hp)
  refine Finset.card_le_card_of_injOn (fun x => x.asIdeal) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter] at hx
    have := mem_primesOverFinset_primeBelow x
    rw [hx.2] at this
    exact this
  · intro x _ y _ hxy
    exact HeightOneSpectrum.ext hxy

theorem nonprime_term_le (q : Prm E) :
    (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) ≤ 1 / ((primeBelow q : ℕ) : ℝ) ^ 2 := by
  split_ifs with h
  · positivity
  · have hq := primeBelow_sq_le q h
    have hp := (primeBelow_prime q).pos
    have hq' : ((primeBelow q : ℝ)) ^ 2 ≤ (Nrm q : ℝ) := by exact_mod_cast hq
    have hpos : (0 : ℝ) < (primeBelow q : ℝ) ^ 2 := by positivity
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos hq'

theorem summable_nonprime_norm :
    Summable (fun q : Prm E => if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) := by
  classical
  let G : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hG : Summable G := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hG0 : ∀ n, 0 ≤ G n := fun n => by positivity
  refine summable_of_sum_le (c := Module.finrank ℚ E * ∑' n, G n) (fun q => by
    dsimp only; split_ifs <;> positivity) (fun u => ?_)
  calc ∑ x ∈ u, (if (Nrm x).Prime then (0 : ℝ) else ((Nrm x : ℕ) : ℝ)⁻¹)
        ≤ ∑ x ∈ u, G (primeBelow x) := Finset.sum_le_sum fun x _ => nonprime_term_le x
    _ = ∑ b ∈ u.image (fun x => primeBelow x),
          (u.filter fun x => primeBelow x = b).card • G b := Finset.sum_comp _ _
    _ ≤ ∑ b ∈ u.image (fun x => primeBelow x), (Module.finrank ℚ E : ℝ) * G b := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hb
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hG0 _)
        exact_mod_cast card_filter_primeBelow_le u _ (primeBelow_prime x)
    _ = (Module.finrank ℚ E : ℝ) * ∑ b ∈ u.image (fun x => primeBelow x), G b := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ E : ℝ) * ∑' n, G n :=
        mul_le_mul_of_nonneg_left (hG.sum_le_tsum _ fun n _ => hG0 n) (by positivity)

theorem finite_norm_mem (T : Finset ℕ) : {q : Prm E | Nrm q ∈ T}.Finite := by
  have h : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T}.Finite := by
    have : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T} = ⋃ n ∈ T, {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
      ext; simp
    rw [this]
    exact Set.Finite.biUnion T.finite_toSet fun n _ => Ideal.finite_setOfPred_absNorm_eq n
  exact h.preimage (f := fun q : Prm E => q.asIdeal) (fun x _ y _ hxy => HeightOneSpectrum.ext hxy)

end ReciprocityTheory.Cheb
end

section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

noncomputable def mulDvdEquiv (c : NZIdeal E) : NZIdeal E ≃ {a : NZIdeal E // c.1 ∣ a.1} :=
  Equiv.ofBijective (fun b => ⟨⟨c.1 * b.1, mul_ne_zero c.2 b.2⟩, dvd_mul_right _ _⟩) (by
    constructor
    · intro b b' h
      have h1 : c.1 * b.1 = c.1 * b'.1 := congrArg (fun x => x.1.1) h
      exact Subtype.ext (mul_left_cancel₀ c.2 h1)
    · rintro ⟨a, ⟨b, hb⟩⟩
      have hb0 : b ≠ ⊥ := by
        rintro rfl
        exact a.2 (by rw [hb]; simp)
      exact ⟨⟨b, hb0⟩, Subtype.ext (Subtype.ext hb.symm)⟩)

theorem mulDvdEquiv_apply (c b : NZIdeal E) : (mulDvdEquiv c b).1.1 = c.1 * b.1 := rfl

theorem tsum_dvd_eq {l : ℕ} (χ : DirichletCharacter ℂ l) (c : NZIdeal E) {s : ℝ} (hs : 1 < s) :
    ∑' a : NZIdeal E, (if c.1 ∣ a.1 then
        χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) else 0) =
      χ ((Ideal.absNorm c.1 : ℕ) : ZMod l) * ((Ideal.absNorm c.1 : ℕ) : ℂ) ^ (-(s : ℂ)) * Lser E χ s := by
  set g : NZIdeal E → ℂ := fun a =>
    χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) with hg
  have h1 : (∑' a : NZIdeal E, (if c.1 ∣ a.1 then g a else 0)) =
      ∑' a : {a : NZIdeal E // c.1 ∣ a.1}, g a.1 := by
    rw [show (∑' a : {a : NZIdeal E // c.1 ∣ a.1}, g a.1) =
      ∑' a : ({a : NZIdeal E | c.1 ∣ a.1} : Set (NZIdeal E)), g a.1 from rfl, tsum_subtype]
    exact tsum_congr (fun a => by simp [Set.indicator_apply])
  rw [h1, ← (mulDvdEquiv c).tsum_eq, Lser, ← tsum_mul_left]
  refine tsum_congr (fun b => ?_)
  simp only [hg]
  rw [mulDvdEquiv_apply]
  simp only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem tsum_eq_sum_cls (F : NZIdeal E → ℂ) (hF : Summable F) :
    ∑' a : NZIdeal E, F a = ∑ C : ClassGroup (𝓞 E), ∑' a : NZIdeal E, (if cls a = C then F a else 0) := by
  rw [← Summable.tsum_finsetSum (fun C _ => ?_)]
  · refine tsum_congr (fun a => ?_)
    rw [Finset.sum_ite_eq]
    simp
  · have := hF.indicator {a | cls a = C}
    refine this.congr (fun a => ?_)
    simp [Set.indicator_apply]

theorem exists_cls_eq (C : ClassGroup (𝓞 E)) : ∃ b : NZIdeal E, cls b = C := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective C
  exact ⟨⟨I.1, nonZeroDivisors.ne_zero I.2⟩, hI⟩

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem csb_nrm_pos {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ Nrm q := by
  unfold Nrm
  rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact q.ne_bot

theorem csb_pow_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ^ 2 ≤ b) (s : ℝ) (hs : 1 < s) :
    ((b : ℕ) : ℝ) ^ (-s) ≤ ((a : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : ((a : ℝ)) ^ 2 ≤ (b : ℝ) := by exact_mod_cast hab
  have hb' : (1 : ℝ) ≤ b := le_trans (one_le_pow₀ ha') hab'
  calc ((b : ℝ)) ^ (-s) ≤ (b : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb' (by linarith)
    _ = (b : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ ((a : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hab'
    _ = (a : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem PE_cyclotomicField_le_mul_Pcl_add_const (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → PE (CyclotomicField l E) s ≤ ((l - 1 : ℕ) : ℝ) * Pcl E l 1 s + C := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hfin := splitA_finite_not_coprime E l hl0
  set A : ℝ := ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)
  set B : ℝ := ∑' q : Prm E, (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)
  refine ⟨((l - 1 : ℕ) : ℝ) * (A + B), fun s hs => ?_⟩
  have hA : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)) := affine_proper_base_change.2.2 E 2 (by norm_num)
  have hB : Summable (fun q : Prm E => (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)) := by
    apply summable_of_ne_finset_zero (s := hfin.toFinset)
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    simp only [Set.mem_ofPred_eq, not_not] at hq
    simp [hq]
  have hP1 : Summable (fun q : Prm E =>
      if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) (affine_proper_base_change.2.2 E s hs)
    · split_ifs <;> positivity
    · split_ifs
      · exact le_rfl
      · positivity
  let h : Prm E → ℝ := fun q =>
    ((if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) + ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)) +
      (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)
  have hh0 : ∀ q, 0 ≤ h q := by
    intro q
    simp only [h]
    have : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ) := by positivity
    split_ifs <;> positivity
  have hhs : Summable h := (hP1.add hA).add hB
  have hfh : ∀ P : Prm (CyclotomicField l E), ((Nrm P : ℕ) : ℝ) ^ (-s) ≤ h (under P) := by
    intro P
    set q := under (E := E) P with hq
    have hq1 := csb_nrm_pos q
    have hP1' := csb_nrm_pos P
    have h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ) := by positivity
    have hPs : 0 ≤ ((Nrm P : ℕ) : ℝ) ^ (-s) := by positivity
    simp only [h]
    by_cases hc : Nat.Coprime (Nrm q) l
    · have hnd : ¬ l ∣ Nrm q := by
        rw [← Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
        exact hc.symm
      rw [if_pos hc, add_zero]
      rcases splitA_norm E l q P hq.symm hnd with ⟨he, h1⟩ | hsq
      · rw [if_pos h1, he]
        linarith
      · have := csb_pow_le _ _ hq1 hsq s hs
        have : 0 ≤ (if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
          split_ifs <;> positivity
        linarith
    · rw [if_neg hc]
      have : ((Nrm P : ℕ) : ℝ) ^ (-s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hP1') (by linarith)
      have : 0 ≤ (if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
        split_ifs <;> positivity
      linarith
  have key := fibre_sum_le (under (E := E)) (fun P : Prm (CyclotomicField l E) => ((Nrm P : ℕ) : ℝ) ^ (-s)) h
    (l - 1) (fun P => by positivity) hfh hh0 hhs (fun q => splitA_fibre E l hirr q)
  have hsum : ∑' q, h q = Pcl E l 1 s + A + B := by
    simp only [h]
    rw [(hP1.add hA).tsum_add hB, hP1.tsum_add hA]
    rfl
  have : PE (CyclotomicField l E) s ≤ ((l - 1 : ℕ) : ℝ) * ∑' q, h q := key.2
  rw [hsum] at this
  linarith

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitC_nrm_pos {E : Type} [Field E] [NumberField E] (q : Prm E) : 0 < ((Nrm q : ℕ) : ℝ) := by
  have : Nrm q ≠ 0 := by
    unfold Nrm
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem splitC_nrm_ge_one {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ ((Nrm q : ℕ) : ℝ) := by
  have h := splitC_nrm_pos q
  have : 0 < Nrm q := by exact_mod_cast h
  exact_mod_cast this

theorem splitC_indicator_le {E : Type} [Field E] [NumberField E] (S : Set (Prm E)) (hS : S.Finite) (s : ℝ)
    (hs : 0 ≤ s) : ∑' q, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q ≤ hS.toFinset.card := by
  rw [tsum_eq_sum (s := hS.toFinset)]
  · calc ∑ q ∈ hS.toFinset, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q
        ≤ ∑ _q ∈ hS.toFinset, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Set.indicator_of_mem (hS.mem_toFinset.mp hq)]
          exact Real.rpow_le_one_of_one_le_of_nonpos (splitC_nrm_ge_one q) (by linarith)
      _ = hS.toFinset.card := by simp
  · intro q hq
    rw [Set.indicator_of_notMem]
    intro h'
    exact hq (hS.mem_toFinset.mpr h')

theorem splitC_bound (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (S : Set (Prm E)) (hS : S.Finite)
    (h : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard) (s : ℝ) (hs : 1 < s) :
    (k : ℝ) * PE E s ≤ PE E' s + k * hS.toFinset.card := by
  have key := fibre_sum_ge (under (E := E) (E' := E')) (fun P : Prm E' => ((Nrm P : ℕ) : ℝ) ^ (-s))
    (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) k (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (affine_proper_base_change.2.2 E' s hs) (fun q => Real.rpow_nonneg (Nat.cast_nonneg _) _) (affine_proper_base_change.2.2 E s hs) S hS
    (by
      intro q hq
      have hset : {P : Prm E' | under P = q ∧ ((Nrm P : ℕ) : ℝ) ^ (-s) = ((Nrm q : ℕ) : ℝ) ^ (-s)} =
          {P : Prm E' | under P = q ∧ Nrm P = Nrm q} := by
        ext P
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith : -s ≠ 0)).mp h2
          exact_mod_cast this
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [h2]⟩
      rw [hset]
      exact h q hq)
  have hind := splitC_indicator_le S hS s (by linarith)
  unfold PE
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hind hk0]

theorem splitC_not_almost_split (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (hk : 2 ≤ k)
    (h : {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard}.Finite) : False := by
  set S := {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard} with hSdef
  have hfib : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
    intro q hq
    by_contra hc
    exact hq hc
  obtain ⟨C1, hC1⟩ := chebyshev_log_bounded E
  obtain ⟨C2, hC2⟩ := chebyshev_log_bounded E'
  set N : ℝ := (h.toFinset.card : ℝ)
  set M : ℝ := max (C2 + k * (N + C1)) 0
  set s : ℝ := 1 + Real.exp (-(M + 1))
  have he : 0 < Real.exp (-(M + 1)) := Real.exp_pos _
  have he1 : Real.exp (-(M + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ M := le_max_right _ _
    linarith)
  have hs1 : 1 < s := by simp only [s]; linarith
  have hs2 : s ∈ Set.Ioc 1 2 := ⟨hs1, by simp only [s]; linarith⟩
  have hlog : Real.log (1 / (s - 1)) = M + 1 := by
    simp only [s, add_sub_cancel_left, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hb := splitC_bound E E' k S h hfib s hs1
  have h1 := hC1 s hs2
  have h2 := hC2 s hs2
  rw [hlog] at h1 h2
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM : C2 + k * (N + C1) ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have : (k : ℝ) * (M + 1 - C1) ≤ k * PE E s := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitD_natCast_not_mem (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (hl : ¬ l ∣ Nrm q) : (l : 𝓞 E) ∉ q.asIdeal := by
  intro h
  have hmax : q.asIdeal.IsMaximal := q.isMaximal
  let : Field (𝓞 E ⧸ q.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 E ⧸ q.asIdeal) := by
    have := (Ideal.absNorm_ne_zero_iff q.asIdeal).1 (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot)
    exact this
  let := Fintype.ofFinite (𝓞 E ⧸ q.asIdeal)
  have h0 : ((l : 𝓞 E ⧸ q.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk q.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact h
  set p := ringChar (𝓞 E ⧸ q.asIdeal)
  have hpl : p ∣ l := (ringChar.spec _ l).1 h0
  have hp1 : p ≠ 1 := CharP.ringChar_ne_one
  have hpeq : p = l := ((Fact.out : l.Prime).eq_one_or_self_of_dvd p hpl).resolve_left hp1
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ q.asIdeal) p
  apply hl
  have : Nrm q = Fintype.card (𝓞 E ⧸ q.asIdeal) := by
    rw [Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [this, hn, hpeq]
  exact dvd_pow_self l n.ne_zero

theorem splitD_frob (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    ∃ σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E,
      σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
        IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ Nrm q ∧
      ∀ x : 𝓞 (CyclotomicField l E), ∃ y : 𝓞 (CyclotomicField l E),
        (y : CyclotomicField l E) = σ (x : CyclotomicField l E) ∧ y - x ^ Nrm q ∈ P.asIdeal := by
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E _
  have : Algebra.IsInvariant (𝓞 E) (𝓞 (CyclotomicField l E))
      (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Algebra.isInvariant_of_isGalois' (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))
  have : Finite (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Finite.of_equiv _ (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).toEquiv
  have : P.asIdeal.IsPrime := P.isPrime
  have : Finite (𝓞 (CyclotomicField l E) ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff P.asIdeal).1 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E)
    (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) P.asIdeal
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) = Nrm q := by
    rw [Nrm, ← hP, under_asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ : ∀ x : 𝓞 (CyclotomicField l E),
      ((τ x : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
        (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ
          (x : CyclotomicField l E) := by
    intro x
    have := algebraMap_galRestrict_apply (𝓞 E)
      ((galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ) x
    simpa only [MulEquiv.apply_symm_apply] using this
  have hfr : ∀ x : 𝓞 (CyclotomicField l E), τ x - x ^ Nrm q ∈ P.asIdeal := by
    intro x
    have := hτ x
    rw [hcard] at this
    exact this
  refine ⟨(galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ, ?_,
    fun x => ⟨τ x, hσ x, hfr x⟩⟩
  have hz := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  have hlP : ((l : ℕ) : 𝓞 (CyclotomicField l E)) ∉ P.asIdeal := by
    intro h
    apply splitD_natCast_not_mem E l q hl
    rw [← hP, under_asIdeal, Ideal.mem_comap, map_natCast]
    exact h
  have h1 := hτ.apply_of_pow_eq_one (ζ := hz.toInteger) (m := l) hz.toInteger_isPrimitiveRoot.pow_eq_one hlP
  rw [hcard] at h1
  have h2 : ((τ hz.toInteger : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
      ((hz.toInteger ^ Nrm q : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) := congrArg _ h1
  rw [hσ] at h2
  push_cast at h2
  exact h2

end ReciprocityTheory.Cheb
end

section
open NumberField

namespace ReciprocityTheory.Cheb

noncomputable section

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

def splitEH (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    Subgroup (CyclotomicField l E ≃ₐ[E] CyclotomicField l E) :=
  (χ.toUnitHom.comp (IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr).toMonoidHom).ker

theorem splitE_autEquivPow_eq (hirr : Irreducible (Polynomial.cyclotomic l E))
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) :
    ((IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr σ : (ZMod l)ˣ) : ZMod l) = (m : ZMod l) := by
  have hζ := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  rw [IsCyclotomicExtension.autEquivPow_apply]
  have h1 := hζ.autToPow_spec E σ
  rw [hσ] at h1
  have hfin : IsOfFinOrder (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨l, (Fact.out : l.Prime).pos, hζ.pow_eq_one⟩
  have h2 := hfin.pow_eq_pow_iff_modEq.1 h1
  rw [← hζ.eq_orderOf] at h2
  change (((hζ.autToPow E σ : (ZMod l)ˣ) : ZMod l)) = _
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow E σ : (ZMod l)ˣ) : ZMod l)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h2

theorem splitE_mem_H (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) (hm : χ (m : ZMod l) = 1) :
    σ ∈ splitEH hirr χ := by
  rw [splitEH, MonoidHom.mem_ker]
  apply Units.ext
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  simp only [MulEquiv.coe_toMonoidHom, Units.val_one]
  rw [splitE_autEquivPow_eq hirr σ m hσ, hm]

theorem splitE_H_ne_top (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (hχ : χ ≠ 1) : splitEH hirr χ ≠ ⊤ := by
  intro hH
  apply hχ
  apply MulChar.ext
  intro u
  have hm : (IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr).symm u ∈ splitEH hirr χ := by
    rw [hH]; exact Subgroup.mem_top _
  rw [splitEH, MonoidHom.mem_ker] at hm
  have := congrArg Units.val hm
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom] at this
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, Units.val_one] at this
  rw [this, MulChar.one_apply_coe]

theorem splitE_two_le (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (hχ : χ ≠ 1) : 2 ≤ Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) := by
  have h0 : 0 < Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) := Module.finrank_pos
  have h1 : Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) ≠ 1 := by
    intro h
    rw [IntermediateField.finrank_eq_one_iff] at h
    apply splitE_H_ne_top hirr χ hχ
    rw [← IntermediateField.fixingSubgroup_fixedField (splitEH hirr χ), h,
      IntermediateField.fixingSubgroup_bot]
  omega

theorem splitE_one_lt_Nrm (q : Prm E) : 1 < Nrm q := by
  unfold Nrm
  have h0 : Ideal.absNorm q.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot
  have h1 : Ideal.absNorm q.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact q.isPrime.ne_top
  omega

theorem splitE_prime (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (q : Prm E) (hl : ¬ l ∣ Nrm q) (hq : χ ((Nrm q : ℕ) : ZMod l) = 1)
    (K : IntermediateField E (CyclotomicField l E))
    (hK : ∀ x : K, ∀ σ ∈ splitEH hirr χ, σ (x : CyclotomicField l E) = x)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver q.asIdeal] :
    Q.ramificationIdx (𝓞 E) = 1 ∧ Q.inertiaDeg (𝓞 E) = 1 ∧ Ideal.absNorm Q = Nrm q := by
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot Q
  obtain ⟨⟨P, hPp, hPl⟩⟩ := Q.nonempty_primesOver (S := 𝓞 (CyclotomicField l E))
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQ0 P
  have hPq : P.LiesOver q.asIdeal := Ideal.LiesOver.trans P Q q.asIdeal
  let P' : Prm (CyclotomicField l E) := ⟨P, hPp, hP0⟩
  have hund : under (E := E) P' = q := by
    ext1; rw [under_asIdeal]; exact (Ideal.over_def P q.asIdeal).symm
  have he : Q.ramificationIdx (𝓞 E) = 1 := by
    have h1 := splitA_unram E l q P' hund hl
    have h2 := Ideal.ramificationIdx_tower (R := 𝓞 E) Q P
    change P.ramificationIdx (𝓞 E) = 1 at h1
    rw [h2] at h1
    exact Nat.eq_one_of_mul_eq_one_right h1
  obtain ⟨σ, hσζ, hσx⟩ := splitD_frob E l q P' hund hl
  have hσH : σ ∈ splitEH hirr χ := splitE_mem_H hirr χ σ _ hσζ hq
  have hfix : ∀ x : 𝓞 K, x - x ^ Nrm q ∈ Q := by
    intro x
    obtain ⟨y, hy, hyP⟩ := hσx (algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x)
    have hxy : y = algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x := by
      apply RingOfIntegers.ext
      rw [hy]
      have : ((algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x : 𝓞 _) : CyclotomicField l E) =
          ((x : K) : CyclotomicField l E) := rfl
      rw [this]
      exact hK (x : K) σ hσH
    rw [hxy] at hyP
    rw [Ideal.over_def P Q]
    simpa [Ideal.under, map_sub, map_pow] using hyP
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  have : q.asIdeal.IsMaximal := q.isMaximal
  have hN := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver Q q.asIdeal q.isPrime q.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hN
  have h2 : 1 < Nrm q := splitE_one_lt_Nrm q
  let : Field (𝓞 K ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (𝓞 K ⧸ Q) := Fintype.ofFinite _
  have hcard : Ideal.absNorm Q ≤ Nrm q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← Finset.card_univ]
    rw [← FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 K ⧸ Q) h2]
    apply Polynomial.card_le_degree_of_subset_roots
    intro z _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ h2)]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have := (Ideal.Quotient.eq_zero_iff_mem).2 (hfix x)
    rw [map_sub, map_pow, sub_eq_zero] at this
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← this, sub_self]
  have hf0 : 0 < Q.inertiaDeg (𝓞 E) := Ideal.inertiaDeg_pos Q (𝓞 E)
  have hf : Q.inertiaDeg (𝓞 E) = 1 := by
    have h3 : Nrm q ^ Q.inertiaDeg (𝓞 E) ≤ Nrm q ^ 1 := by
      rw [pow_one]; unfold Nrm; rw [← hN]; exact hcard
    have := (Nat.pow_le_pow_iff_right h2).1 h3
    omega
  refine ⟨he, hf, ?_⟩
  rw [hN, hf, pow_one]; rfl

theorem splitE_count (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (q : Prm E) (hl : ¬ l ∣ Nrm q) (hq : χ ((Nrm q : ℕ) : ZMod l) = 1)
    (K : IntermediateField E (CyclotomicField l E))
    (hK : ∀ x : K, ∀ σ ∈ splitEH hirr χ, σ (x : CyclotomicField l E) = x) :
    Module.finrank E K ≤ {P : Prm K | under P = q ∧ Nrm P = Nrm q}.ncard := by
  classical
  have hfin : (q.asIdeal.primesOver (𝓞 K)).Finite := Algebra.QuasiFinite.finite_primesOver q.asIdeal
  let : Fintype (q.asIdeal.primesOver (𝓞 K)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank q.asIdeal (𝓞 K)
  rw [← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K] at hsum
  have hone : ∀ Q : q.asIdeal.primesOver (𝓞 K),
      Q.1.ramificationIdx (𝓞 E) * Q.1.inertiaDeg (𝓞 E) = 1 := by
    rintro ⟨Q, hQp, hQl⟩
    obtain ⟨h1, h2, -⟩ := splitE_prime hirr χ q hl hq K hK Q
    rw [h1, h2]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  let g : q.asIdeal.primesOver (𝓞 K) → Prm K := fun Q =>
    have := Q.2.2
    ⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot Q.1⟩
  have hg : Function.Injective g := by
    intro Q1 Q2 h
    apply Subtype.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  have hset : {P : Prm K | under P = q ∧ Nrm P = Nrm q} = Set.range g := by
    ext P
    constructor
    · rintro ⟨hP, -⟩
      have hlo : P.asIdeal.LiesOver q.asIdeal := ⟨by rw [← hP, under_asIdeal]⟩
      exact ⟨⟨P.asIdeal, P.isPrime, hlo⟩, rfl⟩
    · rintro ⟨Q, rfl⟩
      have := Q.2.1
      have := Q.2.2
      refine ⟨?_, ?_⟩
      · ext1
        rw [under_asIdeal]
        exact (Ideal.over_def Q.1 q.asIdeal).symm
      · exact (splitE_prime hirr χ q hl hq K hK Q.1).2.2
  rw [hset, Set.ncard_range_of_injective hg, Nat.card_eq_fintype_card, hsum]

end

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitE_split_ext (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra E E') (k : ℕ), 2 ≤ k ∧
      ∀ q : Prm E, ¬ l ∣ Nrm q → χ ((Nrm q : ℕ) : ZMod l) = 1 →
        k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
  refine ⟨IntermediateField.fixedField (splitEH hirr χ), inferInstance, inferInstance, inferInstance,
    Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)), splitE_two_le hirr χ hχ, ?_⟩
  intro q hl hq
  exact splitE_count hirr χ q hl hq _
    (fun x σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ hσ)

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem power_series_diagonal_linear : S1 := by
  intro E _ _ l _ hirr
  obtain ⟨C, hC⟩ := PE_cyclotomicField_le_mul_Pcl_add_const E l hirr
  obtain ⟨CE, hE⟩ := chebyshev_log_bounded E
  obtain ⟨CM, hM⟩ := chebyshev_log_bounded (CyclotomicField l E)
  refine ⟨CE + CM + C, ?_⟩
  have hmem : Set.Ioc (1:ℝ) 2 ∈ 𝓝[>] (1:ℝ) := Ioc_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with s hs
  have h1 := hC s hs.1
  have h2 := (abs_le.mp (hE s hs)).2
  have h3 := (abs_le.mp (hM s hs)).1
  linarith

theorem chebyshev_split_estimate : S2 := by
  intro E _ _ l _ hirr χ hχ m hm
  by_contra H
  push Not at H
  obtain ⟨E', _, _, _, k, hk, hsplit⟩ := splitE_split_ext E l hirr χ hχ
  have hlp : l.Prime := Fact.out
  have hml : m * l ≠ 0 := mul_ne_zero hm hlp.ne_zero
  apply splitC_not_almost_split E E' k hk
  refine (splitA_finite_not_coprime E (m * l) hml).subset ?_
  intro q hq
  simp only [Set.mem_ofPred_eq] at hq ⊢
  intro hcop
  apply hq
  apply hsplit q
  · intro hdvd
    have h1 : Nat.Coprime (Nrm q) l := Nat.Coprime.coprime_dvd_right (dvd_mul_left l m) hcop
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 h1.symm hdvd
  · exact H q hcop

end ReciprocityTheory.Cheb
end

section
open NumberField NumberField.Units Filter Topology Set

open scoped Classical

namespace ReciprocityTheory.Cheb

theorem summable_gfun {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) : Summable (gfun χ c s) := by
  have h1 := affine_proper_base_change.1 E (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l))
    (fun a => DirichletCharacter.norm_le_one χ _) s hs
  have h2 := affine_proper_base_change.1 E (fun a => if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0)
    (fun a => by split_ifs <;> simp [DirichletCharacter.norm_le_one]) s hs
  refine (h1.sub (h2.mul_left (Ideal.absNorm c.1 : ℂ))).congr fun a => ?_
  simp only [gfun]
  split_ifs <;> ring

theorem tsum_gfun {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) :
    ∑' a, gfun χ c s a = Lser E χ s * (1 - (Ideal.absNorm c.1 : ℂ) *
      (χ ((Ideal.absNorm c.1 : ℕ) : ZMod l) * ((Ideal.absNorm c.1 : ℕ) : ℂ) ^ (-(s : ℂ)))) := by
  have h1 := affine_proper_base_change.1 E (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l))
    (fun a => DirichletCharacter.norm_le_one χ _) s hs
  have h2 := affine_proper_base_change.1 E (fun a => if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0)
    (fun a => by split_ifs <;> simp [DirichletCharacter.norm_le_one]) s hs
  have hd := tsum_dvd_eq χ c hs
  have e : (fun a => gfun χ c s a) = fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) *
      ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) - (Ideal.absNorm c.1 : ℂ) *
      ((if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0) *
        ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) := by
    funext a; simp only [gfun]; split_ifs <;> ring
  have e2 : (fun a : NZIdeal E => (if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0) *
        ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) = fun a => if c.1 ∣ a.1 then
        χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) else 0 := by
    funext a; split_ifs <;> simp
  rw [e, h1.tsum_sub (h2.mul_left _), tsum_mul_left, e2, hd]
  simp only [Lser]
  ring

theorem k_holds : KProp := by
  intro E _ _ l _ hirr χ hχ
  choose b hb using fun C : ClassGroup (𝓞 E) => exists_cls_eq (E := E) C⁻¹
  have hM : (∏ C, Ideal.absNorm (b C).1) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (b C).2
  obtain ⟨q, hqcop, hqχ⟩ := chebyshev_split_estimate E l hirr χ hχ _ hM
  let c : NZIdeal E := ⟨q.asIdeal, q.ne_bot⟩
  have hcop : ∀ C, Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm (b C).1) := fun C =>
    Nat.Coprime.coprime_dvd_right (by
      rw [mul_comm l]
      exact Nat.mul_dvd_mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ C)) l) hqcop
  choose F hF hFeq using fun C => exists_class_cont χ (b C) c (hcop C)
  set n : ℕ := Ideal.absNorm c.1 with hn
  have hn0 : n ≠ 0 := by rw [hn, Ne, Ideal.absNorm_eq_zero_iff]; exact c.2
  set D : ℝ → ℂ := fun s => ∑ C, ((torsionOrder E : ℕ) : ℂ)⁻¹ *
    ((Ideal.absNorm (b C).1 : ℕ) : ℂ) ^ (s : ℂ) * F C s with hD
  set den : ℝ → ℂ := fun s => 1 - (n : ℂ) * (χ (n : ZMod l) * (n : ℂ) ^ (-(s : ℂ))) with hden
  have hid : ∀ s ∈ Ioc (1 : ℝ) 2, Lser E χ s * den s = D s := by
    intro s hs
    rw [hden, hD]
    dsimp only
    rw [hn, ← tsum_gfun χ c hs.1, tsum_eq_sum_cls _ (summable_gfun χ c hs.1)]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← hFeq C s hs (summable_gfun χ c hs.1)]
    congr 1; funext a
    rw [hb C, mul_inv_eq_one]
  have hDc : ContinuousOn D (Icc 1 2) := by
    refine continuousOn_finsetSum _ fun C _ => ?_
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (hF C)
    refine continuous_const.mul (Continuous.const_cpow Complex.continuous_ofReal (Or.inl ?_))
    have : Ideal.absNorm (b C).1 ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (b C).2
    exact_mod_cast this
  have hdenc : Continuous den := continuous_const.sub (continuous_const.mul (continuous_const.mul
    (Continuous.const_cpow Complex.continuous_ofReal.neg (Or.inl (by exact_mod_cast hn0)))))
  have hden1 : den 1 ≠ 0 := by
    rw [hden]
    dsimp only
    rw [Complex.ofReal_one, Complex.cpow_neg_one, mul_left_comm, mul_inv_cancel₀ (by exact_mod_cast hn0),
      mul_one, sub_ne_zero]
    exact fun h => hqχ h.symm
  refine ⟨D 1 / den 1, ?_⟩
  have hcw : ContinuousWithinAt (fun s => D s / den s) (Icc 1 2) 1 :=
    (hDc 1 ⟨le_rfl, by norm_num⟩).div hdenc.continuousWithinAt hden1
  have ht : Tendsto (fun s => D s / den s) (𝓝[>] 1) (𝓝 (D 1 / den 1)) :=
    (hcw.mono_of_mem_nhdsWithin (mem_of_superset (Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2))
      Ioc_subset_Icc_self)).tendsto
  refine ht.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2),
    nhdsWithin_le_nhds (hdenc.continuousAt.eventually_ne hden1)] with s hs hs0
  rw [div_eq_iff hs0, hid s hs]

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

section

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem cyc_re_psum_upper (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (hK : KProp)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), χ ≠ 1 → (Psum E χ s).re ≤ C := by
  by_cases hχ : χ = 1
  · exact ⟨0, Eventually.of_forall fun _ h => absurd hχ h⟩
  obtain ⟨L1, hL⟩ := hK E l hirr χ hχ
  obtain ⟨C3, hC3⟩ := h3a E l χ
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖Lser E χ s‖ < ‖L1‖ + 1 :=
    ((continuous_norm.tendsto L1).comp hL).eventually (gt_mem_nhds (by linarith))
  refine ⟨Real.log (‖L1‖ + 1) + C3, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s hs (hs1 : 1 < s) _
  have he : Complex.exp (abelian₂ E χ s) = Lser E χ s := h2 E l χ s hs1
  have hre : Real.exp (abelian₂ E χ s).re < ‖L1‖ + 1 := by rw [← Complex.norm_exp, he]; exact hs
  have hlam : (abelian₂ E χ s).re < Real.log (‖L1‖ + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]; exact hre
  have hd : |(abelian₂ E χ s - Psum E χ s).re| ≤ C3 := (Complex.abs_re_le_norm _).trans (hC3 s hs1)
  rw [Complex.sub_re] at hd
  linarith [(abs_le.mp hd).1]

theorem cyc_re_psum_lower (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), -C ≤ (Psum E χ s).re := by
  choose C hC using fun χ' => cyc_re_psum_upper (E := E) h2 h3a hK hirr χ'
  obtain ⟨C1, hC1⟩ := hS1 E l hirr
  refine ⟨|C1| + ∑ χ' : DirichletCharacter ℂ l, |C χ'|, ?_⟩
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ', χ' ≠ 1 → (Psum E χ' s).re ≤ C χ' := eventually_all.2 hC
  filter_upwards [hall, hC1, self_mem_nhdsWithin] with s hs hs1 (hgt : 1 < s)
  have hS := h1.2.2 E s hgt
  have ho := psum_orth (E := E) l (1 : (ZMod l)ˣ) s hS
  simp only [inv_one, Units.val_one, map_one, one_mul] at ho
  have hore : ∑ χ' : DirichletCharacter ℂ l, (Psum E χ' s).re = (Nat.totient l : ℝ) * Pcl E l 1 s := by
    have := congrArg Complex.re ho
    rw [Complex.re_sum] at this
    rw [this]; simp
  have htot : (Nat.totient l : ℝ) = ((l - 1 : ℕ) : ℝ) := by rw [Nat.totient_prime Fact.out]
  have hP := pcl_nonneg (E := E) l 1 s
  have h1le : (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| := by
    have := re_psum_one_le (E := E) l s hS
    rw [htot]; linarith [le_abs_self C1]
  have hbd : ∀ χ', (Psum E χ' s).re ≤
      |C χ'| + (if χ' = 1 then (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| else 0) := by
    intro χ'
    split_ifs with h
    · subst h; linarith [abs_nonneg (C 1)]
    · linarith [hs χ' h, le_abs_self (C χ')]
  have hsplit := Finset.add_sum_erase Finset.univ (fun χ' => (Psum E χ' s).re) (Finset.mem_univ χ)
  have herase : ∑ χ' ∈ Finset.univ.erase χ, (Psum E χ' s).re ≤
      ∑ χ' : DirichletCharacter ℂ l, (|C χ'| + (if χ' = 1 then (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| else 0)) := by
    refine (Finset.sum_le_sum fun χ' _ => hbd χ').trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro χ' _ _
    have := mul_nonneg (Nat.cast_nonneg (Nat.totient l) : (0 : ℝ) ≤ _) hP
    split_ifs
    · linarith [abs_nonneg (C χ'), abs_nonneg C1]
    · simp
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ l)] at herase
  simp only [Finset.mem_univ, if_true] at herase
  linarith

end

section

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem cyc_psum_bdd (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ B : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖Psum E χ s‖ ≤ B := by
  obtain ⟨L1, hL⟩ := hK E l hirr χ hχ
  obtain ⟨C, hC⟩ := cyc_re_psum_lower (E := E) h1 h2 h3a hK hS1 hirr χ
  obtain ⟨C3, hC3⟩ := h3a E l χ
  have hlow : ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.exp (-(C + C3)) ≤ ‖Lser E χ s‖ := by
    filter_upwards [hC, self_mem_nhdsWithin] with s hs (hgt : 1 < s)
    rw [← h2 E l χ s hgt, Complex.norm_exp]
    apply Real.exp_le_exp.2
    have hd : |(abelian₂ E χ s - Psum E χ s).re| ≤ C3 := (Complex.abs_re_le_norm _).trans (hC3 s hgt)
    rw [Complex.sub_re] at hd
    linarith [(abs_le.mp hd).1]
  have hL0 : L1 ≠ 0 := by
    have := ge_of_tendsto ((continuous_norm.tendsto L1).comp hL) hlow
    intro h0
    rw [h0, norm_zero] at this
    exact absurd this (not_le.2 (Real.exp_pos _))
  have hexp : Tendsto (fun s => Complex.exp (abelian₂ E χ s)) (𝓝[>] 1) (𝓝 L1) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    exact (h2 E l χ s hs).symm
  obtain ⟨B, hB⟩ := bdd_of_exp_tendsto _ (h3c E l χ) L1 hL0 hexp
  refine ⟨B + C3, ?_⟩
  filter_upwards [hB, self_mem_nhdsWithin] with s hs (hgt : 1 < s)
  have := hC3 s hgt
  calc ‖Psum E χ s‖ = ‖abelian₂ E χ s - (abelian₂ E χ s - Psum E χ s)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖abelian₂ E χ s‖ + ‖abelian₂ E χ s - Psum E χ s‖ := norm_sub_le _ _
    _ ≤ B + C3 := by linarith

theorem tendsto_log_one_div_sub_one :
    Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] 1) atTop := by
  have h0 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_sub_right 1).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      simpa using hs
  exact (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h0)).congr
    (fun s => by simp only [Function.comp_apply, one_div])

theorem cyc_pcl_large (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3b : faceMap_castSucc_comp_eq_succ) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (a : (ZMod l)ˣ) (X : ℝ) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), X ≤ Pcl E l (a : ZMod l) s := by
  have hB0 : ∀ χ : DirichletCharacter ℂ l, ∃ B : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), χ ≠ 1 → ‖Psum E χ s‖ ≤ B := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, Eventually.of_forall fun _ h => absurd hχ h⟩
    · obtain ⟨B, hB⟩ := cyc_psum_bdd (E := E) h1 h2 h3a h3c hK hS1 hirr χ hχ
      exact ⟨B, hB.mono fun _ h _ => h⟩
  choose B hB using hB0
  obtain ⟨C1, hC1⟩ := hS1 E l hirr
  obtain ⟨HighestWeightIntegral, hC3b⟩ := h3b E
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ, χ ≠ 1 → ‖Psum E χ s‖ ≤ B χ := eventually_all.2 hB
  set k : ℝ := ((l - 1 : ℕ) : ℝ) with hk
  set S : ℝ := ∑ χ : DirichletCharacter ℂ l, |B χ| with hSdef
  have hkpos : 0 < k := by
    have := (Fact.out : l.Prime).two_le
    rw [hk]; exact_mod_cast (by omega : 0 < l - 1)
  have hbig := tendsto_log_one_div_sub_one.eventually (eventually_ge_atTop (k * (k * X + S) + HighestWeightIntegral + C1))
  filter_upwards [hall, hC1, hbig, Ioc_mem_nhdsGT one_lt_two] with s hs hs1 hlog hsI
  have hgt : 1 < s := hsI.1
  have hS := h1.2.2 E s hgt
  have htot : (Nat.totient l : ℝ) = k := by rw [hk, Nat.totient_prime Fact.out]
  have ho := psum_orth (E := E) l a s hS
  have hore : ∑ χ : DirichletCharacter ℂ l, (χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s).re
      = k * Pcl E l (a : ZMod l) s := by
    have := congrArg Complex.re ho
    rw [Complex.re_sum] at this
    rw [this, ← htot]; simp
  have hterm : ∀ χ : DirichletCharacter ℂ l,
      (if χ = 1 then (Psum E (1 : DirichletCharacter ℂ l) s).re else 0) - |B χ|
        ≤ (χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s).re := by
    intro χ
    split_ifs with h
    · subst h
      rw [MulChar.one_apply_coe, one_mul]
      linarith [abs_nonneg (B 1)]
    · have h3 : ‖χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s‖ ≤ B χ := by
        rw [norm_mul]
        calc ‖χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l)‖ * ‖Psum E χ s‖ ≤ 1 * ‖Psum E χ s‖ :=
              mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
          _ ≤ B χ := by rw [one_mul]; exact hs χ h
      have := (abs_le.mp ((Complex.abs_re_le_norm _).trans h3)).1
      linarith [le_abs_self (B χ)]
  have hsum := Finset.sum_le_sum fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ l))) => hterm χ
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ l), hore] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hp1 := pcl_one_le_re_psum_one (E := E) l s hS
  have hpe : Real.log (1 / (s - 1)) - HighestWeightIntegral ≤ PE E s := by
    have := hC3b s hsI
    linarith [(abs_le.mp this).1]

  have hk1 : k * (k * X + S) ≤ k * Pcl E l 1 s := by linarith
  have hk2 : k * X + S ≤ Pcl E l 1 s := le_of_mul_le_mul_left hk1 hkpos
  have hk3 : k * X ≤ k * Pcl E l (a : ZMod l) s := by linarith
  exact le_of_mul_le_mul_left hk3 hkpos

theorem cyc_of (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3b : faceMap_castSucc_comp_eq_succ) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1) :
    CycStatement := by
  intro E _ _ l _ hirr a T
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hbad : ∀ q : Prm E, (Nrm q).Prime → Nrm q ∉ T → ((Nrm q : ℕ) : ZMod l) ≠ a :=
    fun q hp hT => hno q.asIdeal q.isPrime hp hT
  let g : Prm E → ℝ := fun q => (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) +
    Set.indicator {q | Nrm q ∈ T} (fun _ => (1 : ℝ)) q
  have hg : Summable g :=
    summable_nonprime_norm.add (summable_of_hasFiniteSupport ((finite_norm_mem T).subset Set.support_indicator_subset))
  have hle : ∀ s : ℝ, 1 < s → Pcl E l (a : ZMod l) s ≤ ∑' q, g q := by
    intro s hs
    have hS := h1.2.2 E s hs
    have hterm : ∀ q : Prm E, (if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) ≤ g q := by
      intro q
      have h2q := two_le_nrm q
      have hN1 : (1 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Nrm q)
      have hpow1 : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hpow2 : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      have hind0 : 0 ≤ Set.indicator {q : Prm E | Nrm q ∈ T} (fun _ => (1 : ℝ)) q :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) q
      have hinv0 : 0 ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by positivity
      simp only [g]
      by_cases hc : ((Nrm q : ℕ) : ZMod l) = a
      · rw [if_pos hc]
        by_cases hp : (Nrm q).Prime
        · have hT : Nrm q ∈ T := by
            by_contra hT; exact hbad q hp hT hc
          rw [if_pos hp, Set.indicator_of_mem (show q ∈ {q : Prm E | Nrm q ∈ T} from hT)]
          linarith
        · rw [if_neg hp]; linarith
      · rw [if_neg hc]
        split_ifs <;> linarith
    have hP : Summable (fun q : Prm E =>
        if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
      refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS
      · split_ifs
        · positivity
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · positivity
    exact Summable.tsum_le_tsum hterm hP hg
  obtain ⟨s, hs, hs1⟩ := ((cyc_pcl_large (E := E) h1 h2 h3a h3b h3c hK hS1 hirr a (∑' q, g q + 1)).and
    self_mem_nhdsWithin).exists
  linarith [hle s hs1]

end

theorem cyc_holds : CycStatement :=
  cyc_of affine_proper_base_change proper_base_change casimirPower_surjective_symmetric chebyshev_log_bounded smoothMap_seminorm_bound k_holds power_series_diagonal_linear

end ReciprocityTheory.Cheb
end
