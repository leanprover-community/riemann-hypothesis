import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCharpolyRootLift
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormPullbackX
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullGradedAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomCharpoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBadPrimesFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormGoodPrimeIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPrimeBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegreeInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomNormPIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartPrimePowerInverse

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegreeInt

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isWeightedHomogeneous_of_isMultiHomog {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k

theorem isMultiHomog_of_isWeightedHomogeneous {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]

theorem mConeMap_eq (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMap y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem coeff_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) (n : K → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm n) (mConeMap y f) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMap_eq y hm, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]

omit [DecidableEq K] in

theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℤ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRing ι) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegreeInt.Statement := by
  classical
  intro K _ ι _ Ω _ y D e L N M hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩
  have hg' := isWeightedHomogeneous_of_isMultiHomog hg

  have hgI : (M : MRing ι) * g ∈ coneNullIdealZ y L := by
    rw [g.as_sum, Finset.mul_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (coeff μ g)
    exact Ideal.mem_of_dvd _ (mul_dvd_mul_left _ hc) (hN c)
  have hI : coneNullIdealZ y L = RingHom.ker (mConeMap y) ⊔ Ideal.span (Set.range L) := by
    rw [coneNullIdealZ, Ideal.span_union, Ideal.span_eq]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMap y (L j) = monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    rw [mConeMap_eq y (isWeightedHomogeneous_of_isMultiHomog (hL j)), PullConeDegree.prod_X_pow_eq_monomial,
      C_mul_monomial, mul_one]
  have hMg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) ((M : MRing ι) * g) d := by
    have h := (isWeightedHomogeneous_C (NumbersDVR.blockWeight ι) (M : ℤ)).mul hg'
    rw [zero_add, map_natCast] at h
    exact h
  have hψg : mConeMap y ((M : MRing ι) * g) =
      ∑ j, mConeMap y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    rw [← huv, map_add, RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMap_eq y hMg, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum, map_mul, map_natCast] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMap]

end PullConeDegreeInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullSectionIntegralInt

theorem aeval_mem_of_forall {σ Ω : Type} [Field Ω] (V : Subring Ω) (y' : σ → Ω) (hy : ∀ p, y' p ∈ V)
    (b : MvPolynomial σ ℤ) : aeval y' b ∈ V := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add]; exact V.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact V.mul_mem hp (hy i)

theorem proof : PullSectionIntegralInt.Statement := by
  intro K _ ι _ Ω _ y D e L q N M hrel he hL hM hdeg τ s hs j hj
  classical
  set ℓ := aeval y (L j)
  set B := Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => aeval y (L i) / ℓ))
  set R := (integralClosure B Ω).toSubring
  have : IsIntegrallyClosedIn R Ω := inferInstanceAs (IsIntegrallyClosedIn (integralClosure B Ω) Ω)
  show s / ℓ ^ (q * τ) ∈ R
  by_contra hnot
  obtain ⟨V, hRV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot
  have hBV : ∀ x ∈ B, x ∈ V := fun x hx =>
    hRV (isIntegral_algebraMap (R := B) (A := Ω) (x := ⟨x, hx⟩))

  have hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩) := by
    intro k
    obtain ⟨i0, -⟩ := hrel k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
      ⟨i0, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i0, hi0⟩ := hrel k
    have := hc k i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  have hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V := by
    intro p
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc p.1 p.2) zero_le

  set Mc : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
  have hMc0 : Mc ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  have hchart : (chartRingZ y c : Set Ω) ⊆ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hratio p
    | algebraMap r => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have : IsIntegrallyClosedIn V.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn V Ω)
  have hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring :=
    (Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr
      (fun r => hchart r.2) (hs c hc0)
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (Mc ^ (q * τ))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul]
  rw [hprod] at hxV

  set w := N * ∑ k, Fintype.card (ι k)
  have hd : ∀ k, e k + N * Fintype.card (ι k) ≤ ((w + 1) • e) k := by
    intro k
    have h1 : Fintype.card (ι k) ≤ ∑ k, Fintype.card (ι k) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : N * Fintype.card (ι k) ≤ w := Nat.mul_le_mul_left N h1
    have h3 : w ≤ w * e k := Nat.le_mul_of_pos_right w (he k)
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  obtain ⟨a, ha, hrelM⟩ := hdeg ((w + 1) • e) (xpow c ((w + 1) • e)) (isMultiHomog_xpow c _) hd
  have ha' : ∀ i, IsMultiHomog (a i) (fun k => w * e k) := by
    intro i
    convert ha i using 1
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_mul, one_mul, Nat.add_sub_cancel]
  have hg : aeval y (xpow c ((w + 1) • e)) = Mc ^ (w + 1) := by
    simp only [xpow, map_prod, map_pow, aeval_X, Mc, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have hscale : ∀ i, aeval (fun p => t p.1 * y p) (a i) = (Mc ^ w)⁻¹ * aeval y (a i) := by
    intro i
    rw [PullSectionIntegral.aeval_scale_of_isMultiHomog y t (ha' i)]
    congr 1
    simp only [Mc, t, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← pow_mul, mul_comm]

  have hsum : Mc / ℓ = (M : Ω)⁻¹ * ∑ i, aeval (fun p => t p.1 * y p) (a i) * (aeval y (L i) / ℓ) := by
    have : ∑ i, aeval (fun p => t p.1 * y p) (a i) * (aeval y (L i) / ℓ) =
        (Mc ^ w)⁻¹ * (∑ i, aeval y (a i) * aeval y (L i)) / ℓ := by
      simp only [hscale, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, ← hrelM, hg]
    field_simp
    ring
  have hMV : Mc / ℓ ∈ V := by
    rw [hsum]
    refine mul_mem (hBV _ (Algebra.subset_adjoin (Set.mem_insert _ _))) (sum_mem fun i _ => mul_mem ?_ ?_)
    · exact aeval_mem_of_forall V.toSubring _ (fun p => by simpa [t, div_eq_inv_mul] using hratio p) (a i)
    · exact hBV _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  apply htV
  have hMn : Mc ^ (q * τ) ≠ 0 := pow_ne_zero _ hMc0
  have : s / ℓ ^ (q * τ) = s * (Mc ^ (q * τ))⁻¹ * (Mc / ℓ) ^ (q * τ) := by
    rw [div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]
  rw [this]
  exact mul_mem hxV (pow_mem hMV _)

end PullSectionIntegralInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem aeval_mul_blockScale_of_isMultiHomog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [CommRing Ω] {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (t : K → Ω)
    (y : (Σ k, ι k) → Ω) :
    aeval (fun p => y p * t p.1) f = aeval y f * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ x, t k ^ d ⟨k, x⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal {K : Type*} [Fintype K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω] {y : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) (t : K → Ω) : aeval (fun p => y p * t p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have hcomp : ((aeval t).restrictScalars ℤ).comp (mConeMap y) = aeval (fun p => y p * t p.1) :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  rw [← hcomp, AlgHom.comp_apply, h0, map_zero]

theorem ChartPrimePowerInverse.proof : ChartPrimePowerInverse.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L hhom hL p hp j hj
  obtain ⟨N, hN⟩ := PullConeNull.proof K ι Ω y D L hL
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have key : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ a : ℕ,
      (p : Ω) ^ a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro c hc
    set R := Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) with hR
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hYdef
    have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have hpR : ∀ n : ℕ, (p : Ω) ^ n ∈ R := fun n => R.pow_mem (natCast_mem R p) n

    let G : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ a : ℕ, (p : Ω) ^ a * x ∈ R}
        mul_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x * z) = ((p : Ω) ^ a * x) * ((p : Ω) ^ b * z) := by ring
          rw [this]
          exact R.mul_mem ha hb
        add_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x + z) = (p : Ω) ^ b * ((p : Ω) ^ a * x) + (p : Ω) ^ a * ((p : Ω) ^ b * z) := by
            ring
          rw [this]
          exact R.add_mem (R.mul_mem (hpR b) ha) (R.mul_mem (hpR a) hb)
        algebraMap_mem' := by
          intro q
          obtain ⟨b, d', hd', hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.one_lt.ne'
          refine ⟨b, ?_⟩
          have hden' : (q.den : Ω) = (p : Ω) ^ b * (d' : Ω) := by exact_mod_cast hden
          have hd0 : (d' : Ω) ≠ 0 := by
            intro h0
            have : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
            rw [hden', h0, mul_zero] at this
            exact this rfl
          have : (p : Ω) ^ b * algebraMap ℚ Ω q = (q.num : Ω) * (d' : Ω)⁻¹ := by
            rw [eq_ratCast, Rat.cast_def, hden']
            field_simp
          show (p : Ω) ^ b * algebraMap ℚ Ω q ∈ R
          rw [this]
          exact R.mul_mem (intCast_mem R _) (Subring.subset_closure (Or.inr ⟨d', hd', rfl⟩)) }
    have hmemG : ∀ x ∈ R, x ∈ G := fun x hx => ⟨0, by simpa using hx⟩
    let r : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, c q.1⟩
    let χ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval r
    let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
    have hχG : ∀ g, χ g ∈ G := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C q => simpa [χ] using G.algebraMap_mem q
      | add f g hf hg => simpa using G.add_mem hf hg
      | mul_X f q hf =>
        simpa [χ] using G.mul_mem hf (hmemG _ (Subring.subset_closure (Or.inl (Or.inl ⟨q, rfl⟩))))
    have hχmap : ∀ f : MRing ι,
        χ (map (Int.castRingHom ℚ) f) = aeval (fun q => y q * t q.1) f := by
      intro f
      rw [← algebraMap_int_eq, aeval_map_algebraMap]
      simp only [r, t, div_eq_mul_inv]

    let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) :=
      { carrier := {f | χ f * (Y / aeval y (L j)) ∈ G}
        add_mem' := by
          intro f g hf hg
          simpa [add_mul] using G.add_mem hf hg
        zero_mem' := by simp
        smul_mem' := by
          intro g f hf
          simpa [smul_eq_mul, mul_assoc] using G.mul_mem (hχG g) hf }
    have hIJ : coneNullIdeal y L ≤ J := by
      refine Ideal.span_le.mpr ?_
      rintro f (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal hf t, zero_mul]
        exact G.zero_mem
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_of_isMultiHomog (hhom i) t]
        have : aeval y (L i) * (∏ k, t k ^ e k) * (Y / aeval y (L j)) =
            aeval y (L i) / aeval y (L j) := by
          have hprod : (∏ k, t k ^ e k) = Y⁻¹ := by
            rw [hYdef, ← Finset.prod_inv_distrib]
            exact Finset.prod_congr rfl fun k _ => inv_pow _ _
          rw [hprod]
          field_simp
        rw [this]
        exact hmemG _ (Subring.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩)))
    have h1 := hIJ (hN c)
    have hone : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) = 1 := by
      simp [χ, r, div_self (hc _)]
    obtain ⟨a, ha⟩ : Y / aeval y (L j) ∈ G := by
      have : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) * (Y / aeval y (L j)) ∈ G := h1
      rwa [hone, one_mul] at this
    exact ⟨a, by rw [mul_div_assoc]; exact ha⟩
  choose! a ha using key
  refine ⟨Finset.univ.sup a, fun c hc => ?_⟩
  have hle : a c ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ c)
  have e1 : (p : Ω) ^ Finset.univ.sup a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) =
      (p : Ω) ^ (Finset.univ.sup a - a c) * ((p : Ω) ^ a c * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j)) := by
    rw [← Nat.sub_add_cancel hle, pow_add, Nat.add_sub_cancel]
    ring
  rw [e1]
  exact Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _) (ha c hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem FibreNormDehomRoots.full : FibreNormDehomRoots.Statement :=
  FibreNormDehomRoots.proof
    (PullFormsGeneric.proof
      (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof))
    PullSectionIntegral.proof CharpolyRootLift.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
