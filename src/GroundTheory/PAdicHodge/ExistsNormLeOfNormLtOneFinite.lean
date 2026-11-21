import Mathlib
import GroundTheory.PAdicHodge.WAKummerEps
import GroundTheory.PAdicHodge.FundamentalSeqBCris
import GroundTheory.PAdicHodge.BCrisRegularFinal

section
set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

namespace ACris

section General

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}



variable [CharZero K]

theorem span_p_le_comap_theta : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta K p) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

theorem thetaAway_dpow_eq (n : ℕ) (x : AInf K p) :
    thetaAway K p (dpow n x) = ((θ x : 𝒪) : K) ^ n / (n.factorial : K) := by
  have h := congrArg (thetaAway K p) (factorial_mul_dpow n x)
  rw [map_mul, map_natCast, map_pow, thetaAway_algebraMap] at h
  rw [eq_div_iff (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), mul_comm, h]

theorem coe_theta_logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) :
    ((theta K p (logTermJA hx n) : 𝒪) : K) = (-1) ^ n * ((θ x : 𝒪) : K) ^ (n + 1) / ((n + 1 : ℕ) : K) := by
  rw [logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, theta_of,
    coe_thetaZero, coe_logTermJ, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
    thetaAway_dpow_eq, Nat.factorial_succ, Nat.cast_mul]
  have h1 : ((n.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h2 : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 n.succ_ne_zero
  field_simp

theorem theta_logJ_congr {x y : AInf K p} (hx : x ∈ pdIdeal K p) (hy : y ∈ pdIdeal K p)
    (h : θ x = θ y) : theta K p (logJ hx) = theta K p (logJ hy) := by
  have h1 := (isAdicSum_logJ hx).map (theta K p) span_p_le_comap_theta
  have h2 := (isAdicSum_logJ hy).map (theta K p) span_p_le_comap_theta
  refine h1.unique (h2.congr fun n => Subtype.ext ?_)
  rw [coe_theta_logTermJA, coe_theta_logTermJA, h]



theorem mk_logTermJ_add_sub {x δ : AInf K p} (hx : x ∈ pdIdeal K p) (hδ : δ ∈ RingHom.ker θ)
    (hz : x + δ ∈ pdIdeal K p) (n : ℕ) :
    Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hz n : 𝔸) -
        Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hx n : 𝔸) =
      Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 ((-x) ^ n * δ)) := by
  have hS : Ideal.Quotient.mk (kerAway K p ^ 2)
      (∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k hk => by
      rw [map_mul, mk_dpow_eq_zero hδ (by have := Finset.mem_range.1 hk; omega), mul_zero]
  rw [← map_sub, coe_logTermJ, coe_logTermJ, dpow_add, Finset.sum_range_succ, Finset.sum_range_succ,
    Nat.add_sub_cancel_left, Nat.sub_self, dpow_zero, dpow_one]
  have e : (-1) ^ n * (n.factorial : 𝔸) * (∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ +
      dpow n x * algebraMap (AInf K p) 𝔸 δ + dpow (n + 1) x * 1) -
      (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) x =
      (-1) ^ n * (n.factorial : 𝔸) * ∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ +
        algebraMap (AInf K p) 𝔸 ((-x) ^ n * δ) := by
    rw [map_mul, map_pow, map_neg, neg_pow (algebraMap (AInf K p) 𝔸 x), ← factorial_mul_dpow]
    ring
  rw [e, map_add, map_mul, hS, mul_zero, zero_add]

theorem mk_sum_logTermJ_mul_sub {x k : AInf K p} (hx : x ∈ pdIdeal K p) (hk : k ∈ RingHom.ker θ)
    (hz : x + (1 + x) * k ∈ pdIdeal K p) (N : ℕ) :
    ∑ n ∈ Finset.range N, (Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hz n : 𝔸) -
        Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hx n : 𝔸)) =
      Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 (k - k * (-x) ^ N)) := by
  have hδ : (1 + x) * k ∈ RingHom.ker θ := Ideal.mul_mem_left _ _ hk
  rw [Finset.sum_congr rfl fun n _ => mk_logTermJ_add_sub hx hδ hz n, ← map_sum, ← map_sum]
  congr 2
  have h := mul_neg_geom_sum (-x) N
  rw [← Finset.sum_mul]
  linear_combination k * h

set_option maxHeartbeats 2000000 in

theorem iotaQ_logJ_mul_sub {x k : AInf K p} (hx : x ∈ pdIdeal K p) (hk : k ∈ RingHom.ker θ)
    (hz : x + (1 + x) * k ∈ pdIdeal K p) :
    iotaQ K p 2 (logJ hz) - iotaQ K p 2 (logJ hx) =
      Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 k) := by
  have hle : 𝔭 ≤ (Ideal.span {(p : acrisQ K p 2)}).comap (embedding₂ K p 2) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have hterm : ∀ {w : AInf K p} (hw : w ∈ pdIdeal K p) (n : ℕ),
      ((embedding₂ K p 2 (logTermJA hw n) : acrisQ K p 2) : 𝔸 ⧸ kerAway K p ^ 2) =
        Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hw n : 𝔸) := fun hw n => by
    rw [logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      iotaM_of, coe_iotaZero]
  have hs := ((isAdicSum_logJ hz).map (embedding₂ K p 2) hle).sub ((isAdicSum_logJ hx).map (embedding₂ K p 2) hle)
  have hkA : algebraMap (AInf K p) 𝔸 k ∈ ACrisZero K p := Subalgebra.algebraMap_mem _ k
  set tk : acrisQ K p 2 := ⟨Ideal.Quotient.mk _ (algebraMap (AInf K p) 𝔸 k), mk_mem_acrisQ 2 hkA⟩ with htk
  have hs' : IsAdicSum (Ideal.span {(p : acrisQ K p 2)})
      (fun n => embedding₂ K p 2 (logTermJA hz n) - embedding₂ K p 2 (logTermJA hx n)) tk := by
    intro j
    refine ⟨p * j, fun M hM => ?_⟩
    set w : ACrisZero K p := algebraMap (AInf K p) (ACrisZero K p) k * (-1) ^ M *
      (M.factorial : ACrisZero K p) * dpowJ hx M with hw
    have hwmem : w ∈ Ideal.span {(p : ACrisZero K p)} ^ j :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow (pow_dvd_factorial hM)))
    have hmem : iotaZero K p 2 w ∈ Ideal.span {(p : acrisQ K p 2)} ^ j :=
      (Ideal.le_comap_pow _ j) (Ideal.pow_right_mono (span_p_le_comap_iotaZero 2) j hwmem)
    convert hmem using 1
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum]
    simp only [AddSubgroupClass.coe_sub, hterm]
    rw [mk_sum_logTermJ_mul_sub hx hk hz M, coe_iotaZero, htk, ← map_sub]
    congr 1
    rw [hw, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_mul, coe_dpowJ]
    simp only [Subalgebra.coe_algebraMap, Subalgebra.coe_pow, Subalgebra.coe_neg,
      Subalgebra.coe_one, SubringClass.coe_natCast]
    rw [map_sub, map_mul, map_pow, map_neg, neg_pow (algebraMap (AInf K p) 𝔸 x), ← factorial_mul_dpow]
    ring
  have h := hs.unique hs'
  rw [iotaQ, RingHom.comp_apply, RingHom.comp_apply, ← map_sub, h]
  rfl

theorem iotaQ_two_log {k : AInf K p} (hk : k ∈ RingHom.ker θ) :
    iotaQ K p 2 (log hk) = Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 k) := by
  rw [iotaQ_log, Finset.sum_range_succ, Finset.sum_range_one, logTermZero, logTermZero]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one,
    SubringClass.coe_natCast, coe_dpowZero]
  rw [map_add, map_mul (Ideal.Quotient.mk (kerAway K p ^ 2)) _ (dpow (1 + 1) k),
    mk_dpow_eq_zero hk (show 2 ≤ 1 + 1 from le_refl _), mul_zero, add_zero, zero_add, dpow_one]
  simp

end General

section Cp

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "θ" => fontaineTheta (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}

section Galois

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem span_p_le_comap_galCris (σ : Gal(PadicAlgCl p/K)) : 𝔭 ≤ Ideal.comap (galCris σ) 𝔭 := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, galCris_natCast_p]
  exact Ideal.mem_span_singleton_self _

set_option maxHeartbeats 1600000 in

theorem gal_smul_logJ (σ : Gal(PadicAlgCl p/K)) {x : AInf ℂ_[p] p} (hx : x ∈ pdIdeal ℂ_[p] p)
    (hσx : σ • x ∈ pdIdeal ℂ_[p] p) : σ • logJ hx = logJ hσx := by
  rw [gal_smul_def]
  refine (logJ_eq_of_isAdicSum (((isAdicSum_logJ hx).map (galCris σ) (span_p_le_comap_galCris σ)).congr
    fun n => ?_)).symm
  rw [logTermJA, logTermJA, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, galCris_of]
  refine congrArg (AdicCompletion.of _ _) (Subtype.ext ?_)
  rw [gal_smul_zero_def, coe_galZero, coe_logTermJ, coe_logTermJ, map_mul, map_mul, map_pow, map_neg,
    map_one, map_natCast, galAway_dpow]

theorem gal_smul_mu (σ : Gal(PadicAlgCl p/K)) (x : 𝒪♭) :
    σ • AInf.mu (K := ℂ_[p]) x = AInf.mu (tiltGal σ x) := by
  rw [AInf.mu, AInf.mu, smul_sub, smul_one, AInf.gal_smul_teichmuller]

theorem untilt_tiltGal_sub_one_mem (σ : Gal(PadicAlgCl p/K)) {x : 𝒪♭}
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    PreTilt.untilt (tiltGal σ x) - 1 ∈ Ideal.span {(p : 𝒪)} := by
  rw [mem_span_singleton_iff_norm_le] at hx ⊢
  rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, AInf.coe_untilt_gal]
  have e : σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) - 1 = σ • (((PreTilt.untilt x : 𝒪) : ℂ_[p]) - 1) := by
    rw [smul_sub, smul_one]
  rw [e, ← galCp_apply, norm_galCp]
  simpa using hx

theorem gal_smul_logTeich (σ : Gal(PadicAlgCl p/K)) {x : 𝒪♭}
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    σ • logTeich hx = logTeich (untilt_tiltGal_sub_one_mem σ hx) := by
  have h := mu_mem_pdIdeal (K := ℂ_[p]) (untilt_tiltGal_sub_one_mem σ hx)
  rw [logTeich, logTeich, gal_smul_logJ σ (mu_mem_pdIdeal hx) (by rw [gal_smul_mu]; exact h)]
  exact logJ_congr (gal_smul_mu σ x) _ _

end Galois

theorem logTeich_congr {x y : 𝒪♭} (h : x = y) (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)})
    (hy : PreTilt.untilt y - 1 ∈ Ideal.span {(p : 𝒪)}) : logTeich (K := ℂ_[p]) hx = logTeich hy := by
  subst h; rfl

set_option maxHeartbeats 1600000 in

theorem exists_iota_eq_mul_fontaineT {D : ACris ℂ_[p] p} (hφ : phi ℂ_[p] p D = (p : ACris ℂ_[p] p) * D)
    (hθ : theta ℂ_[p] p D = 0) :
    ∃ q : ℚ_[p], iota ℂ_[p] p D =
      algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) q * fontaineT (epsilon p) (untilt_epsilon) := by
  set y := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) D with hy
  have hφy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ 1 * y := by
    rw [hy, phiPlus_algebraMap, hφ, pow_one, map_mul, map_natCast]
  have hιy : iotaPlus ℂ_[p] p y ∈ Ideal.span {fontaineT (epsilon p) (untilt_epsilon) ^ 1} := by
    rw [hy, iotaPlus_algebraMap, pow_one, ← maximalIdeal_eq_span_fontaineT untilt_epsilon
      untilt_frobeniusEquiv_symm_epsilon_ne_one, IsPerfectoidField.maximalIdeal_bDeRhamPlus,
      RingHom.mem_ker, thetaField_iota, hθ]
    rfl
  obtain ⟨q, hq⟩ := exists_eq_algebraMap_mul_pow_of_phiPlus_eq untilt_epsilon
    untilt_frobeniusEquiv_symm_epsilon_ne_one 1 hφy hιy
  refine ⟨q, ?_⟩
  have h := congrArg (iotaPlus ℂ_[p] p) hq
  rw [hy, iotaPlus_algebraMap, pow_one, map_mul, iotaPlus_algebraMap_padic] at h
  rw [h, periodTPlus, iotaPlus_algebraMap, iota_periodT]

omit hp in

theorem not_mem_maximalIdeal_sq_of_span_eq {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {t : R} (ht : maximalIdeal R = Ideal.span {t}) (ht0 : t ≠ 0) : t ∉ maximalIdeal R ^ 2 := by
  intro h
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨c, hc⟩ := h
  have h1 : t * (c * t) = t * 1 := by
    rw [mul_one]
    calc t * (c * t) = c * t ^ 2 := by ring
      _ = t := hc
  have h2 := mul_left_cancel₀ ht0 h1
  have htm : t ∈ maximalIdeal R := by rw [ht]; exact Ideal.mem_span_singleton_self t
  exact (IsLocalRing.mem_maximalIdeal t).1 htm ⟨⟨t, c, by rw [mul_comm]; exact h2, h2⟩, rfl⟩

set_option maxHeartbeats 3200000 in

theorem logTeich_mul_eq_add {x η : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)})
    (hη : PreTilt.untilt η = 1) (hxη : PreTilt.untilt (x * η) - 1 ∈ Ideal.span {(p : 𝒪)}) :
    logTeich (K := ℂ_[p]) hxη = logTeich hx + periodT hη := by
  set D := logTeich (K := ℂ_[p]) hxη - logTeich hx - periodT hη with hD
  have hmu : AInf.mu (K := ℂ_[p]) (x * η) = AInf.mu x + (1 + AInf.mu x) * AInf.mu η := by
    rw [AInf.mu, AInf.mu, AInf.mu, map_mul]; ring
  have hz : AInf.mu (K := ℂ_[p]) x + (1 + AInf.mu x) * AInf.mu η ∈ pdIdeal ℂ_[p] p :=
    hmu ▸ mu_mem_pdIdeal hxη

  have h2 : iotaQ ℂ_[p] p 2 D = 0 := by
    have h := iotaQ_logJ_mul_sub (mu_mem_pdIdeal hx) (mu_mem_ker hη) hz
    rw [hD, map_sub, map_sub, logTeich, logJ_congr hmu _ hz, logTeich, h, periodT, iotaQ_two_log,
      sub_self]

  have hφ : phi ℂ_[p] p D = (p : ACris ℂ_[p] p) * D := by
    rw [hD, map_sub, map_sub, phi_logTeich, phi_logTeich, phi_periodT_eq_mul]; ring
  have hθ : theta ℂ_[p] p D = 0 := by
    have hθμ : fontaineTheta (normInteger ℂ_[p]) p (AInf.mu (x * η)) =
        fontaineTheta (normInteger ℂ_[p]) p (AInf.mu x) := by
      rw [AInf.mu, AInf.mu, map_sub, map_sub, fontaineTheta_teichmuller, fontaineTheta_teichmuller,
        map_mul, hη, mul_one]
    rw [hD, map_sub, map_sub, logTeich, logTeich, theta_logJ_congr (mu_mem_pdIdeal hxη)
      (mu_mem_pdIdeal hx) hθμ, theta_periodT, sub_self, sub_zero]
  obtain ⟨q, hq⟩ := exists_iota_eq_mul_fontaineT hφ hθ

  have hm2 : iota ℂ_[p] p D ∈ maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) ^ 2 := by
    rw [← IsPerfectoidField.ker_evalB, RingHom.mem_ker]
    exact (evalₐ_iota 2 D).trans h2
  have hq0 : q = 0 := by
    by_contra hq0
    have hu : IsUnit (algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) q) :=
      (isUnit_iff_ne_zero.2 hq0).map _
    rw [hq, Ideal.unit_mul_mem_iff_mem _ hu] at hm2
    exact not_mem_maximalIdeal_sq_of_span_eq (maximalIdeal_eq_span_fontaineT untilt_epsilon
      untilt_frobeniusEquiv_symm_epsilon_ne_one)
      (fontaineT_ne_zero untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one) hm2
  have hD0 : D = 0 := iota_injective (by rw [hq, hq0, map_zero, zero_mul, map_zero])
  rw [hD] at hD0
  linear_combination hD0

theorem periodT_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) :
    periodT (untilt_epsPow hε a) = algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)
      (IsPerfectoidField.padicIntToWitt p a) * periodT hε := by
  apply iota_injective
  rw [iota_periodT, map_mul, iota_padicInt, iota_periodT, fontaineT_epsPow]

theorem gal_smul_logTeich_eq {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    {x : 𝒪♭} (hx0 : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]))
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) (σ : Gal(PadicAlgCl p/K)) :
    σ • logTeich hx = logTeich hx + algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)
      (IsPerfectoidField.padicIntToWitt p (kummerCocycle hε hζ hx0 hfix σ)) * periodT hε := by
  have e := tiltGal_eq_mul_epsPow hε hζ hx0 hfix σ
  have h1 : PreTilt.untilt (x * epsPow hε (kummerCocycle hε hζ hx0 hfix σ)) - 1 ∈
      Ideal.span {(p : 𝒪)} := e ▸ untilt_tiltGal_sub_one_mem σ hx
  rw [gal_smul_logTeich, logTeich_congr e _ h1, logTeich_mul_eq_add hx (untilt_epsPow hε _) h1,
    periodT_epsPow]

end Cp

end ACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_norm_le_of_norm_lt_one_finite (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : ∃ δ : ℝ, δ < 1 ∧ ∀ y ∈ K, ‖y‖ < 1 → ‖y‖ ≤ δ := by
  set D := Module.finrank ℚ_[p] K with hD
  have hD0 : 0 < D := Module.finrank_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpinv0 : 0 < (p : ℝ)⁻¹ := by positivity
  refine ⟨(p : ℝ)⁻¹ ^ (1 / (D : ℝ)), Real.rpow_lt_one hpinv0.le hpinv (by positivity),
    fun y hy hy1 => ?_⟩
  have hint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  have hmin : minpoly ℚ_[p] y = minpoly ℚ_[p] (⟨y, hy⟩ : K) :=
    minpoly.algHom_eq K.val Subtype.val_injective ⟨y, hy⟩
  have hdeg : (minpoly ℚ_[p] y).natDegree ≤ D := by
    rw [hmin]; exact minpoly.natDegree_le _
  have hd0 : 0 < (minpoly ℚ_[p] y).natDegree := minpoly.natDegree_pos hint
  have hnorm : ‖y‖ = ‖(minpoly ℚ_[p] y).coeff 0‖ ^ (1 / ((minpoly ℚ_[p] y).natDegree : ℝ)) := by
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow]
  set a := ‖(minpoly ℚ_[p] y).coeff 0‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hd0' : (0 : ℝ) < (minpoly ℚ_[p] y).natDegree := by exact_mod_cast hd0
  have ha1 : a < 1 := by
    by_contra h
    rw [not_lt] at h
    have := Real.one_le_rpow h (by positivity : (0 : ℝ) ≤ 1 / ((minpoly ℚ_[p] y).natDegree : ℝ))
    rw [← hnorm] at this
    linarith
  have hap : a ≤ (p : ℝ)⁻¹ := by
    have h := (Padic.norm_le_pow_iff_norm_lt_pow_add_one ((minpoly ℚ_[p] y).coeff 0) (-1)).2
      (by simpa using ha1)
    simpa [zpow_neg, zpow_one] using h
  rw [hnorm]
  calc a ^ (1 / ((minpoly ℚ_[p] y).natDegree : ℝ))
      ≤ (p : ℝ)⁻¹ ^ (1 / ((minpoly ℚ_[p] y).natDegree : ℝ)) :=
        Real.rpow_le_rpow ha0 hap (by positivity)
    _ ≤ (p : ℝ)⁻¹ ^ (1 / (D : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpinv0 hpinv.le
        apply one_div_le_one_div_of_le hd0'
        exact_mod_cast hdeg

theorem exists_sub_p_mul_eq_of_iterate_eq {R : Type*} [CommRing R] [Algebra ℚ_[p] R] (f : R →+* R)
    (hf : ∀ q : ℚ_[p], f (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q) {ν : R} {d : ℕ} (hd : 0 < d)
    (hν : f^[d] ν = ν) :
    ∃ a : R, f a - (p : R) * a = ν ∧
      ∀ g : R →+* R, (∀ q : ℚ_[p], g (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q) →
        (∀ x, g (f x) = f (g x)) → g ν = ν → g a = a := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  set A := algebraMap ℚ_[p] R with hA
  set q : ℚ_[p] := (p : ℚ_[p]) with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact_mod_cast hp.out.ne_zero
  have hne : q⁻¹ ^ e - q ≠ 0 := by
    intro h
    have h1 : q ^ (e + 1) = 1 := by
      have h' : q⁻¹ ^ e = q := sub_eq_zero.1 h
      calc q ^ (e + 1) = q ^ e * q := pow_succ q e
        _ = q ^ e * q⁻¹ ^ e := by rw [h']
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq0, one_pow]
    have h2 : ((p ^ (e + 1) : ℕ) : ℚ_[p]) = ((1 : ℕ) : ℚ_[p]) := by
      rw [Nat.cast_pow, Nat.cast_one]; exact h1
    have h3 := Nat.cast_injective h2
    have h4 : 1 < p ^ (e + 1) := Nat.one_lt_pow (Nat.succ_ne_zero e) hp.out.one_lt
    omega
  set c := (q⁻¹ ^ e - q)⁻¹ with hc
  have hpA : (p : R) = A q := by rw [hq, map_natCast]
  refine ⟨∑ k ∈ Finset.range (e + 1), A (c * q⁻¹ ^ k) * f^[k] ν, ?_, ?_⟩
  · have h1 : f (∑ k ∈ Finset.range (e + 1), A (c * q⁻¹ ^ k) * f^[k] ν) =
        ∑ k ∈ Finset.range e, A (c * q⁻¹ ^ k) * f^[k + 1] ν + A (c * q⁻¹ ^ e) * ν := by
      rw [map_sum, Finset.sum_range_succ]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by
          rw [map_mul, hf, ← Function.iterate_succ_apply' f]
      · rw [map_mul, hf, ← Function.iterate_succ_apply' f, hν]
    have h2 : (p : R) * ∑ k ∈ Finset.range (e + 1), A (c * q⁻¹ ^ k) * f^[k] ν =
        ∑ k ∈ Finset.range e, A (c * q⁻¹ ^ k) * f^[k + 1] ν + A (q * c) * ν := by
      rw [Finset.mul_sum, Finset.sum_range_succ']
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by
          rw [hpA, ← mul_assoc, ← map_mul]
          congr 2
          linear_combination (c * q⁻¹ ^ k) * mul_inv_cancel₀ hq0
      · rw [hpA, ← mul_assoc, ← map_mul, pow_zero, mul_one, Function.iterate_zero, id]
    rw [h1, h2, add_sub_add_left_eq_sub, ← sub_mul, ← map_sub, mul_comm q c, ← mul_sub,
      hc, inv_mul_cancel₀ hne, map_one, one_mul]
  · intro g hg hgf hgν
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hg]
    congr 1
    have : ∀ m, g (f^[m] ν) = f^[m] ν := by
      intro m
      induction m with
      | zero => exact hgν
      | succ m ih => rw [Function.iterate_succ_apply', hgf, ih]
    exact this k

theorem exists_iterate_eq_of_algebraic {R F : Type*} [CommRing R] [Field F] [Algebra ℚ_[p] R]
    [Algebra ℚ_[p] F] (ι : R →ₐ[ℚ_[p]] F) (hι : Function.Injective ι) (f : R →ₐ[ℚ_[p]] R) {μ : R}
    (hμ : IsAlgebraic ℚ_[p] (ι μ)) : ∃ n d, 0 < d ∧ f^[n + d] μ = f^[n] μ := by
  classical
  obtain ⟨P, hP0, hP⟩ := hμ
  have h0 : Polynomial.aeval μ P = 0 := hι (by rw [← Polynomial.aeval_algHom_apply, hP, map_zero])
  have hn : ∀ n, Polynomial.aeval (f^[n] μ) P = 0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => rw [Function.iterate_succ_apply', Polynomial.aeval_algHom_apply, ih, map_zero]
  have hmem : ∀ n, ι (f^[n] μ) ∈ (P.aroots F).toFinset := fun n => by
    rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
    exact ⟨hP0, by rw [Polynomial.aeval_algHom_apply, hn, map_zero]⟩
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨ι (f^[n] μ), hmem n⟩ : (P.aroots F).toFinset))
  have he' : f^[a] μ = f^[b] μ := hι (congrArg Subtype.val he)
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b - a, by omega, by rw [Nat.add_sub_cancel' h.le]; exact he'.symm⟩
  · exact ⟨b, a - b, by omega, by rw [Nat.add_sub_cancel' h.le]; exact he'⟩

theorem exists_eq_p_mul_of_sub_eq {R G : Type*} [CommRing R] [Algebra ℚ_[p] R] (f : R →+* R)
    (hf : ∀ q : ℚ_[p], f (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q) (g : G → R →+* R)
    (hg : ∀ σ q, g σ (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q)
    (hgf : ∀ σ x, g σ (f x) = f (g σ x)) {t : R} (ht : f t = (p : R) * t)
    (hper : ∀ μ : R, (∀ σ, g σ μ = μ) → ∃ n d, 0 < d ∧ f^[n + d] μ = f^[n] μ)
    (c : G → ℚ_[p]) {y : R} (hy : ∀ σ, g σ y - y = algebraMap ℚ_[p] R (c σ) * t) :
    ∃ y' : R, f y' = (p : R) * y' ∧ ∀ σ, g σ y' - y' = algebraMap ℚ_[p] R (c σ) * t := by
  set A := algebraMap ℚ_[p] R with hA
  have hpA : (p : R) = A (p : ℚ_[p]) := by rw [map_natCast]
  set μ := f y - (p : R) * y with hμdef
  have hμ : ∀ σ, g σ μ = μ := by
    intro σ
    have hgy : g σ y = y + A (c σ) * t := by rw [← hy σ]; ring
    rw [hμdef, map_sub, map_mul, map_natCast, hgf, hgy, map_add, map_mul, hf, ht]
    ring
  obtain ⟨n, d, hd, hnd⟩ := hper μ hμ
  have hit : ∀ m x, f^[m] x = (f ^ m) x := fun m x => by rw [RingHom.coe_pow]
  have hfA : ∀ m q, (f ^ m) (A q) = A q := by
    intro m q
    rw [← hit]
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hf]
  have hgit : ∀ σ m x, g σ ((f ^ m) x) = (f ^ m) (g σ x) := by
    intro σ m x
    rw [← hit, ← hit]
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', hgf, ih, Function.iterate_succ_apply']
  have hft : ∀ m, (f ^ m) t = (p : R) ^ m * t := by
    intro m
    rw [← hit]
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, ht, pow_succ]; ring
  set s : ℚ_[p] := ((p : ℚ_[p]) ^ n)⁻¹ with hs
  have hsp : A s * (p : R) ^ n = 1 := by
    rw [hpA, ← map_pow, ← map_mul, hs, inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)),
      map_one]
  set ν := A s * (f ^ n) μ with hνdef
  have hν : f^[d] ν = ν := by
    rw [hit d, hνdef, map_mul, hfA, ← hit n, ← hit d, ← Function.iterate_add_apply, add_comm d n, hnd,
      hit]
  obtain ⟨a, ha, hafix⟩ := exists_sub_p_mul_eq_of_iterate_eq f hf hd hν
  have hgν : ∀ σ, g σ ν = ν := fun σ => by rw [hνdef, map_mul, hg, hgit, hμ]
  have hga : ∀ σ, g σ a = a := fun σ => hafix (g σ) (hg σ) (hgf σ) (hgν σ)
  set T := A s * (f ^ n) y with hT
  refine ⟨T - a, ?_, fun σ => ?_⟩
  · have e1 : f ((f ^ n) y) = (f ^ (n + 1)) y := by rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    have e2 : (f ^ n) (f y) = (f ^ (n + 1)) y := by rw [pow_succ, RingHom.mul_def, RingHom.comp_apply]
    have hfT : f T - (p : R) * T = ν := by
      rw [hT, hνdef, hμdef, map_mul, hf, e1, map_sub, map_mul, map_natCast, e2]
      ring
    rw [map_sub]
    linear_combination hfT - ha
  · rw [map_sub, hga, hT, map_mul, hg, hgit]
    have hgy : g σ y = y + A (c σ) * t := by rw [← hy σ]; ring
    rw [hgy, map_add, map_mul, hfA, hft]
    linear_combination (A (c σ) * t) * hsp

section Span

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def thetaLogSet : Set (PadicAlgCl p) :=
  {s | s ∈ K ∧ ∃ (x : 𝒪♭) (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}), x ≠ 0 ∧
    (∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p])) ∧
    ((ACris.theta ℂ_[p] p (ACris.logTeich hx) : 𝒪) : ℂ_[p]) = ((s : PadicAlgCl p) : ℂ_[p])}

variable {K}

theorem gal_smul_theta_logTeich {x : 𝒪♭} (hx0 : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]))
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) (σ : Gal(PadicAlgCl p/K)) :
    σ • ((ACris.theta ℂ_[p] p (ACris.logTeich hx) : 𝒪) : ℂ_[p]) =
      ((ACris.theta ℂ_[p] p (ACris.logTeich hx) : 𝒪) : ℂ_[p]) := by
  rw [← ACris.theta_gal_smul, ACris.gal_smul_logTeich_eq untilt_epsilon
    untilt_frobeniusEquiv_symm_epsilon_ne_one hx0 hfix hx σ, map_add, map_mul, ACris.theta_periodT,
    mul_zero, add_zero]

theorem norm_natCast_padicAlgCl_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [norm_natCast_padicAlgCl hp.out.ne_zero, padicValNat_self, Nat.cast_one, zpow_neg, zpow_one]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem coe_padicAlgCl_eq (x : PadicAlgCl p) :
    ((x : PadicAlgCl p) : ℂ_[p]) = algebraMap (PadicAlgCl p) ℂ_[p] x := rfl

theorem exists_mem_span_thetaLogSet_add [FiniteDimensional ℚ_[p] K] {β : PadicAlgCl p} (hβ : β ∈ K)
    (hβ1 : ‖β‖ ≤ 1) : ∃ v ∈ Submodule.span ℚ_[p] (thetaLogSet K), ∃ β' ∈ K, ‖β'‖ ≤ 1 ∧
      β = v + (p : PadicAlgCl p) * β' := by
  set P : PadicAlgCl p := (p : PadicAlgCl p) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast hp.out.ne_zero
  have hP1 : ‖P‖ < 1 := norm_natCast_padicAlgCl_lt_one
  have hPK : P ∈ K := natCast_mem K p
  set y₀ : PadicAlgCl p := 1 + P ^ 2 * β with hy₀
  have hy₀K : y₀ ∈ K := add_mem (one_mem K) (mul_mem (pow_mem hPK 2) hβ)
  have hy₀1 : ‖y₀‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hP1.le) (norm_nonneg _) hβ1
  set X : 𝒪 := ⟨((y₀ : PadicAlgCl p) : ℂ_[p]), mem_normInteger.2 (by
    rw [UniformSpace.Completion.norm_coe]; exact hy₀1)⟩ with hX
  set c : 𝒪 := ⟨((β : PadicAlgCl p) : ℂ_[p]), mem_normInteger.2 (by
    rw [UniformSpace.Completion.norm_coe]; exact hβ1)⟩ with hc
  obtain ⟨x, hxX⟩ := ACris.exists_untilt_eq_of_cp X
  have hxc : PreTilt.untilt x - 1 = (p : 𝒪) ^ 2 * c := by
    rw [hxX]
    apply Subtype.ext
    simp only [hX, hc, hy₀, hP, AddSubgroupClass.coe_sub, OneMemClass.coe_one, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, SubringClass.coe_natCast, coe_padicAlgCl_eq, map_add, map_one, map_mul,
      map_pow, map_natCast]
    ring
  have hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)} := by
    rw [hxc, pow_two, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hx0 : x ≠ 0 := by
    intro h
    have h1 : ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = 0 := by
      rw [h, IsPerfectoidField.untilt_zero]; rfl
    rw [hxX, hX] at h1
    have h2 : y₀ = 0 := UniformSpace.Completion.coe_injective _ (by simpa using h1)
    have h3 : ‖P ^ 2 * β‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖P‖ ^ 2 * ‖β‖ ≤ ‖P‖ ^ 2 * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact pow_lt_one₀ (norm_nonneg _) hP1 two_ne_zero
    have h4 : P ^ 2 * β = -1 := by rw [hy₀] at h2; linear_combination h2
    rw [h4, norm_neg, norm_one] at h3
    exact lt_irrefl _ h3
  have hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]) := fun σ => by
    rw [hxX, hX]
    exact gal_smul_coe_of_mem σ ⟨y₀, hy₀K⟩
  obtain ⟨sK, hsK⟩ := exists_eq_coe_of_forall_smul_eq (gal_smul_theta_logTeich hx0 hfix hx)
  have hsS : (sK : PadicAlgCl p) ∈ thetaLogSet K := ⟨sK.2, x, hx, hx0, hfix, hsK.symm⟩
  have hr := ACris.theta_logTeich_sub_mem hx hxc
  rw [mem_span_singleton_iff_norm_le] at hr
  have hr' : ‖(sK : PadicAlgCl p) - P ^ 2 * β‖ ≤ ‖P‖ ^ 3 := by
    rw [← UniformSpace.Completion.norm_coe]
    have e : ((((sK : PadicAlgCl p) - P ^ 2 * β : PadicAlgCl p)) : ℂ_[p]) =
        (((ACris.theta ℂ_[p] p (ACris.logTeich hx) - (p : 𝒪) ^ 2 * c : 𝒪)) : ℂ_[p]) := by
      rw [AddSubgroupClass.coe_sub, ← hsK]
      simp only [hc, hP, MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast,
        coe_padicAlgCl_eq, map_sub, map_mul, map_pow, map_natCast]
    rw [e]
    refine hr.trans (le_of_eq ?_)
    rw [show (((p : 𝒪) ^ 3 : 𝒪) : ℂ_[p]) = ((P ^ 3 : PadicAlgCl p) : ℂ_[p]) by
      simp [hP, coe_padicAlgCl_eq], UniformSpace.Completion.norm_coe, norm_pow]
  refine ⟨((p : ℚ_[p]) ^ 2)⁻¹ • (sK : PadicAlgCl p),
    Submodule.smul_mem _ _ (Submodule.subset_span hsS),
    -(P ^ 3)⁻¹ * ((sK : PadicAlgCl p) - P ^ 2 * β), ?_, ?_, ?_⟩
  · exact mul_mem (neg_mem (inv_mem (pow_mem hPK 3))) (sub_mem sK.2 (mul_mem (pow_mem hPK 2) hβ))
  · rw [norm_mul, norm_neg, norm_inv, norm_pow]
    rw [inv_mul_le_iff₀ (pow_pos (norm_pos_iff.2 hP0) 3), mul_one]
    exact hr'
  · rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, ← hP]
    field_simp
    ring

theorem mem_span_thetaLogSet [FiniteDimensional ℚ_[p] K] {k : PadicAlgCl p} (hk : k ∈ K) :
    k ∈ Submodule.span ℚ_[p] (thetaLogSet K) := by
  set V := Submodule.span ℚ_[p] (thetaLogSet K) with hV
  have hfinK : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra) :=
    ‹FiniteDimensional ℚ_[p] K›
  have hVK : V ≤ Subalgebra.toSubmodule K.toSubalgebra :=
    Submodule.span_le.2 fun s hs => hs.1
  have hfinV : FiniteDimensional ℚ_[p] V := Submodule.finiteDimensional_of_le hVK
  have hVc : IsClosed (V : Set (PadicAlgCl p)) := Submodule.closed_of_finiteDimensional V
  set P : PadicAlgCl p := (p : PadicAlgCl p) with hP
  have hP1 : ‖P‖ < 1 := norm_natCast_padicAlgCl_lt_one
  have hPK : P ∈ K := natCast_mem K p
  have hPV : ∀ v ∈ V, P * v ∈ V := fun v hv => by
    have := Submodule.smul_mem V (p : ℚ_[p]) hv
    rwa [Algebra.smul_def, map_natCast] at this
  have hPnV : ∀ n : ℕ, ∀ v ∈ V, P ^ n * v ∈ V := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; rw [pow_succ', mul_assoc]; exact hPV _ (ih v hv)
  have hiter : ∀ n : ℕ, ∀ β ∈ K, ‖β‖ ≤ 1 → ∃ v ∈ V, ∃ β' ∈ K, ‖β'‖ ≤ 1 ∧ β = v + P ^ n * β' := by
    intro n
    induction n with
    | zero => exact fun β hβ hβ1 => ⟨0, V.zero_mem, β, hβ, hβ1, by simp⟩
    | succ n ih =>
      intro β hβ hβ1
      obtain ⟨v, hv, β', hβ', hβ'1, rfl⟩ := ih β hβ hβ1
      obtain ⟨v', hv', β'', hβ'', hβ''1, rfl⟩ := exists_mem_span_thetaLogSet_add hβ' hβ'1
      exact ⟨v + P ^ n * v', V.add_mem hv (hPnV n v' hv'), β'', hβ'', hβ''1, by ring⟩
  have hO : ∀ β ∈ K, ‖β‖ ≤ 1 → β ∈ V := by
    intro β hβ hβ1
    rw [← SetLike.mem_coe, ← hVc.closure_eq, Metric.mem_closure_iff]
    intro r hr
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hP1
    obtain ⟨v, hv, β', _, hβ'1, hβeq⟩ := hiter n β hβ hβ1
    refine ⟨v, hv, ?_⟩
    rw [dist_eq_norm, hβeq, add_sub_cancel_left, norm_mul, norm_pow]
    calc ‖P‖ ^ n * ‖β'‖ ≤ ‖P‖ ^ n * 1 := by gcongr
      _ < r := by rw [mul_one]; exact hn
  have hk0 : (0 : ℝ) < ‖k‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hk0) hP1
  have hk1 : ‖P ^ n * k‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    have h := mul_lt_mul_of_pos_right hn hk0
    rw [inv_mul_cancel₀ hk0.ne'] at h
    nlinarith [norm_nonneg k, pow_nonneg (norm_nonneg P) n]
  have hkV := hO _ (mul_mem (pow_mem hPK n) hk) hk1
  have hPn0 : P ^ n ≠ 0 := pow_ne_zero _ (by rw [hP]; exact_mod_cast hp.out.ne_zero)
  have h := V.smul_mem (((p : ℚ_[p]) ^ n)⁻¹) hkV
  rwa [Algebra.smul_def, map_inv₀, map_pow, map_natCast, ← hP, ← mul_assoc, inv_mul_cancel₀ hPn0,
    one_mul] at h

end Span

section Contradiction

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p)

local instance instNeZeroPowPrime' (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem gal_smul_untilt_iterate_of_eq_mul {ε x : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    {σ : Gal(PadicAlgCl p/K)} {a : ℤ_[p]} (h : tiltGal σ x = x * epsPow hε a) (m : ℕ) :
    σ • ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) *
      ((PreTilt.untilt (φi^[m] ε) : 𝒪) : ℂ_[p]) ^ (PadicInt.toZModPow m a).val := by
  rw [← coe_untilt_iterate_tiltGal, h, iterate_frobSymm_mul, map_mul, untilt_iterate_epsPow,
    MulMemClass.coe_mul, SubmonoidClass.coe_pow]

theorem norm_eq_one_of_sub_one_mem {x : 𝒪} (hx : x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    ‖((x : 𝒪) : ℂ_[p])‖ = 1 := by
  rw [mem_span_singleton_iff_norm_le] at hx
  have hp1 : ‖((p : 𝒪) : ℂ_[p])‖ < 1 := by
    simpa using IsPerfectoidField.norm_natCast_lt_one (K := ℂ_[p]) (p := p)
  have h1 : ‖((x : 𝒪) : ℂ_[p]) - 1‖ < 1 := by
    simpa using hx.trans_lt hp1
  have e : ((x : 𝒪) : ℂ_[p]) = 1 + (((x : 𝒪) : ℂ_[p]) - 1) := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h1.ne'), norm_one]
  exact max_eq_left h1.le

theorem norm_natCast_p_cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [show (p : ℂ_[p]) = ((p : PadicAlgCl p) : ℂ_[p]) by rw [coe_padicAlgCl_eq, map_natCast],
    UniformSpace.Completion.norm_coe, norm_natCast_padicAlgCl hp.out.ne_zero, padicValNat_self,
    Nat.cast_one, zpow_neg, zpow_one]

omit [Fact p.Prime] in
theorem norm_eq_one_of_pow_eq {E : Type*} [NormedField E] {z : E} {N : ℕ} (hN : N ≠ 0)
    (h : ‖z‖ ^ N = 1) : ‖z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg z) hN).1 h

set_option maxHeartbeats 1600000 in

theorem false_of_kummerC_eq [FiniteDimensional ℚ_[p] K] {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt (φi ε) ≠ 1) {n : ℕ} (f : Fin n → ℚ_[p]) (l : ℚ_[p]) (x : Fin n → 𝒪♭)
    (hx0 : ∀ i, x i ≠ 0)
    (hfix : ∀ i, ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt (x i) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (x i) : 𝒪) : ℂ_[p]))
    (hunit : ∀ i, ‖((PreTilt.untilt (x i) : 𝒪) : ℂ_[p])‖ = 1)
    (H : ∀ σ : Gal(PadicAlgCl p/K), (kummerC hε hζ σ : ℚ_[p]) =
      ∑ i, f i * (kummerCocycle hε hζ (hx0 i) (hfix i) σ : ℚ_[p]) +
        l * (((cycloChar K σ : ℤ_[p]) : ℚ_[p]) - 1)) : False := by

  have hpn : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  have hsc : ∀ q : ℚ_[p], ∃ e : ℕ, ∀ e' ≥ e, ‖(p : ℚ_[p]) ^ e' * q‖ ≤ 1 := by
    intro q
    obtain ⟨e, he⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by positivity : (0 : ℝ) < ‖q‖ + 1)) hpn
    refine ⟨e, fun e' he' => ?_⟩
    rw [norm_mul, norm_pow]
    have h1 : ‖(p : ℚ_[p])‖ ^ e' ≤ ‖(p : ℚ_[p])‖ ^ e :=
      pow_le_pow_of_le_one (norm_nonneg _) hpn.le he'
    have h2 := mul_lt_mul_of_pos_right he (by positivity : (0 : ℝ) < ‖q‖ + 1)
    rw [inv_mul_cancel₀ (by positivity)] at h2
    nlinarith [norm_nonneg q, pow_nonneg (norm_nonneg (p : ℚ_[p])) e']
  choose E hE using hsc
  set e : ℕ := ∑ i, E (f i) + E l with he
  have hef : ∀ i, ‖(p : ℚ_[p]) ^ e * f i‖ ≤ 1 := fun i => hE _ e (by
    have := Finset.single_le_sum (f := fun j => E (f j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega)
  have hel : ‖(p : ℚ_[p]) ^ e * l‖ ≤ 1 := hE _ e (by omega)
  set μ : Fin n → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ e * f i, hef i⟩ with hμ
  set ν : ℤ_[p] := ⟨(p : ℚ_[p]) ^ e * l, hel⟩ with hν
  set κ : Fin n → Gal(PadicAlgCl p/K) → ℤ_[p] := fun i => kummerCocycle hε hζ (hx0 i) (hfix i) with hκ
  have HZ : ∀ σ : Gal(PadicAlgCl p/K), (p : ℤ_[p]) ^ e * kummerC hε hζ σ + ν =
      ∑ i, μ i * κ i σ + ν * (cycloChar K σ : ℤ_[p]) := by
    intro σ
    apply PadicInt.ext
    have hs : ∑ i, ((μ i * κ i σ : ℤ_[p]) : ℚ_[p]) =
        ∑ i, (p : ℚ_[p]) ^ e * (f i * (κ i σ : ℚ_[p])) :=
      Finset.sum_congr rfl fun i _ => by rw [PadicInt.coe_mul]; ring
    have hνc : (ν : ℚ_[p]) = (p : ℚ_[p]) ^ e * l := rfl
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, H σ,
      PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_sum, hs, hνc, ← Finset.mul_sum]
    ring

  obtain ⟨δ, hδ1, hδ⟩ := exists_norm_le_of_norm_lt_one_finite K

  have hlevel : ∀ m : ℕ, ((p : ℝ)⁻¹) ^ p ^ e ≤ δ ^ p ^ m := by
    intro m
    set ζ : ℂ_[p] := ((PreTilt.untilt (φi^[m] ε) : 𝒪) : ℂ_[p]) with hζdef
    set π : ℂ_[p] := ((PreTilt.untilt (φi^[m] (pFlat p)) : 𝒪) : ℂ_[p]) with hπdef
    set u : Fin n → ℂ_[p] := fun i => ((PreTilt.untilt (φi^[m] (x i)) : 𝒪) : ℂ_[p]) with hudef
    have hζ1 : ζ ^ p ^ m = 1 := coe_untilt_iterate_pow_eq_one hε m
    have hζn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq (pow_ne_zero _ hp.out.ne_zero) (by
      rw [← norm_pow, hζ1, norm_one])
    have hun : ∀ i, ‖u i‖ = 1 := fun i => norm_eq_one_of_pow_eq (pow_ne_zero _ hp.out.ne_zero) (by
      rw [hudef, IsPerfectoidField.norm_untilt_iterate_pow, hunit i])
    have hπn : ‖π‖ ^ p ^ m = (p : ℝ)⁻¹ := by
      rw [hπdef, IsPerfectoidField.norm_untilt_iterate_pow, coe_untilt_pFlat, norm_natCast_p_cp]
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hπ1 : ‖π‖ < 1 := (pow_lt_one_iff_of_nonneg (norm_nonneg π) (pow_ne_zero _ hp.out.ne_zero)).1
      (by rw [hπn]; exact hpinv)
    set A : Fin n → ℕ := fun i => (PadicInt.toZModPow m (μ i)).val with hA
    set B : ℕ := (PadicInt.toZModPow m ν).val with hB
    set P : ℂ_[p] := ∏ i, u i ^ A i with hP
    have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζn; exact zero_ne_one hζn
    have hPn : ‖P‖ = 1 := by rw [hP, norm_prod]; exact Finset.prod_eq_one fun i _ => by rw [norm_pow, hun i, one_pow]
    have hP0 : P ≠ 0 := by intro h; rw [h, norm_zero] at hPn; exact zero_ne_one hPn
    set N : ℂ_[p] := ζ ^ B * P with hN
    set Y : ℂ_[p] := π ^ p ^ e * N⁻¹ with hY
    have hYfix : ∀ σ : Gal(PadicAlgCl p/K), σ • Y = Y := by
      intro σ
      set cm := (PadicInt.toZModPow m (kummerC hε hζ σ)).val with hcm
      set χm := (PadicInt.toZModPow m (cycloChar K σ : ℤ_[p])).val with hχm
      set κm : Fin n → ℕ := fun i => (PadicInt.toZModPow m (κ i σ)).val with hκm
      set S : ℕ := ∑ i, κm i * A i with hS
      have hπσ : σ • π = π * ζ ^ cm :=
        gal_smul_untilt_iterate_of_eq_mul hε
          (tiltGal_eq_mul_epsPow hε hζ pFlat_ne_zero gal_smul_coe_untilt_pFlat σ) m
      have huσ : ∀ i, σ • u i = u i * ζ ^ κm i := fun i =>
        gal_smul_untilt_iterate_of_eq_mul hε (tiltGal_eq_mul_epsPow hε hζ (hx0 i) (hfix i) σ) m
      have hζσ : σ • ζ = ζ ^ χm := gal_smul_eq_pow_of_pow_eq_one σ hζ1
      have hexp : ζ ^ (χm * B + S) = ζ ^ (p ^ e * cm + B) := by
        apply pow_eq_pow_of_mod_eq hζ1
        rw [← ZMod.natCast_eq_natCast_iff', hS]
        have h := congrArg (PadicInt.toZModPow m) (HZ σ)
        simp only [map_add, map_mul, map_pow, map_natCast, map_sum] at h
        push_cast
        simp only [hcm, hχm, hκm, hA, hB, ZMod.natCast_val, ZMod.cast_id', id]
        rw [h, Finset.sum_congr rfl fun i _ => mul_comm ((PadicInt.toZModPow m) (κ i σ)) _]
        ring
      have hσP : σ • P = P * ζ ^ S := by
        rw [hP, hS, ← galCp_apply, map_prod]
        simp only [map_pow, galCp_apply, huσ, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
          Finset.prod_pow_eq_pow_sum]
      have hσN : σ • N = ζ ^ (p ^ e * cm) * N := by
        rw [hN, ← galCp_apply, map_mul, map_pow, galCp_apply, galCp_apply, hζσ, hσP, ← pow_mul]
        have h2 : ζ ^ (χm * B) * ζ ^ S = ζ ^ (p ^ e * cm) * ζ ^ B := by
          rw [← pow_add, ← pow_add, hexp]
        linear_combination P * h2
      rw [hY, ← galCp_apply, map_mul, map_inv₀, map_pow, galCp_apply, galCp_apply, hπσ, hσN, mul_pow,
        ← pow_mul, mul_inv, mul_comm cm, ← mul_assoc, mul_assoc (π ^ p ^ e), mul_inv_cancel₀
          (pow_ne_zero _ hζ0), mul_one]
    obtain ⟨yK, hyK⟩ := exists_eq_coe_of_forall_smul_eq hYfix
    have hYn : ‖Y‖ = ‖π‖ ^ p ^ e := by
      simp only [hY, hN, norm_mul, norm_inv, norm_pow, hζn, hPn, one_pow, mul_one, inv_one]
    have hy1 : ‖(yK : PadicAlgCl p)‖ < 1 := by
      rw [← UniformSpace.Completion.norm_coe, hyK, hYn]
      exact pow_lt_one₀ (norm_nonneg _) hπ1 (pow_ne_zero _ hp.out.ne_zero)
    have hyδ := hδ _ yK.2 hy1
    rw [← UniformSpace.Completion.norm_coe, hyK, hYn] at hyδ
    calc ((p : ℝ)⁻¹) ^ p ^ e = (‖π‖ ^ p ^ e) ^ p ^ m := by rw [← pow_mul, mul_comm, pow_mul, hπn]
      _ ≤ δ ^ p ^ m := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) hyδ _

  have ha : (0 : ℝ) < ((p : ℝ)⁻¹) ^ p ^ e :=
    pow_pos (inv_pos.2 (by exact_mod_cast hp.out.pos)) _
  rcases le_or_gt δ 0 with hδ0 | hδ0
  · have h := hlevel 0
    rw [pow_zero, pow_one] at h
    linarith
  · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ha hδ1
    have h1 : δ ^ p ^ m ≤ δ ^ m :=
      pow_le_pow_of_le_one hδ0.le hδ1.le (Nat.lt_pow_self hp.out.one_lt).le
    linarith [hlevel m]

end Contradiction

end GroundTheory.PAdicHodge
end
end
