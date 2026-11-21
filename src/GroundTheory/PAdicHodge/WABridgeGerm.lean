import Mathlib
import GroundTheory.PAdicHodge.WAEval
import GroundTheory.PAdicHodge.ACrisBdRGalois
import GroundTheory.PAdicHodge.BCrisNewtonApprox

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift ACris PhiGamma IsPerfectoidField

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "θ" => fontaineTheta (normInteger ℂ_[p]) p

variable (p) in

def radA : ℝ := ((p : ℝ)⁻¹) ^ p

theorem radA_pos : 0 < radA p := pow_pos inv_p_pos p

theorem radA_lt_one : radA p < 1 := pow_lt_one₀ inv_p_pos.le inv_p_lt_one hp.out.ne_zero

theorem xiA_mem_ker : xiA p ∈ RingHom.ker θ := by
  rw [ker_theta_eq_span_xiA]; exact Ideal.mem_span_singleton_self _

theorem exists_teich_pow_eq : ∃ w ∈ ACrisZero ℂ_[p] p,
    algebraMap (AInf ℂ_[p] p) 𝔸 (teichmuller p (pFlat p)) ^ p = (p : 𝔸) * w := by
  have e : teichmuller p (pFlat p) = (p : AInf ℂ_[p] p) - xiA p := by rw [xiA]; ring
  obtain ⟨q, hq⟩ : ((p : AInf ℂ_[p] p) ^ (1 + 1)) ∣ ((p : AInf ℂ_[p] p) - xiA p) ^ p ^ 1 -
      (-xiA p) ^ p ^ 1 :=
    dvd_sub_pow_of_dvd_sub (p := p) (a := (p : AInf ℂ_[p] p) - xiA p) (b := -xiA p) ⟨1, by ring⟩ 1
  refine ⟨(p : 𝔸) * algebraMap _ 𝔸 q + ((-1) ^ p * ((p - 1).factorial : 𝔸)) * dpow p (xiA p), ?_, ?_⟩
  · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
      (Subalgebra.algebraMap_mem _ _)) (Subalgebra.mul_mem _ ?_ (dpow_mem xiA_mem_ker p))
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
      (Subalgebra.natCast_mem _ _)
  · have h1 : ((p : AInf ℂ_[p] p) - xiA p) ^ p = (-xiA p) ^ p + (p : AInf ℂ_[p] p) ^ 2 * q := by
      rw [pow_one] at hq; rw [← hq]; ring
    have h2 := factorial_mul_dpow (K := ℂ_[p]) (p := p) p (xiA p)
    have h3 : (p.factorial : 𝔸) = (p : 𝔸) * ((p - 1).factorial : 𝔸) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
    rw [e, ← map_pow, h1, map_add, map_mul, map_pow, map_pow, map_neg, neg_pow, ← h2, h3,
      map_natCast]
    ring

theorem gn_radA_natCast_p : gn ℂ_[p] p (radA p) (p : 𝔸) = radA p := gn_natCast_p (radA_pos (p := p))

theorem norm_red_le_gn (x : AInf ℂ_[p] p) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ‖(𝓣).red (incl ℂ_[p] p x)‖ ≤ gn ℂ_[p] p ρ (algebraMap _ 𝔸 x) := by
  have hc := convergesAt_toB (K := ℂ_[p]) (p := p) (algebraMap _ 𝔸 x) hρ0 hρ1
  unfold gn
  rw [coeffB_toB_algebraMap] at hc ⊢
  have h := hc.le_gaussNorm 0
  rw [zpow_zero, mul_one] at h
  have e : (𝓣).zcoeff (incl ℂ_[p] p x) 0 = (𝓣).red (incl ℂ_[p] p x) := by
    simp [TeichLift.zcoeff, TeichLift.coeff]
  rw [e] at h
  exact h

theorem gn_of_incl_eq_teich {x : AInf ℂ_[p] p} {a : Cb p} (h : incl ℂ_[p] p x = (𝓣).teich a)
    {ρ : ℝ} (hρ0 : 0 < ρ) : gn ℂ_[p] p ρ (algebraMap _ 𝔸 x) = ‖a‖ := by
  rw [gn, coeffB_toB_algebraMap, h, TeichLift.zcoeff_teich, TeichLift.gaussNorm_pi_single 0 a hρ0,
    zpow_zero, mul_one]

theorem exists_eq_pow_mul_of_gn_le (k : ℕ) : ∀ x : AInf ℂ_[p] p,
    gn ℂ_[p] p (radA p) (algebraMap _ 𝔸 x) ≤ radA p ^ k →
      ∃ c ∈ ACrisZero ℂ_[p] p, algebraMap _ 𝔸 x = (p : 𝔸) ^ k * c := by
  induction k with
  | zero =>
    intro x _
    exact ⟨_, Subalgebra.algebraMap_mem _ x, by rw [pow_zero, one_mul]⟩
  | succ k ih =>
    intro x hx
    obtain ⟨w, hw, hwe⟩ := exists_teich_pow_eq (p := p)
    set a := (𝓣).red (incl ℂ_[p] p x) with ha
    have hv0 : varpi p ≠ 0 := varpi_ne_zero
    have hna : ‖a‖ ≤ ‖varpi p‖ ^ (p * (k + 1)) := by
      rw [norm_varpi, pow_mul]
      exact (norm_red_le_gn x (radA_pos (p := p)) (radA_lt_one (p := p))).trans hx
    set c := a / varpi p ^ (p * (k + 1)) with hc_def
    have hc : ‖c‖ ≤ 1 := by
      rw [hc_def, norm_div, norm_pow]
      exact div_le_one_of_le₀ hna (by positivity)
    have hac : a = varpi p ^ (p * (k + 1)) * c := by
      rw [hc_def, mul_div_cancel₀ _ (pow_ne_zero _ hv0)]
    obtain ⟨u, hu⟩ := (𝓣).teich_mem_int hc
    obtain ⟨x', hx'⟩ := (𝓣).tail_mem_int (⟨x, rfl⟩ : incl ℂ_[p] p x ∈ (𝓣).int)
    obtain ⟨t, ht⟩ : ∃ t, t = teichmuller p (pFlat p) ^ (p * (k + 1)) * u := ⟨_, rfl⟩
    have hteich : incl ℂ_[p] p t = (𝓣).teich a := by
      rw [ht, map_mul, map_pow, incl_teichmuller, hu, hac, (𝓣).teich_mul, (𝓣).teich_pow, teich_eq, teich_eq]
      rfl
    have hdec : x = t + (p : AInf ℂ_[p] p) * x' := by
      apply incl_injective
      rw [map_add, map_mul, hteich, hx', map_natCast]
      exact (𝓣).eq_teich_add_π_mul_tail (incl ℂ_[p] p x)
    have hgt : gn ℂ_[p] p (radA p) (algebraMap _ 𝔸 t) ≤ radA p ^ (k + 1) := by
      rw [gn_of_incl_eq_teich hteich (radA_pos (p := p))]
      exact (norm_red_le_gn x (radA_pos (p := p)) (radA_lt_one (p := p))).trans hx
    have hgx' : gn ℂ_[p] p (radA p) (algebraMap _ 𝔸 x') ≤ radA p ^ k := by
      have e : algebraMap (AInf ℂ_[p] p) 𝔸 ((p : AInf ℂ_[p] p) * x') =
          algebraMap _ 𝔸 x - algebraMap _ 𝔸 t := by
        rw [hdec, map_add]; ring
      have h1 := gn_sub_le (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p)) (algebraMap _ 𝔸 x) (algebraMap _ 𝔸 t)
      rw [← e, map_mul, map_natCast, gn_mul (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p)), gn_radA_natCast_p]
        at h1
      have h2 := h1.trans (max_le hx hgt)
      rw [pow_succ'] at h2
      exact le_of_mul_le_mul_left h2 (radA_pos (p := p))
    obtain ⟨c', hc', hc'e⟩ := ih x' hgx'
    refine ⟨w ^ (k + 1) * algebraMap _ 𝔸 u + c', Subalgebra.add_mem _
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hw _) (Subalgebra.algebraMap_mem _ u)) hc', ?_⟩
    rw [hdec, map_add, map_mul, hc'e, ht, map_mul, map_pow, pow_mul, hwe, map_natCast]
    ring

theorem isUnit_p_away : IsUnit (p : 𝔸) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := 𝔸) (p : AInf ℂ_[p] p)
  rwa [map_natCast] at this

theorem mem_acrisZero_of_gn_le_one {z : 𝔸} (hz : gn ℂ_[p] p (radA p) z ≤ 1) :
    z ∈ ACrisZero ℂ_[p] p := by
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (p : AInf ℂ_[p] p) z
  have hgx : gn ℂ_[p] p (radA p) (algebraMap _ 𝔸 x) ≤ radA p ^ k := by
    rw [← hx, map_natCast, gn_mul (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p)),
      gn_pow (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p)), gn_radA_natCast_p]
    exact mul_le_of_le_one_left (pow_nonneg (radA_pos (p := p)).le k) hz
  obtain ⟨c, hc, hcx⟩ := exists_eq_pow_mul_of_gn_le k x hgx
  have e : z = c := by
    have h1 : z * (p : 𝔸) ^ k = c * (p : 𝔸) ^ k := by
      rw [mul_comm c, ← hcx, ← hx, map_natCast]
    exact (isUnit_p_away.pow k).mul_right_cancel h1
  rw [e]; exact hc

theorem gn_pUnit_zpow (k : ℤ) : gn ℂ_[p] p (radA p) ((pUnit p ^ k : 𝔸ˣ) : 𝔸) = radA p ^ k := by
  have hnat : ∀ n : ℕ, gn ℂ_[p] p (radA p) ((pUnit p ^ n : 𝔸ˣ) : 𝔸) = radA p ^ n := by
    intro n
    rw [Units.val_pow_eq_pow_val, coe_pUnit, map_natCast, gn_pow (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p)),
      gn_radA_natCast_p]
  have hinv : ∀ u : 𝔸ˣ, gn ℂ_[p] p (radA p) ((u⁻¹ : 𝔸ˣ) : 𝔸) *
      gn ℂ_[p] p (radA p) (u : 𝔸) = 1 := by
    intro u
    rw [← gn_mul (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p)), ← Units.val_mul, inv_mul_cancel, Units.val_one,
      gn_one (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p))]
  rcases k with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hnat, zpow_natCast]
  · rw [zpow_negSucc, zpow_negSucc]
    have h := hinv (pUnit p ^ (n + 1))
    rw [← hnat]
    exact eq_inv_of_mul_eq_one_left h

theorem exists_eq_zpow_mul_of_gn_le {z : 𝔸} {M : ℤ} (hz : gn ℂ_[p] p (radA p) z ≤ radA p ^ M) :
    ∃ c ∈ ACrisZero ℂ_[p] p, z = ((pUnit p ^ M : 𝔸ˣ) : 𝔸) * c := by
  refine ⟨((pUnit p ^ (-M) : 𝔸ˣ) : 𝔸) * z, mem_acrisZero_of_gn_le_one ?_, ?_⟩
  · rw [gn_mul (K := ℂ_[p]) (p := p) (radA_pos (p := p)) (radA_lt_one (p := p)), gn_pUnit_zpow, zpow_neg]
    have hpos : 0 < radA p ^ M := zpow_pos (radA_pos (p := p)) M
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hz
  · rw [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul]

theorem exists_toB_eq_of_norm_coeffB_le_one {b : (𝓣).B} (hb : ∀ n, ‖(𝓣).coeffB b n‖ ≤ 1) :
    ∃ s : 𝔸, toB ℂ_[p] p s = b := by
  have hnum := (𝓣).num_spec b
  have hcoeff := (𝓣).coeffB_eq hnum
  have hint : (𝓣).num b ∈ (𝓣).int := (𝓣).mem_int_iff.2 fun n => by
    have h := hb ((n : ℤ) - ((𝓣).den b : ℤ))
    rw [hcoeff] at h
    simp only [sub_add_cancel] at h
    simpa [TeichLift.zcoeff] using h
  obtain ⟨x, hx⟩ := hint
  refine ⟨algebraMap _ 𝔸 x * ((pUnit p ^ (-((𝓣).den b : ℤ)) : 𝔸ˣ) : 𝔸), ?_⟩
  have hu : toB ℂ_[p] p ((pUnit p ^ (-((𝓣).den b : ℤ)) : 𝔸ˣ) : 𝔸) *
      algebraMap _ (𝓣).B (𝓣).π ^ (𝓣).den b = 1 := by
    have e : algebraMap _ (𝓣).B (𝓣).π ^ (𝓣).den b =
        toB ℂ_[p] p ((pUnit p ^ (((𝓣).den b : ℕ) : ℤ) : 𝔸ˣ) : 𝔸) := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_pow, toB_algebraMap, map_natCast]
      rfl
    rw [e, ← map_mul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, map_one]
  have h2 : (toB ℂ_[p] p (algebraMap _ 𝔸 x * ((pUnit p ^ (-((𝓣).den b : ℤ)) : 𝔸ˣ) : 𝔸)) - b) *
      algebraMap _ (𝓣).B (𝓣).π ^ (𝓣).den b = 0 := by
    rw [sub_mul, map_mul, mul_assoc, hu, mul_one, hnum, toB_algebraMap, hx, sub_self]
  exact sub_eq_zero.1 ((𝓣).eq_zero_of_mul_pow h2)

theorem toB_phiAway (z : 𝔸) :
    toB ℂ_[p] p (phiAway ℂ_[p] p z) = (frob ℂ_[p] p).toB (toB ℂ_[p] p z) := by
  have h : (toB ℂ_[p] p).comp (phiAway ℂ_[p] p) =
      ((frob ℂ_[p] p).toB : (𝓣).B →+* (𝓣).B).comp (toB ℂ_[p] p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p))
    ext x
    simp only [RingHom.comp_apply, phiAway_algebraMap, toB_algebraMap, RingEquiv.coe_toRingHom,
      TeichLift.TeichFrob.toB_algebraMap, frob_φ_incl]
  exact RingHom.congr_fun h z

set_option maxHeartbeats 1000000 in

theorem exists_limit (t : ℕ → ACrisZero ℂ_[p] p)
    (ht : ∀ N N', N ≤ N' → ∃ d : ACrisZero ℂ_[p] p, t N - t N' = (p : ACrisZero ℂ_[p] p) ^ N * d) :
    ∃ c : ACris ℂ_[p] p, ∀ N, ∃ d : ACris ℂ_[p] p,
      c - algebraMap _ (ACris ℂ_[p] p) (t N) = (p : ACris ℂ_[p] p) ^ N * d := by
  have hprec : IsPrecomplete (Ideal.span {(p : ACris ℂ_[p] p)}) (ACris ℂ_[p] p) := inferInstance
  have key : ∀ m n : ℕ, m ≤ n → (p : ACris ℂ_[p] p) ^ m ∣
      algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) (t m) -
        algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) (t n) := by
    intro m n hmn
    obtain ⟨d, hd⟩ := ht m n hmn
    refine ⟨algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) d, ?_⟩
    rw [← map_sub, hd, map_mul, map_pow, map_natCast]
  obtain ⟨L, hL⟩ := hprec.prec (f := fun N => algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) (t N))
    (fun {m n} hmn => (smodEq_span_singleton_pow_iff _ _ _ _).2 (key m n hmn))
  refine ⟨L, fun N => ?_⟩
  obtain ⟨d, hd⟩ := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hL N)
  refine ⟨-d, ?_⟩
  rw [mul_neg, ← hd]; ring

variable {ρ : Set.Ioo (0 : ℝ) 1}

theorem evalB_zero_eq (x y : 𝔹) : evalB ℂ_[p] p 0 x = evalB ℂ_[p] p 0 y := by
  rw [← sub_eq_zero]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalB ℂ_[p] p 0 x - evalB ℂ_[p] p 0 y)
  rw [← ha, Ideal.Quotient.eq_zero_iff_mem, pow_zero, Ideal.one_eq_top]
  trivial

theorem evalB_iota_acris (n : ℕ) (c : ACris ℂ_[p] p) :
    evalB ℂ_[p] p n (ACris.iota ℂ_[p] p c) = ACris.iotaQ ℂ_[p] p n c :=
  evalₐ_iota n c

theorem iotaQ_algebraMap_acrisZero (n : ℕ) (y : ACrisZero ℂ_[p] p) :
    ACris.iotaQ ℂ_[p] p n (algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) y) =
      Ideal.Quotient.mk _ (y : 𝔸) := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, iotaQ_of]

theorem iotaQ_mem_acrisQ (n : ℕ) (c : ACris ℂ_[p] p) : ACris.iotaQ ℂ_[p] p n c ∈ acrisQ ℂ_[p] p n :=
  (embedding₂ ℂ_[p] p n c).2

set_option maxHeartbeats 1000000 in

theorem pow_mul_iota_eq (hρ : (p : ℝ)⁻¹ < ρ) {w : (𝓣).RobbaExt ρ} {c : ACris ℂ_[p] p} (j : ℕ)
    (s : ℕ → 𝔸)
    (hs : ∀ N : ℕ, (𝓣).extNorm ρ (inversePRadius p hρ) (w - awayToExt p ρ (s N)) ≤ (p : ℝ) ^ (-(N : ℤ)))
    (hmem : ∀ N, (p : 𝔸) ^ j * s N ∈ ACrisZero ℂ_[p] p)
    (hc : ∀ N, ∃ d : ACris ℂ_[p] p,
      c - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem N⟩ = (p : ACris ℂ_[p] p) ^ N * d) :
    (p : 𝔹) ^ j * iota p hρ w = ACris.iota ℂ_[p] p c := by
  refine evalB_ext fun n => ?_
  rcases n with _ | m
  · exact evalB_zero_eq _ _
  set Q := 𝔸 ⧸ RingHom.ker (fontaineThetaInvertP (normInteger ℂ_[p]) p) ^ (m + 1)
  set D : Q := evalB ℂ_[p] p (m + 1) ((p : 𝔹) ^ j * iota p hρ w) -
    evalB ℂ_[p] p (m + 1) (ACris.iota ℂ_[p] p c) with hDdef
  have hD : ∀ N : ℕ, ∃ e ∈ acrisQ ℂ_[p] p (m + 1), D = (p : Q) ^ N * e := by
    intro N
    have hw := hs (N + m)
    have hw' : (𝓣).extNorm ρ (inversePRadius p hρ) (w - awayToExt p ρ (s (N + m))) ≤
        (p : ℝ) ^ (-((N + m : ℕ) : ℤ)) := hw
    obtain ⟨y, hy⟩ := exists_evalB_iota_eq_zpow hρ hw' m
    obtain ⟨d, hd⟩ := hc (N + m)
    have hexp : (((N + m : ℕ) : ℤ) - (m : ℤ)) = (N : ℤ) := by push_cast; ring
    have e1 : iota p hρ (w - awayToExt p ρ (s (N + m))) =
        iota p hρ w - toBDeRhamPlus (normInteger ℂ_[p]) p (s (N + m)) := by
      rw [map_sub, iota_awayToExt]
    have e2 : ((pUnit p ^ (((N + m : ℕ) : ℤ) - (m : ℤ)) : 𝔸ˣ) : 𝔸) = (p : 𝔸) ^ N := by
      rw [hexp, zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_natCast]
    rw [e1, e2] at hy
    have h1 : evalB ℂ_[p] p (m + 1) (iota p hρ w) = Ideal.Quotient.mk _ (s (N + m)) +
        (p : Q) ^ N * Ideal.Quotient.mk _ (algebraMap _ 𝔸 y) := by
      have h2 := hy
      rw [map_sub, evalB_toBDeRhamPlus] at h2
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, ← h2]
      ring
    have hc' : c = algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem (N + m)⟩ +
        (p : ACris ℂ_[p] p) ^ (N + m) * d := by rw [← hd]; ring
    refine ⟨(p : Q) ^ j * Ideal.Quotient.mk _ (algebraMap _ 𝔸 y) -
      (p : Q) ^ m * ACris.iotaQ ℂ_[p] p (m + 1) d, ?_, ?_⟩
    · refine Subring.sub_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _)
        (latticeQ_le _ ⟨y, rfl⟩)) (Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _)
        (iotaQ_mem_acrisQ _ _))
    · have h3 : evalB ℂ_[p] p (m + 1) (ACris.iota ℂ_[p] p c) =
          (p : Q) ^ j * Ideal.Quotient.mk _ (s (N + m)) +
            (p : Q) ^ (N + m) * ACris.iotaQ ℂ_[p] p (m + 1) d := by
        rw [evalB_iota_acris, hc', map_add, map_mul, map_pow, map_natCast,
          iotaQ_algebraMap_acrisZero]
        simp only [map_mul, map_pow, map_natCast]
      rw [hDdef, map_mul, map_pow, map_natCast, h1, h3]
      ring
  obtain ⟨e0, he0, hDe0⟩ := hD 0
  have hDmem : D ∈ acrisQ ℂ_[p] p (m + 1) := by rw [hDe0, pow_zero, one_mul]; exact he0
  have := isAdicComplete_acrisQ ℂ_[p] p (m + 1)
  have hzero : (⟨D, hDmem⟩ : acrisQ ℂ_[p] p (m + 1)) = 0 := by
    refine IsHausdorff.haus' (I := Ideal.span {(p : acrisQ ℂ_[p] p (m + 1))}) _ fun N => ?_
    rw [smodEq_span_singleton_pow_iff, sub_zero, subring_pow_dvd_iff]
    obtain ⟨e, he, hDe⟩ := hD N
    exact ⟨e, he, hDe⟩
  have h0 : D = 0 := congrArg Subtype.val hzero
  exact sub_eq_zero.1 h0

end WABridge

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable (p) in

def allRad : Subring (𝓣).RobbaTilde := ⨅ ρ : Set.Ioo (0 : ℝ) 1, ((𝓣).ofRad ρ).range

theorem mem_allRad {x : (𝓣).RobbaTilde} :
    x ∈ allRad p ↔ ∀ ρ : Set.Ioo (0 : ℝ) 1, x ∈ ((𝓣).ofRad ρ).range := by
  rw [allRad, Subring.mem_iInf]

theorem mem_range_ofRad_of_le {ρ ρ' : Set.Ioo (0 : ℝ) 1} (h : (ρ' : ℝ) ≤ ρ) {x : (𝓣).RobbaTilde}
    (hx : x ∈ ((𝓣).ofRad ρ).range) : x ∈ ((𝓣).ofRad ρ').range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(𝓣).res h y, (𝓣).ofRad_res h y⟩

theorem tildeFrobSymm_mem_range {τ : Set.Ioo (0 : ℝ) 1} {x : (𝓣).RobbaTilde}
    (hx : x ∈ ((𝓣).ofRad τ).range) :
    (frob ℂ_[p] p).tildeFrobSymm x ∈ ((𝓣).ofRad ((frob ℂ_[p] p).rootRadius τ)).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, ((frob ℂ_[p] p).tildeFrobSymm_ofRad τ y).symm⟩

theorem tildeFrobSymm_mem_allRad {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) :
    (frob ℂ_[p] p).tildeFrobSymm x ∈ allRad p :=
  mem_allRad.2 fun ρ => mem_range_ofRad_of_le (le_rootRadius ρ)
    (tildeFrobSymm_mem_range (mem_allRad.1 hx ρ))

theorem coe_iterate_rootRadius (τ : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (((frob ℂ_[p] p).rootRadius^[n] τ : Set.Ioo (0 : ℝ) 1) : ℝ) = (τ : ℝ) ^ ((p : ℝ)⁻¹ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', rootRadius_coe, ih, ← Real.rpow_mul τ.2.1.le, pow_succ]

theorem exists_le_iterate_rootRadius (τ ρ : Set.Ioo (0 : ℝ) 1) :
    ∃ n : ℕ, (ρ : ℝ) ≤ (((frob ℂ_[p] p).rootRadius^[n] τ : Set.Ioo (0 : ℝ) 1) : ℝ) := by
  have hL : 0 < -Real.log τ := neg_pos.2 (Real.log_neg τ.2.1 τ.2.2)
  have hR : 0 < -Real.log ρ := neg_pos.2 (Real.log_neg ρ.2.1 ρ.2.2)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hR hL) (inv_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  rw [coe_iterate_rootRadius, Real.rpow_def_of_pos τ.2.1]
  rw [lt_div_iff₀ hL] at hN
  calc (ρ : ℝ) = Real.exp (Real.log ρ) := (Real.exp_log ρ.2.1).symm
    _ ≤ Real.exp (Real.log τ * (p : ℝ)⁻¹ ^ N) := Real.exp_le_exp.2 (by nlinarith)

theorem ofRad_awayToExt (ρ ρ' : Set.Ioo (0 : ℝ) 1) (a : 𝔸) :
    (𝓣).ofRad ρ (awayToExt p ρ a) = (𝓣).ofRad ρ' (awayToExt p ρ' a) := by
  let ρ3 : Set.Ioo (0 : ℝ) 1 := ⟨min ρ ρ', lt_min ρ.2.1 ρ'.2.1, min_lt_of_left_lt ρ.2.2⟩
  rw [← (𝓣).ofRad_res (ρ1 := ρ3) (min_le_left _ _), res_awayToExt,
    ← (𝓣).ofRad_res (ρ1 := ρ3) (min_le_right _ _) (awayToExt p ρ' a), res_awayToExt]

variable (p) in

def ainfTilde : AInf ℂ_[p] p →+* (𝓣).RobbaTilde :=
  ((𝓣).ofRad (rhoMid p)).comp ((awayToExt p (rhoMid p)).comp (algebraMap (AInf ℂ_[p] p) 𝔸))

theorem ainfTilde_eq (ρ : Set.Ioo (0 : ℝ) 1) (a : AInf ℂ_[p] p) :
    ainfTilde p a = (𝓣).ofRad ρ (awayToExt p ρ (algebraMap _ 𝔸 a)) :=
  ofRad_awayToExt _ _ _

theorem ainfTilde_mem_allRad (a : AInf ℂ_[p] p) : ainfTilde p a ∈ allRad p :=
  mem_allRad.2 fun ρ => ⟨_, (ainfTilde_eq ρ a).symm⟩

theorem mem_allRad_of_tildeFrob_eq {m : ℕ} (C : Matrix (Fin m) (Fin m) (𝓣).RobbaTilde)
    (hC : ∀ i j, C i j ∈ allRad p) (y : Fin m → (𝓣).RobbaTilde)
    (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) = ∑ j, C i j * y j) (i : Fin m) :
    y i ∈ allRad p := by
  obtain ⟨ρ₀, h₀⟩ : ∃ ρ₀ : Set.Ioo (0 : ℝ) 1, ∀ j, y j ∈ ((𝓣).ofRad ρ₀).range := by
    have key : ∀ s : Finset (Fin m), ∃ ρ₀ : Set.Ioo (0 : ℝ) 1,
        ∀ j ∈ s, y j ∈ ((𝓣).ofRad ρ₀).range := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨rhoMid p, by simp⟩
      | insert j s hj ih =>
        obtain ⟨ρ₁, h₁⟩ := ih
        obtain ⟨ρ₂, z, hz⟩ := (𝓣).exists_ofRad (y j)
        refine ⟨⟨min ρ₁ ρ₂, lt_min ρ₁.2.1 ρ₂.2.1, min_lt_of_left_lt ρ₁.2.2⟩, fun k hk => ?_⟩
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact mem_range_ofRad_of_le (min_le_right _ _) ⟨z, hz⟩
        · exact mem_range_ofRad_of_le (min_le_left _ _) (h₁ k hk)
    obtain ⟨ρ₀, h⟩ := key Finset.univ
    exact ⟨ρ₀, fun j => h j (Finset.mem_univ j)⟩
  have hstep : ∀ n : ℕ, ∀ j, y j ∈ ((𝓣).ofRad ((frob ℂ_[p] p).rootRadius^[n] ρ₀)).range := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih =>
      intro j
      rw [Function.iterate_succ_apply']
      have e : y j = ∑ k, (frob ℂ_[p] p).tildeFrobSymm (C j k) *
          (frob ℂ_[p] p).tildeFrobSymm (y k) := by
        conv_lhs => rw [← (frob ℂ_[p] p).tildeFrobSymm_tildeFrob (y j), hy j, map_sum]
        simp only [map_mul]
      rw [e]
      refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (tildeFrobSymm_mem_range (ih k))
      exact mem_allRad.1 (tildeFrobSymm_mem_allRad (hC j k)) _
  refine mem_allRad.2 fun ρ => ?_
  obtain ⟨n, hn⟩ := exists_le_iterate_rootRadius (p := p) ρ₀ ρ
  exact mem_range_ofRad_of_le hn (hstep n i)

def rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (ρ : Set.Ioo (0 : ℝ) 1) : (𝓣).RobbaExt ρ :=
  (mem_allRad.1 hx ρ).choose

theorem ofRad_rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (ρ : Set.Ioo (0 : ℝ) 1) :
    (𝓣).ofRad ρ (rep hx ρ) = x :=
  (mem_allRad.1 hx ρ).choose_spec

theorem rep_eq {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) {ρ : Set.Ioo (0 : ℝ) 1}
    {y : (𝓣).RobbaExt ρ} (h : (𝓣).ofRad ρ y = x) : rep hx ρ = y :=
  (𝓣).ofRad_injective ρ (by rw [ofRad_rep, h])

theorem res_rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1}
    (h : (ρ1 : ℝ) ≤ ρ0) : (𝓣).res h (rep hx ρ0) = rep hx ρ1 :=
  (rep_eq hx (by rw [(𝓣).ofRad_res, ofRad_rep])).symm

def tn {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  (𝓣).extNorm r (topRad r) (rep hx r)

theorem tn_nonneg {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (r : Set.Ioo (0 : ℝ) 1) :
    0 ≤ tn hx r :=
  (𝓣).extNorm_nonneg _ _

theorem extNorm_rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (σ : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioc (0 : ℝ) σ) :
    (𝓣).extNorm σ r (rep hx σ) = tn hx ⟨r, r.2.1, lt_of_le_of_lt r.2.2 σ.2.2⟩ := by
  rw [tn, ← res_rep hx (ρ0 := σ) (ρ1 := ⟨r, r.2.1, lt_of_le_of_lt r.2.2 σ.2.2⟩) r.2.2,
    (𝓣).extNorm_res]
  rfl

theorem coe_powRadius (σ : Set.Ioo (0 : ℝ) 1) :
    (((frob ℂ_[p] p).powRadius σ : Set.Ioo (0 : ℝ) 1) : ℝ) = (σ : ℝ) ^ p := by
  show (σ : ℝ) ^ p ^ (frob ℂ_[p] p).a = _
  rw [frob_a, pow_one]

theorem coe_iterate_powRadius (σ : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    (((frob ℂ_[p] p).powRadius^[k] σ : Set.Ioo (0 : ℝ) 1) : ℝ) = (σ : ℝ) ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', coe_powRadius, ih, ← pow_mul, pow_succ]

theorem iterate_powRadius_rootRadius (c : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    (frob ℂ_[p] p).powRadius^[k] ((frob ℂ_[p] p).rootRadius^[k] c) = c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
      (frob ℂ_[p] p).powRadius_rootRadius, ih]

theorem extNorm_awayToExt (ρ : Set.Ioo (0 : ℝ) 1) (r : Set.Ioc (0 : ℝ) ρ) (a : 𝔸) :
    (𝓣).extNorm ρ r (awayToExt p ρ a) = gn ℂ_[p] p r a := by
  rw [awayToExt_apply, extNorm_coe]
  rfl

theorem exists_extNorm_sum_le {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (f : ι → (𝓣).RobbaExt σ) :
    ∃ j ∈ s, (𝓣).extNorm σ r (∑ k ∈ s, f k) ≤ (𝓣).extNorm σ r (f j) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by rw [Finset.sum_singleton]⟩
  | cons a s ha hs ih =>
    obtain ⟨j, hj, hjle⟩ := ih
    rw [Finset.sum_cons]
    rcases le_total ((𝓣).extNorm σ r (f a)) ((𝓣).extNorm σ r (f j)) with h | h
    · exact ⟨j, Finset.mem_cons_of_mem hj, ((𝓣).extNorm_add_le _ _ _).trans (max_le h hjle)⟩
    · exact ⟨a, Finset.mem_cons_self a s,
        ((𝓣).extNorm_add_le _ _ _).trans (max_le le_rfl (hjle.trans h))⟩

section Decay

variable {m : ℕ} (C : Matrix (Fin m) (Fin m) (AInf ℂ_[p] p))
  {y : Fin m → (teichLift ℂ_[p] p).RobbaTilde}
  (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) =
    ∑ j, (p : (teichLift ℂ_[p] p).RobbaTilde) * ainfTilde p (C i j) * y j)
  (ha : ∀ i, y i ∈ allRad p)

include hy in

theorem extFrob_rep (i : Fin m) (σ : Set.Ioo (0 : ℝ) 1) :
    (frob ℂ_[p] p).extFrob σ (rep (ha i) σ) = ∑ j, (p : (𝓣).RobbaExt ((frob ℂ_[p] p).powRadius σ)) *
      awayToExt p ((frob ℂ_[p] p).powRadius σ) (algebraMap _ 𝔸 (C i j)) *
        rep (ha j) ((frob ℂ_[p] p).powRadius σ) := by
  apply (𝓣).ofRad_injective
  rw [← (frob ℂ_[p] p).tildeFrob_ofRad, ofRad_rep, hy i, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, map_natCast, ofRad_rep, ← ainfTilde_eq]

include hy in

theorem exists_tn_pow_le (i : Fin m) (r : Set.Ioo (0 : ℝ) 1) :
    ∃ j, tn (ha i) r ^ p ≤ (r : ℝ) ^ p * tn (ha j) ((frob ℂ_[p] p).powRadius r) := by
  set r' := (frob ℂ_[p] p).powRadius r
  have h1 : tn (ha i) r ^ p = (𝓣).extNorm r' (topRad r') ((frob ℂ_[p] p).extFrob r (rep (ha i) r)) := by
    have := (frob ℂ_[p] p).extNorm_extFrob r (topRad r) (rep (ha i) r)
    rw [frob_a, pow_one] at this
    rw [tn, ← this]
    rfl
  obtain ⟨j, -, hj⟩ := exists_extNorm_sum_le (topRad r') (s := Finset.univ) ⟨i, Finset.mem_univ i⟩
    (fun j => (p : (𝓣).RobbaExt r') * awayToExt p r' (algebraMap _ 𝔸 (C i j)) * rep (ha j) r')
  refine ⟨j, ?_⟩
  rw [h1, extFrob_rep C hy ha i r]
  refine hj.trans ?_
  rw [(𝓣).extNorm_mul, (𝓣).extNorm_mul, ← awayToExt_natCast, extNorm_awayToExt, extNorm_awayToExt,
    map_natCast, gn_natCast_p (K := ℂ_[p]) (topRad r').2.1]
  have hr' : ((topRad r' : Set.Ioc (0 : ℝ) r') : ℝ) = (r : ℝ) ^ p := coe_powRadius r
  have hC1 := gn_algebraMap_le_one (K := ℂ_[p]) (p := p) (topRad r').2.1 (rad_lt_one r' (topRad r')).le (C i j)
  have hg0 := gn_nonneg (K := ℂ_[p]) (p := p) (topRad r').2.1 (algebraMap _ 𝔸 (C i j))
  rw [hr'] at hC1 hg0 ⊢
  have hnn := tn_nonneg (ha j) r'
  calc (r : ℝ) ^ p * gn ℂ_[p] p ((r : ℝ) ^ p) (algebraMap _ 𝔸 (C i j)) *
        (𝓣).extNorm r' (topRad r') (rep (ha j) r')
      ≤ (r : ℝ) ^ p * 1 * tn (ha j) r' := by
        have hr0 : (0 : ℝ) ≤ (r : ℝ) ^ p := pow_nonneg r.2.1.le _
        gcongr
        exact le_rfl
    _ = (r : ℝ) ^ p * tn (ha j) r' := by ring

include hy in

theorem exists_tn_pow_pow_le (k : ℕ) : ∀ (i : Fin m) (r : Set.Ioo (0 : ℝ) 1),
    ∃ j, tn (ha i) r ^ (p ^ k) ≤
      (r : ℝ) ^ (k * p ^ k) * tn (ha j) ((frob ℂ_[p] p).powRadius^[k] r) := by
  induction k with
  | zero => intro i r; exact ⟨i, by simp⟩
  | succ k ih =>
    intro i r
    obtain ⟨j₁, h₁⟩ := exists_tn_pow_le C hy ha i r
    obtain ⟨j₂, h₂⟩ := ih j₁ ((frob ℂ_[p] p).powRadius r)
    refine ⟨j₂, ?_⟩
    rw [Function.iterate_succ_apply]
    have hr0 : (0 : ℝ) ≤ r := r.2.1.le
    calc tn (ha i) r ^ (p ^ (k + 1)) = (tn (ha i) r ^ p) ^ (p ^ k) := by rw [pow_succ', pow_mul]
      _ ≤ ((r : ℝ) ^ p * tn (ha j₁) ((frob ℂ_[p] p).powRadius r)) ^ (p ^ k) :=
          pow_le_pow_left₀ (pow_nonneg (tn_nonneg _ _) _) h₁ _
      _ = (r : ℝ) ^ (p * p ^ k) * tn (ha j₁) ((frob ℂ_[p] p).powRadius r) ^ (p ^ k) := by
          rw [mul_pow, ← pow_mul]
      _ ≤ (r : ℝ) ^ (p * p ^ k) * ((((frob ℂ_[p] p).powRadius r : Set.Ioo (0 : ℝ) 1) : ℝ) ^
            (k * p ^ k) * tn (ha j₂) ((frob ℂ_[p] p).powRadius^[k] ((frob ℂ_[p] p).powRadius r))) :=
          mul_le_mul_of_nonneg_left h₂ (pow_nonneg hr0 _)
      _ = (r : ℝ) ^ ((k + 1) * p ^ (k + 1)) *
            tn (ha j₂) ((frob ℂ_[p] p).powRadius^[k] ((frob ℂ_[p] p).powRadius r)) := by
          rw [coe_powRadius, ← pow_mul, ← mul_assoc, ← pow_add]
          congr 2
          ring

end Decay

end WABridge

end GroundTheory.PAdicHodge
end
end
