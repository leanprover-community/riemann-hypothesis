import Mathlib
import GroundTheory.PAdicHodge.AInfXi
import GroundTheory.PAdicHodge.AInfTopology
import GroundTheory.PAdicHodge.ACrisFrobFixed
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.FontainePhiPowerSubgroups
import GroundTheory.PAdicHodge.FontaineLemmaPeriod
import GroundTheory.PAdicHodge.BCrisRegular

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace AInf

open _root_.WittVector

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem fontaineTheta_frobenius_pow_succ_xi {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    θ ((φ ^ (n + 1)) (xi ε)) = p := by
  rw [pow_succ, RingAut.mul_apply, frobeniusEquiv_xi, map_sum, map_sum]
  simp only [map_pow, WittVector.frobeniusEquiv_pow_teichmuller, fontaineTheta_teichmuller, hε,
    one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem fontaineTheta_frobenius_pow_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    θ ((φ ^ n) (mu ε)) = 0 := by
  rw [mu, map_sub, map_one, WittVector.frobeniusEquiv_pow_teichmuller, map_sub, map_one,
    fontaineTheta_teichmuller, map_pow, hε, one_pow, sub_self]

theorem fontaineTheta_frobenius_pow_mul_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (b : AInf K p)
    (n : ℕ) : θ ((φ ^ n) (mu ε * b)) = 0 := by
  rw [map_mul, map_mul, fontaineTheta_frobenius_pow_mu hε, zero_mul]

theorem natCast_ne_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : (p : 𝒪) ≠ 0 := by
  intro h
  apply norm_natCast_ne_zero hε hζ
  have h2 : ((p : 𝒪) : K) = (p : K) := by simp
  rw [← h2, h, ZeroMemClass.coe_zero, norm_zero]

variable (K p) in

noncomputable def kerThetaFrob : Ideal (AInf K p) :=
  ⨅ n : ℕ, RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ ^ n : AInf K p ≃+* AInf K p) : AInf K p →+* AInf K p))

theorem mem_kerThetaFrob {a : AInf K p} : a ∈ kerThetaFrob K p ↔ ∀ n : ℕ, θ ((φ ^ n) a) = 0 := by
  simp only [kerThetaFrob, Ideal.mem_iInf, RingHom.mem_ker, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply]

theorem exists_mul_frobeniusEquiv_symm_pow_mu_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) (N : ℕ) :
    ∀ a : AInf K p, (∀ n : ℕ, θ ((φ ^ n) a) = 0) →
      ∃ c : AInf K p, a * ((φ).symm ^ N) (mu ε) = mu ε * c := by
  induction N with
  | zero => exact fun a _ => ⟨a, by rw [pow_zero, RingAut.one_apply, mul_comm]⟩
  | succ N ih =>
    intro a ha
    have h0 : a ∈ RingHom.ker θ := by
      rw [RingHom.mem_ker]
      simpa using ha 0
    rw [ker_fontaineTheta_eq_span_xi hε hζ, Ideal.mem_span_singleton'] at h0
    obtain ⟨a₁, rfl⟩ := h0
    have hp0 := natCast_ne_zero hε hζ
    have h1 : ∀ n : ℕ, θ ((φ ^ n) (φ a₁)) = 0 := by
      intro n
      have h := ha (n + 1)
      rw [map_mul, map_mul, fontaineTheta_frobenius_pow_succ_xi hε n, mul_eq_zero] at h
      rw [← RingAut.mul_apply, ← pow_succ]
      exact h.resolve_right hp0
    obtain ⟨c, hc⟩ := ih _ h1
    refine ⟨(φ).symm c, ?_⟩
    have h2 := congrArg (φ).symm hc
    rw [map_mul, map_mul, RingEquiv.symm_apply_apply] at h2
    calc a₁ * xi ε * ((φ).symm ^ (N + 1)) (mu ε)
        = xi ε * (a₁ * (φ).symm (((φ).symm ^ N) (mu ε))) := by
          rw [pow_succ', RingAut.mul_apply]; ring
      _ = xi ε * ((φ).symm (mu ε) * (φ).symm c) := by rw [h2]
      _ = mu ε * (φ).symm c := by
          conv_rhs => rw [mu_eq_xi_mul ε]
          ring

theorem constantCoeff_mu (ε : 𝒪♭) : WittVector.constantCoeff (mu ε : AInf K p) = ε - 1 := by
  rw [mu, map_sub, map_one]
  exact congrArg (· - 1) (teichmuller_coeff_zero p ε)

theorem constantCoeff_frobeniusEquiv_symm_pow_mu (ε : 𝒪♭) (N : ℕ) :
    WittVector.constantCoeff (((φ).symm ^ N) (mu ε) : AInf K p) =
      ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ N) ε - 1 := by
  rw [frobeniusEquiv_symm_pow_mu, map_sub, map_one]
  exact congrArg (· - 1) (teichmuller_coeff_zero p _)

theorem norm_frobeniusEquiv_symm_pow_sub_one_pow (ε : 𝒪♭) (N : ℕ) :
    ‖((_root_.frobeniusEquiv 𝒪♭ p).symm ^ N) ε - 1‖ ^ p ^ N = ‖ε - 1‖ := by
  rw [← norm_pow, sub_pow_char_pow, one_pow, frobeniusEquiv_symm_pow_apply_pow]

theorem sub_one_dvd_coeff_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {a : AInf K p}
    (ha : ∀ n : ℕ, θ ((φ ^ n) a) = 0) : ε - 1 ∣ WittVector.constantCoeff a := by
  rw [preTilt_dvd_iff_norm_le]
  set r := ‖ε - 1‖ with hr
  set x := ‖WittVector.constantCoeff a‖ with hx
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 (ne_one_of_untilt_ne_one hζ))
  have key : ∀ N : ℕ, x ^ p ^ N * r ≤ r ^ p ^ N := by
    intro N
    obtain ⟨c, hc⟩ := exists_mul_frobeniusEquiv_symm_pow_mu_eq hε hζ N a ha
    have h := congrArg (fun y : AInf K p => ‖WittVector.constantCoeff y‖ ^ p ^ N) hc
    simp only [map_mul, norm_mul, mul_pow, constantCoeff_mu,
      constantCoeff_frobeniusEquiv_symm_pow_mu, norm_frobeniusEquiv_symm_pow_sub_one_pow] at h
    rw [h]
    calc r ^ p ^ N * ‖WittVector.constantCoeff c‖ ^ p ^ N ≤ r ^ p ^ N * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) (preTilt_norm_le_one _)
      _ = r ^ p ^ N := mul_one _
  by_contra hlt
  push_neg at hlt
  set q := x / r with hq
  have hq1 : 1 < q := by rw [hq, one_lt_div hr0]; exact hlt
  have hbound : ∀ N : ℕ, q ^ p ^ N * r ≤ 1 := by
    intro N
    have h := key N
    have hxq : x = q * r := by rw [hq, div_mul_cancel₀ _ hr0.ne']
    rw [hxq, mul_pow] at h
    have hrN : 0 < r ^ p ^ N := pow_pos hr0 _
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (r * (q - 1)))
  have hpN : (N : ℝ) < (p ^ N : ℕ) := by exact_mod_cast Nat.lt_pow_self hp.out.one_lt
  have hB := one_add_mul_le_pow (a := q - 1) (by linarith) (p ^ N)
  rw [add_sub_cancel] at hB
  have h3 := hbound N
  have hq0 : 0 < q - 1 := by linarith
  have h4 : (1 : ℝ) / (r * (q - 1)) < ((p ^ N : ℕ) : ℝ) := hN.trans hpN
  rw [div_lt_iff₀ (mul_pos hr0 hq0)] at h4
  push_cast at h4 hB
  nlinarith

theorem mem_span_mu_of_forall {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {a : AInf K p}
    (ha : ∀ n : ℕ, θ ((φ ^ n) a) = 0) : a ∈ Ideal.span {mu ε} := by
  have hp0 := natCast_ne_zero hε hζ
  have hJ : kerThetaFrob K p ≤ Ideal.span {mu ε} := by
    refine le_span_singleton_of_forall_mem_eq (π := (p : AInf K p)) fun x hx => ?_
    rw [mem_kerThetaFrob] at hx
    obtain ⟨β, hβ⟩ := sub_one_dvd_coeff_zero hε hζ hx
    obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p (x - mu ε * teichmuller p β)
    have h0 : (x - mu ε * teichmuller p β).coeff 0 = 0 := by
      change _root_.WittVector.constantCoeff (x - mu ε * teichmuller p β) = 0
      rw [map_sub, map_mul, constantCoeff_mu, hβ]
      change _ - _ * (teichmuller p β).coeff 0 = 0
      rw [teichmuller_coeff_zero, sub_self]
    rw [h0, teichmuller_zero, zero_add] at hv
    have hxv : x = teichmuller p β * mu ε + v * p := by linear_combination hv
    refine ⟨teichmuller p β, v, ?_, hxv⟩
    rw [mem_kerThetaFrob]
    intro n
    have h := hx n
    rw [hxv, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
      fontaineTheta_frobenius_pow_mu hε, mul_zero, zero_add, map_natCast, map_natCast,
      mul_eq_zero] at h
    exact h.resolve_right hp0
  exact hJ (mem_kerThetaFrob.2 ha)


end AInf

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

section Iteration

variable {A R ι : Type*} [CommRing A] [CommRing R]

theorem exists_eq_add_mul_of_forall {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) (hf : f a = r) (X : R) (ψ : ι → R)
    (h : ∀ y, ∃ b : A, ∃ s : R, ∃ y' : ι, ψ y = f b + X * s + r * ψ y') (y : ι) :
    ∃ b : A, ∃ s : R, ψ y = f b + X * s :=
  _root_.GroundTheory.Variant₂.N1.exists_eq_add_mul_of_forall' f hf X ψ h y

end Iteration

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem exists_p_mul_eq_frobenius_sub {ξ : AInf K p} (hξ : ξ ∈ RingHom.ker θ) :
    ∃ X : ACrisZero K p, (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p := by
  obtain ⟨c, hc⟩ := exists_frobenius_eq ξ
  refine ⟨⟨algebraMap (AInf K p) 𝔸 c + ((p - 1).factorial : 𝔸) * dpow p ξ - 1,
    sub_mem (add_mem (Subalgebra.algebraMap_mem _ c)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_mem hξ p))) (one_mem _)⟩, ?_⟩
  have h1 := factorial_mul_dpow (K := K) p ξ
  have h2 : algebraMap (AInf K p) 𝔸 (φ ξ) =
      algebraMap (AInf K p) 𝔸 ξ ^ p + (p : 𝔸) * algebraMap (AInf K p) 𝔸 c := by
    rw [hc, map_add, map_pow, map_mul, map_natCast]
  have h3 : (p : 𝔸) * ((p - 1).factorial : 𝔸) = (p.factorial : 𝔸) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
  show (p : 𝔸) * (algebraMap (AInf K p) 𝔸 c + ((p - 1).factorial : 𝔸) * dpow p ξ - 1) = _
  linear_combination dpow p ξ * h3 + h1 - h2

theorem exists_phiAway_eq_add_mul {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ})
    {X : ACrisZero K p} (hX : (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p) {y : 𝔸}
    (hy : y ∈ ACrisZero K p) :
    ∃ b : AInf K p, ∃ s ∈ ACrisZero K p,
      phiAway K p y = algebraMap (AInf K p) 𝔸 b + (X : 𝔸) * s := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [hξ] at hx
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨w, hw⟩ := exists_natCast_mul_eq_pow (K := K) (p := p) (Nat.factorial_ne_zero n)
      (factorization_factorial_le (p := p) n)

    have hd : dpow n (φ ξ) = algebraMap (AInf K p) 𝔸 w * (1 + (X : 𝔸)) ^ n := by
      rw [dpow_eq_iff, ← mul_assoc, ← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, hw,
        map_pow, map_natCast, ← mul_pow, mul_add, mul_one, hX, add_sub_cancel]
    set g := ∑ i ∈ Finset.range n, (1 + (X : 𝔸)) ^ i
    have hg : g ∈ ACrisZero K p :=
      Subalgebra.sum_mem _ fun i _ => Subalgebra.pow_mem _ (add_mem (one_mem _) X.2) i
    have hgeom : (1 + (X : 𝔸)) ^ n = 1 + (X : 𝔸) * g := by
      have := geom_sum_mul (1 + (X : 𝔸)) n
      rw [add_sub_cancel_left] at this
      rw [mul_comm, this]; ring
    refine ⟨w * φ d ^ n, algebraMap (AInf K p) 𝔸 w * g * algebraMap (AInf K p) 𝔸 (φ d) ^ n,
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ w) hg)
        (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) n), ?_⟩
    rw [phiAway_dpow, map_mul, mul_comm (φ d) (φ ξ), dpow_mul, hd, hgeom, map_mul, map_pow]
    ring
  | algebraMap r =>
    exact ⟨φ r, 0, zero_mem _, by rw [phiAway_algebraMap, mul_zero, add_zero]⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, z₁, hz₁, e₁⟩ := h₁
    obtain ⟨w₂, z₂, hz₂, e₂⟩ := h₂
    exact ⟨w₁ + w₂, z₁ + z₂, add_mem hz₁ hz₂, by rw [map_add, e₁, e₂, map_add]; ring⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, z₁, hz₁, e₁⟩ := h₁
    obtain ⟨w₂, z₂, hz₂, e₂⟩ := h₂
    refine ⟨w₁ * w₂, algebraMap (AInf K p) 𝔸 w₁ * z₂ + z₁ * algebraMap (AInf K p) 𝔸 w₂ +
      (X : 𝔸) * z₁ * z₂, ?_, by rw [map_mul, e₁, e₂, map_mul]; ring⟩
    exact add_mem (add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hz₂)
      (Subalgebra.mul_mem _ hz₁ (Subalgebra.algebraMap_mem _ _)))
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ X.2 hz₁) hz₂)

set_option maxHeartbeats 1600000 in

theorem exists_phi_eq_add_mul [CharZero K] {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ})
    {X : ACrisZero K p} (hX : (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p)
    (y : ACris K p) :
    ∃ b : AInf K p, ∃ s : ACris K p, phi K p y =
      algebraMap (AInf K p) (ACris K p) b + algebraMap (ACrisZero K p) (ACris K p) X * s := by
  refine exists_eq_add_mul_of_forall (a := (p : AInf K p)) (r := (p : ACris K p))
    (algebraMap (AInf K p) (ACris K p)) (map_natCast _ p) _ (phi K p) (fun y => ?_) y
  obtain ⟨y₀, z₁, rfl⟩ := exists_eq_add_p_pow_mul 1 y
  obtain ⟨b, s, hs, e⟩ := exists_phiAway_eq_add_mul hξ hX y₀.2
  refine ⟨b, algebraMap (ACrisZero K p) (ACris K p) ⟨s, hs⟩, z₁, ?_⟩
  have e' : phiZero K p y₀ = algebraMap (AInf K p) (ACrisZero K p) b + X * ⟨s, hs⟩ :=
    Subtype.ext (by rw [coe_phiZero, e]; rfl)
  have hof : phi K p (algebraMap (ACrisZero K p) (ACris K p) y₀) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y₀) := phi_of y₀
  have hb : algebraMap (AInf K p) (ACris K p) b =
      algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) b) :=
    AdicCompletion.algebraMap_apply _ b
  rw [map_add, map_mul, pow_one, map_natCast, hof, e', map_add, map_mul, hb]

theorem frobenius_xi_sub_mem_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    φ (AInf.xi ε) - p ∈ Ideal.span {AInf.mu (K := K) ε} := by
  refine AInf.mem_span_mu_of_forall hε hζ fun n => ?_
  rw [map_sub, map_natCast, map_sub, map_natCast, ← RingAut.mul_apply, ← pow_succ,
    AInf.fontaineTheta_frobenius_pow_succ_xi hε n, sub_self]

section Theta

variable [CharZero K]

theorem theta_phi_iterate_algebraMap (n : ℕ) (w : AInf K p) :
    theta K p ((phi K p)^[n] (algebraMap (AInf K p) (ACris K p) w)) = θ ((φ ^ n) w) := by
  rw [phi_iterate_algebraMap, theta_algebraMap]

set_option maxHeartbeats 1600000 in

theorem p_mul_phi_mem_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : ACris K p}
    (hy : ∀ n : ℕ, theta K p ((phi K p)^[n] y) = 0) :
    (p : ACris K p) * phi K p y ∈
      Ideal.span {algebraMap (AInf K p) (ACris K p) (AInf.mu ε)} := by
  have hξ := AInf.ker_fontaineTheta_eq_span_xi hε hζ
  have hξk : AInf.xi ε ∈ RingHom.ker θ := by rw [hξ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨X, hX⟩ := exists_p_mul_eq_frobenius_sub hξk
  obtain ⟨b, s, e⟩ := exists_phi_eq_add_mul hξ hX y
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (frobenius_xi_sub_mem_span_mu hε hζ)

  have hXc : (p : ACris K p) * algebraMap (ACrisZero K p) (ACris K p) X =
      algebraMap (AInf K p) (ACris K p) (AInf.mu ε) * algebraMap (AInf K p) (ACris K p) d := by
    have h1 : (p : ACrisZero K p) * X =
        algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε * d) := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, SubringClass.coe_natCast, hX, Subalgebra.coe_algebraMap, mul_comm,
        hd, map_sub, map_natCast]
    have hof : algebraMap (ACrisZero K p) (ACris K p) ((p : ACrisZero K p) * X) =
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) := by
      rw [h1]
      exact (AdicCompletion.algebraMap_apply _ _).symm
    rw [map_mul, map_natCast] at hof
    rw [hof, map_mul]
  have hp0 := AInf.natCast_ne_zero hε hζ

  have e2 : (p : ACris K p) * phi K p y =
      algebraMap (AInf K p) (ACris K p) ((p : AInf K p) * b) +
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) * s := by
    rw [e, mul_add, ← mul_assoc, hXc, map_mul, map_mul, map_natCast]
  have hb : ∀ n : ℕ, θ ((φ ^ n) b) = 0 := by
    intro n
    set Φ := phi K p ^ n with hΦ
    have hΦa : ∀ w, theta K p (Φ (algebraMap (AInf K p) (ACris K p) w)) = θ ((φ ^ n) w) :=
      fun w => by rw [hΦ, RingHom.coe_pow, theta_phi_iterate_algebraMap]
    have h : theta K p (Φ (phi K p y)) = 0 := by
      rw [hΦ, RingHom.coe_pow, ← Function.iterate_succ_apply]
      exact hy (n + 1)
    have hl : theta K p (Φ ((p : ACris K p) * phi K p y)) = 0 := by
      rw [map_mul, map_natCast, map_mul, map_natCast, h, mul_zero]
    have hr : theta K p (Φ (algebraMap (AInf K p) (ACris K p) ((p : AInf K p) * b) +
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) * s)) = (p : 𝒪) * θ ((φ ^ n) b) := by
      rw [map_add, map_mul Φ, map_add, map_mul (theta K p), hΦa, hΦa,
        AInf.fontaineTheta_frobenius_pow_mul_mu hε, zero_mul, add_zero, map_mul, map_natCast,
        map_mul, map_natCast]
    rw [e2, hr] at hl
    exact (mul_eq_zero.1 hl).resolve_left hp0
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 (AInf.mem_span_mu_of_forall hε hζ hb)
  rw [Ideal.mem_span_singleton']
  refine ⟨(p : ACris K p) * algebraMap (AInf K p) (ACris K p) β +
    algebraMap (AInf K p) (ACris K p) d * s, ?_⟩
  rw [e2, ← hβ]
  simp only [map_mul, map_natCast]
  ring

end Theta

end ACris

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := K) p

theorem iterate_phiPlus_algebraMap (n : ℕ) (x : ACris K p) :
    (phiPlus K p)^[n] (algebraMap (ACris K p) (BCrisPlus K p) x) =
      algebraMap (ACris K p) (BCrisPlus K p) ((phi K p)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap, Function.iterate_succ_apply']

theorem thetaField_iotaPlus_algebraMap (x : ACris K p) :
    θdR (iotaPlus K p (algebraMap (ACris K p) (BCrisPlus K p) x)) = (theta K p x : K) := by
  rw [iotaPlus_algebraMap, thetaField_iota]

theorem theta_phi_iterate_eq_zero_of_mul_eq {y : BCrisPlus K p} {a : ACris K p} {k : ℕ}
    (hya : y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ k) =
      algebraMap (ACris K p) (BCrisPlus K p) a)
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) (n : ℕ) :
    theta K p ((phi K p)^[n] a) = 0 := by
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← thetaField_iotaPlus_algebraMap, ← iterate_phiPlus_algebraMap, ← hya,
    ← RingHom.coe_pow, map_mul, map_mul, map_mul, RingHom.coe_pow, hy n, zero_mul]

set_option maxHeartbeats 1600000 in

theorem phiPlus_mem_span_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : BCrisPlus K p}
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) :
    phiPlus K p y ∈ Ideal.span {algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)} := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris K p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk] at hs
  have ha := theta_phi_iterate_eq_zero_of_mul_eq hs hy

  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (p_mul_phi_mem_span_mu hε hζ ha)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (mu_mem_span_periodT (K := K) hε hζ)
  have hpa : (p : ACris K p) * phi K p a = periodT hε * (c * w) := by
    rw [← hw, ← hc]; ring

  have h1 := congrArg (phiPlus K p) hs
  rw [map_mul, phiPlus_algebraMap, phiPlus_algebraMap, map_pow, map_natCast] at h1
  have hu : IsUnit (algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1))) :=
    IsLocalization.map_units (BCrisPlus K p)
      (⟨(p : ACris K p) ^ (k + 1), k + 1, rfl⟩ : Submonoid.powers (p : ACris K p))
  rw [Ideal.mem_span_singleton']
  refine ⟨algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹, ?_⟩
  have h2 : phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) =
      algebraMap (ACris K p) (BCrisPlus K p) (periodT hε) *
        algebraMap (ACris K p) (BCrisPlus K p) (c * w) := by
    rw [pow_succ, map_mul, ← mul_assoc, h1, ← map_mul, mul_comm (phi K p a), hpa, map_mul]
  calc algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹ *
        algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)
      = phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) *
          ↑hu.unit⁻¹ := by rw [h2]; ring
    _ = phiPlus K p y := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]

set_option maxHeartbeats 1600000 in

theorem mem_span_xi_of_forall_imp {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    (H : ∀ y : BCrisPlus K p, (∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) →
      y ∈ Ideal.span {algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)})
    {z : BCrisPlus K p} (hz : θdR (iotaPlus K p z) = 0) :
    z ∈ Ideal.span {algebraMap (AInf K p) (BCrisPlus K p) (AInf.xi ε)} := by
  set v : AInf K p := (φ).symm (AInf.mu ε) with hv
  set V : BCrisPlus K p := algebraMap (AInf K p) (BCrisPlus K p) v with hV
  have hVa : ∀ w : AInf K p, algebraMap (AInf K p) (BCrisPlus K p) w =
      algebraMap (ACris K p) (BCrisPlus K p) (algebraMap (AInf K p) (ACris K p) w) :=
    fun w => IsScalarTower.algebraMap_apply _ _ _ w
  have hθV : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] V)) = θ ((φ ^ n) v) := by
    intro n
    rw [hV, hVa, iterate_phiPlus_algebraMap, thetaField_iotaPlus_algebraMap,
      theta_phi_iterate_algebraMap]

  have hyz : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] (V * z))) = 0 := by
    intro n
    rw [← RingHom.coe_pow, map_mul, map_mul, map_mul, RingHom.coe_pow, hθV]
    rcases n with _ | n
    · rw [Function.iterate_zero_apply, hz, mul_zero]
    · rw [pow_succ, RingAut.mul_apply, hv, RingEquiv.apply_symm_apply,
        AInf.fontaineTheta_frobenius_pow_mu hε, ZeroMemClass.coe_zero, zero_mul]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (H _ hyz)
  obtain ⟨u, -, hu⟩ := exists_periodT_eq_mu_mul_unit hε hζ

  have e : V * z = V * (algebraMap (AInf K p) (BCrisPlus K p) (AInf.xi ε) *
      (algebraMap (ACris K p) (BCrisPlus K p) u * a)) := by
    rw [← ha, hu, map_mul, ← hVa, AInf.mu_eq_xi_mul ε, map_mul, ← hv, ← hV]
    ring
  have hV0 : iotaPlus K p V ≠ 0 := by
    intro h0
    have h1 := hθV 0
    rw [Function.iterate_zero_apply, h0, map_zero, pow_zero, RingAut.one_apply, hv,
      AInf.frobeniusEquiv_symm_mu, map_sub, map_one, fontaineTheta_teichmuller] at h1
    apply hζ
    have h2 : ((PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) - 1 :
        normInteger K) : K) = 0 := h1.symm
    rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, sub_eq_zero] at h2
    exact Subtype.ext (by rw [h2, OneMemClass.coe_one])
  have e2 := congrArg (iotaPlus K p) e
  rw [map_mul, map_mul (iotaPlus K p) V] at e2
  have e3 := iotaPlus_injective (K := K) (p := p) (mul_left_cancel₀ hV0 e2)
  rw [Ideal.mem_span_singleton']
  exact ⟨algebraMap (ACris K p) (BCrisPlus K p) u * a, by rw [e3]; ring⟩

end ACris

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

section Abstract

variable {R S T L : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing L]

theorem iterate_pow_mul_eq_of_map_eq (f : R →+* R) {t c : R} (hc : f c = c) (ht : f t = c * t)
    (x : R) (m n : ℕ) : f^[n] (t ^ m * x) = (c ^ n * t) ^ m * f^[n] x := by
  have hct : ∀ n : ℕ, f^[n] t = c ^ n * t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hc, ht, pow_succ]; ring
  rw [iterate_map_mul, iterate_map_pow, hct]

theorem iterate_map_eq_pow_mul (f : R →+* R) {t c : R} (hc : f c = c) (ht : f t = c * t) (n : ℕ) :
    f^[n] t = c ^ n * t := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hc, ht, pow_succ]; ring

theorem exists_map_eq_pow_mul_of_mul_eq (g : S →+* R) {t c u : R} (ht : IsUnit t) {q : S}
    (hq : IsUnit q) (hgq : g q = c) {w : S} {m : ℕ} (h : g w * t = (c * t) ^ (m + 1) * u) :
    ∃ z : S, g z = t ^ m * u := by
  have hqm : IsUnit (q ^ (m + 1)) := hq.pow _
  refine ⟨w * ↑hqm.unit⁻¹, ?_⟩
  have h1 : c ^ (m + 1) * g ↑hqm.unit⁻¹ = 1 := by
    rw [← hgq, ← map_pow, ← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : g w = c ^ (m + 1) * t ^ m * u :=
    ht.mul_right_cancel (by rw [h]; ring)
  rw [map_mul, h2]
  linear_combination t ^ m * u * h1

theorem map_eq_zero_of_eq_pow_mul {D : Type*} [CommRing D] (ι : S →+* T) (j : D →+* T)
    (hj : Function.Injective j) (θ : D →+* L) {a : D} {c t x : S} {c' τ κ : D} {n k : ℕ}
    (h : j a = ι ((c ^ n * t) ^ (k + 1) * x)) (hc : ι c = j c') (ht : ι t = j τ) (hx : ι x = j κ)
    (hτ : θ τ = 0) : θ a = 0 := by
  have e : a = (c' ^ n * τ) ^ (k + 1) * κ := hj (by rw [h]; simp only [map_mul, map_pow, hc, ht, hx])
  rw [e, map_mul, map_pow, map_mul, hτ, mul_zero, zero_pow (Nat.succ_ne_zero k), zero_mul]

theorem exists_eq_iterate_of_step (g : S →+* R) (f : R → R) (t : R) (P : R → Prop)
    (hP : ∀ x, P x → P (f x))
    (step : ∀ (m : ℕ) (x : R), P x → (∃ y, g y = t ^ (m + 1) * x) → ∃ z, g z = t ^ m * f x) :
    ∀ (m : ℕ) (x : R), P x → (∃ y, g y = t ^ m * x) → ∃ z, g z = f^[m] x := by
  intro m
  induction m with
  | zero =>
    rintro x - ⟨y, hy⟩
    exact ⟨y, by rw [hy, pow_zero, one_mul, Function.iterate_zero_apply]⟩
  | succ m ih =>
    intro x hx hex
    obtain ⟨z, hz⟩ := ih (f x) (hP x hx) (step m x hx hex)
    exact ⟨z, by rw [hz, Function.iterate_succ_apply]⟩

theorem eq_pow_mul_of_map_eq {D : Type*} [CommRing D] (ι : S →+* T) (j : D →+* T)
    (hj : Function.Injective j) {a : D} {t x : S} {τ κ : D} {m : ℕ} (h : j a = ι (t ^ m * x))
    (ht : ι t = j τ) (hx : ι x = j κ) : a = τ ^ m * κ :=
  hj (by rw [h, map_mul, map_pow, ht, hx, map_mul, map_pow])

theorem map_pow_mul_pow_mul (g : S →+* R) {c : S} {c' : R} (hc : g c = c') (n m : ℕ) (t z : S) :
    g ((c ^ n * t) ^ m * z) = (c' ^ n * g t) ^ m * g z := by
  rw [map_mul, map_pow, map_mul, map_pow, hc]

def homogEval {A : Type*} [CommRing A] (f : A →+* S) (P : A[X]) (y s : S) : S :=
  ∑ i ∈ Finset.range (P.natDegree + 1), f (P.coeff i) * y ^ i * s ^ (P.natDegree - i)

theorem homogEval_mul {A : Type*} [CommRing A] (f : A →+* S) (P : A[X]) (s z : S) :
    homogEval f P (s * z) s = s ^ P.natDegree * P.eval₂ f z := by
  rw [homogEval, eval₂_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc f (P.coeff i) * (s * z) ^ i * s ^ (P.natDegree - i)
      = f (P.coeff i) * z ^ i * (s ^ i * s ^ (P.natDegree - i)) := by ring
    _ = s ^ P.natDegree * (f (P.coeff i) * z ^ i) := by rw [pow_mul_pow_sub _ hi']; ring

theorem map_homogEval {A : Type*} [CommRing A] (f : A →+* S) (P : A[X]) (y s : S) (g : S →+* T)
    (f' : A →+* T) (hf : ∀ a, g (f a) = f' a) :
    g (homogEval f P y s) = homogEval f' P (g y) (g s) := by
  simp only [homogEval, map_sum, map_mul, map_pow, hf]

theorem Localization.Away.exists_algebraMap_eq_pow_mul (t : R) (x : Localization.Away t) :
    ∃ (m : ℕ) (y : R), algebraMap R (Localization.Away t) y =
      algebraMap R (Localization.Away t) t ^ m * x := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) x
  obtain ⟨m, hm⟩ := s.2
  refine ⟨m, a, ?_⟩
  rw [← hs, ← hm, map_pow, mul_comm]

theorem map_pow_mul_pow (g : S →+* R) {c : S} {c' : R} (hc : g c = c') (n m : ℕ) (t : S) :
    g ((c ^ n * t) ^ m) = (c' ^ n * g t) ^ m := by
  rw [map_pow, map_mul, map_pow, hc]

theorem map_eq_zero_of_pow_mul_eq_zero [IsDomain T] (g : S →+* T) {c z : S} {d : ℕ}
    (h : c ^ d * z = 0) (hc : g c ≠ 0) : g z = 0 := by
  have h1 := congrArg g h
  rw [map_mul, map_pow, map_zero] at h1
  exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hc)

end Abstract

namespace ACris

section Generic

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField F p]
variable {ε : PreTilt (normInteger F) p} (hε : PreTilt.untilt ε = 1)

abbrev periodTCris : BCris hε :=
  algebraMap (BCrisPlus F p) (BCris hε) (algebraMap (ACris F p) (BCrisPlus F p) (periodT hε))

theorem isUnit_periodTCris : IsUnit (periodTCris hε) :=
  IsLocalization.Away.algebraMap_isUnit _

theorem phiB_periodTCris : phiB hε (periodTCris hε) = (p : BCris hε) * periodTCris hε :=
  ((phiB_algebraMap hε _).trans
    (congrArg _ ((phiPlus_algebraMap _).trans (congrArg _ (phi_periodT_eq_mul hε))))).trans
    (by simp only [map_mul, map_natCast])

theorem iterate_phiB_algebraMap (n : ℕ) (y : BCrisPlus F p) :
    (phiB hε)^[n] (algebraMap (BCrisPlus F p) (BCris hε) y) =
      algebraMap (BCrisPlus F p) (BCris hε) ((phiPlus F p)^[n] y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, phiB_algebraMap]

theorem algebraMap_iterate_phiPlus_eq {x : BCris hε} {m : ℕ} {y : BCrisPlus F p}
    (hy : algebraMap (BCrisPlus F p) (BCris hε) y = periodTCris hε ^ m * x) (n : ℕ) :
    algebraMap (BCrisPlus F p) (BCris hε) ((phiPlus F p)^[n] y) =
      ((p : BCris hε) ^ n * periodTCris hε) ^ m * (phiB hε)^[n] x :=
  (iterate_phiB_algebraMap hε n y).symm.trans ((congrArg (phiB hε)^[n] hy).trans
    (iterate_pow_mul_eq_of_map_eq (phiB hε) (map_natCast _ p) (phiB_periodTCris hε) x m n))


theorem exists_algebraMap_eq_periodTCris_pow_mul (x : BCris hε) :
    ∃ (m : ℕ) (y : BCrisPlus F p), algebraMap (BCrisPlus F p) (BCris hε) y = periodTCris hε ^ m * x :=
  Localization.Away.exists_algebraMap_eq_pow_mul _ x


variable [CharZero F]
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger F) p) p).symm ε) ≠ 1)

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_algebraMap_eq_periodTCris_pow_mul_phiB {x : BCris hε} {m : ℕ} {y : BCrisPlus F p}
    (hy : algebraMap (BCrisPlus F p) (BCris hε) y = periodTCris hε ^ (m + 1) * x)
    (hθ : ∀ n : ℕ, IsPerfectoidField.thetaBDeRhamPlusField (K := F) p
      (iotaPlus F p ((phiPlus F p)^[n] y)) = 0) :
    ∃ z : BCrisPlus F p, algebraMap (BCrisPlus F p) (BCris hε) z =
      periodTCris hε ^ m * phiB hε x := by
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (phiPlus_mem_span_periodT hε hζ hθ)
  have hp1 : IsUnit (p : BCrisPlus F p) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus F p) (p : ACris F p)
    simpa only [map_natCast] using this

  have h : algebraMap (BCrisPlus F p) (BCris hε) w * periodTCris hε =
      ((p : BCris hε) * periodTCris hε) ^ (m + 1) * phiB hε x :=
    (map_mul _ w _).symm.trans ((congrArg _ hw).trans ((phiB_algebraMap hε y).symm.trans
      ((congrArg (phiB hε) hy).trans (iterate_pow_mul_eq_of_map_eq (phiB hε) (map_natCast _ p)
        (phiB_periodTCris hε) x (m + 1) 1) |>.trans (by rw [pow_one]; rfl))))
  exact exists_map_eq_pow_mul_of_mul_eq _ (isUnit_periodTCris hε) hp1 (map_natCast _ p) h

end Generic

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

theorem phiB_algebraMap_padic (q : ℚ_[p]) :
    phiB hε (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q)) =
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q) :=
  (phiB_algebraMap hε _).trans (congrArg _ (phiPlus_algebraMap_padic q))

theorem mem_unramifiedClosure_of_minpoly_eq {β β₁ : PadicAlgCl p}
    (h : minpoly ℚ_[p] β = minpoly ℚ_[p] β₁) (h₁ : β₁ ∈ unramifiedClosure p) :
    β ∈ unramifiedClosure p := by
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 h
  have hτ' : τ β₁ = β := hτ
  rw [← hτ']
  exact gal_mem_unramifiedClosure τ h₁

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem galB_iterate_phiB (σ : Gal(PadicAlgCl p/K)) {x : BCris hε} (hx : galB hε σ x = x)
    (n : ℕ) : galB hε σ ((phiB hε)^[n] x) = (phiB hε)^[n] x := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    exact (congrArg (galB hε σ) (Function.iterate_succ_apply' _ _ _)).trans
      ((phiB_galB hε σ _).symm.trans ((congrArg (phiB hε) ih).trans
        (Function.iterate_succ_apply' _ _ _).symm))

theorem iotaB_periodTCris :
    iotaB hε hζ (periodTCris hε) = algebraMap 𝔹 𝔹dR (iota ℂ_[p] p (periodT hε)) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ (iotaPlus_algebraMap _))

theorem thetaField_iota_periodT :
    IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p (iota ℂ_[p] p (periodT hε)) = 0 :=
  (thetaField_iota _).trans (by rw [theta_periodT]; rfl)

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_bCrisPlus_fixed_eq_of_mem_maxUnramified {x : BCris hε} {k : PadicAlgCl p}
    (hk : k ∈ maxUnramified p K) (hx : iotaB hε hζ x = algebraMap 𝔹 𝔹dR (algClToBdR p k)) :
    ∃ y' : BCrisPlus ℂ_[p] p, (∀ σ : Gal(PadicAlgCl p/K), σ • y' = y') ∧
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y' = x := by
  obtain ⟨y', hyfix, hy'⟩ := exists_bCrisPlus_fixed hk
  exact ⟨y', hyfix, iotaB_injective hε hζ
    ((iotaB_algebraMap hε hζ y').trans ((congrArg _ hy').trans hx.symm))⟩

variable [FiniteDimensional ℚ_[p] K]

include hζ in
set_option maxHeartbeats 1600000 in

theorem thetaField_iotaPlus_iterate_eq_zero {x : BCris hε}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) {m : ℕ} {y : BCrisPlus ℂ_[p] p}
    (hy : algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = periodTCris hε ^ (m + 1) * x) (n : ℕ) :
    IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p
      (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[n] y)) = 0 := by
  obtain ⟨k, hk⟩ := bCris_fixed hε hζ ((phiB hε)^[n] x) fun σ => galB_iterate_phiB hε σ (hx σ) n
  exact map_eq_zero_of_eq_pow_mul (iotaB hε hζ) (algebraMap 𝔹 𝔹dR)
    (IsFractionRing.injective 𝔹 𝔹dR) (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p)
    ((iotaB_algebraMap hε hζ _).symm.trans (congrArg _ (algebraMap_iterate_phiPlus_eq hε hy n)))
    ((map_natCast _ p).trans (map_natCast _ p).symm) (iotaB_periodTCris hε hζ)
    (hk.trans (algebraMap_intermediateField_bDeRham K k)) (thetaField_iota_periodT hε)

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_iterate_phiB_eq (m : ℕ) (x : BCris hε)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x)
    (hxy : ∃ y : BCrisPlus ℂ_[p] p,
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = periodTCris hε ^ m * x) :
    ∃ z : BCrisPlus ℂ_[p] p, algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) z = (phiB hε)^[m] x :=
  exists_eq_iterate_of_step (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (phiB hε) (periodTCris hε)
    (fun x => ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x)
    (fun x hx σ => (phiB_galB hε σ x).symm.trans (congrArg (phiB hε) (hx σ)))
    (fun _ _ hx ⟨_, hy⟩ => exists_algebraMap_eq_periodTCris_pow_mul_phiB hε hζ hy
      (thetaField_iotaPlus_iterate_eq_zero hε hζ hx hy)) m x hx hxy

theorem iterate_phiPlus_algebraMap_padic (n : ℕ) (q : ℚ_[p]) :
    (phiPlus ℂ_[p] p)^[n] (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q) =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap_padic]

include hζ in

theorem algebraMap_bCrisPlus_bCris_injective :
    Function.Injective (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) := fun a b h =>
  iotaPlus_injective (K := ℂ_[p]) (p := p) (IsFractionRing.injective 𝔹 𝔹dR
    ((iotaB_algebraMap hε hζ a).symm.trans ((congrArg (iotaB hε hζ) h).trans
      (iotaB_algebraMap hε hζ b))))

include hζ in

theorem iota_periodT_ne_zero : iota ℂ_[p] p (periodT hε) ≠ 0 := by
  rw [iota_periodT]
  exact fontaineT_ne_zero hε hζ

include hζ in
set_option maxHeartbeats 1600000 in

theorem aeval_minpoly_eq_zero_of_iterate {y x₁ : BCrisPlus ℂ_[p] p} {m : ℕ}
    {β β₁ : PadicAlgCl p}
    (hιy : iotaPlus ℂ_[p] p y = iota ℂ_[p] p (periodT hε) ^ m * algClToBdR p β)
    (hιx₁ : iotaPlus ℂ_[p] p x₁ = algClToBdR p β₁)
    (hφy : (phiPlus ℂ_[p] p)^[m] y = ((p : BCrisPlus ℂ_[p] p) ^ m *
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) ^ m * x₁) :
    aeval β₁ (minpoly ℚ_[p] β) = 0 := by
  obtain ⟨t', ht'⟩ : ∃ t', algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε) = t' :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, iota ℂ_[p] p (periodT hε) = τ := ⟨_, rfl⟩
  rw [ht'] at hφy
  rw [hτdef] at hιy
  have hτ : iotaPlus ℂ_[p] p t' = τ := by rw [← ht', ← hτdef]; exact iotaPlus_algebraMap _
  obtain ⟨P, hP⟩ : ∃ P, minpoly ℚ_[p] β = P := ⟨_, rfl⟩
  rw [hP]
  obtain ⟨f, hf⟩ : ∃ f, algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) = f := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, homogEval f P y (t' ^ m) = R := ⟨_, rfl⟩

  have hιs : iotaPlus ℂ_[p] p (t' ^ m) = τ ^ m := (map_pow _ _ _).trans (congrArg (· ^ m) hτ)
  have hιR : iotaPlus ℂ_[p] p R = 0 := by
    have e1 : iotaPlus ℂ_[p] p R = homogEval (algebraMap ℚ_[p] 𝔹) P (iotaPlus ℂ_[p] p y)
        (iotaPlus ℂ_[p] p (t' ^ m)) := by
      rw [← hR]
      exact map_homogEval f P y (t' ^ m) (iotaPlus ℂ_[p] p) (algebraMap ℚ_[p] 𝔹)
        (fun q => by rw [← hf]; exact iotaPlus_algebraMap_padic q)
    have e2 : aeval (algClToBdR p β) P = 0 := by
      rw [aeval_algHom_apply, ← hP, minpoly.aeval, map_zero]
    rw [e1, hιy, hιs, homogEval_mul, ← aeval_def, e2, mul_zero]
  have hR0 : R = 0 := iotaPlus_injective (K := ℂ_[p]) (p := p) (hιR.trans (map_zero _).symm)

  obtain ⟨c, hc⟩ : ∃ c, ((p : BCrisPlus ℂ_[p] p) ^ m * t') ^ m = c := ⟨_, rfl⟩
  rw [hc] at hφy
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, phiPlus ℂ_[p] p ^ m = Φ := ⟨_, rfl⟩
  have hΦf : ∀ q, Φ (f q) = f q := fun q => by
    rw [← hΦ, ← hf]
    exact (congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) _).trans
      (iterate_phiPlus_algebraMap_padic m q)
  have hΦy : Φ y = c * x₁ := by
    rw [← hΦ]
    exact (congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) y).trans hφy
  have hφt : (phiPlus ℂ_[p] p)^[m] t' = (p : BCrisPlus ℂ_[p] p) ^ m * t' := by
    rw [← ht']
    exact iterate_map_eq_pow_mul (phiPlus ℂ_[p] p) (map_natCast _ p)
      ((phiPlus_algebraMap _).trans ((congrArg _ (phi_periodT_eq_mul hε)).trans
        (by simp only [map_mul, map_natCast]))) m
  have hΦs : Φ (t' ^ m) = c := by
    rw [← hΦ, ← hc]
    exact (congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) _).trans
      ((iterate_map_pow (phiPlus ℂ_[p] p) m t' m).trans (congrArg (· ^ m) hφt))
  have hΦR : c ^ P.natDegree * P.eval₂ f x₁ = 0 := by
    have e1 : Φ R = homogEval f P (Φ y) (Φ (t' ^ m)) := by
      rw [← hR]
      exact map_homogEval f P y (t' ^ m) Φ f hΦf
    rw [hΦy, hΦs, homogEval_mul, hR0, map_zero] at e1
    exact e1.symm

  have hιc : iotaPlus ℂ_[p] p c ≠ 0 := by
    rw [← hc, map_pow_mul_pow (iotaPlus ℂ_[p] p) (map_natCast _ p) m m t', hτ]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus
      (K := ℂ_[p]) p).ne_zero) (by rw [← hτdef]; exact iota_periodT_ne_zero hε hζ))
  have h1 : iotaPlus ℂ_[p] p (aeval x₁ P) = 0 := by
    rw [aeval_def, hf]
    exact map_eq_zero_of_pow_mul_eq_zero (iotaPlus ℂ_[p] p) hΦR hιc
  have h2 := aeval_algHom_apply (iotaPlusAlg (p := p)) x₁ P
  rw [iotaPlusAlg_apply, iotaPlusAlg_apply, hιx₁, h1, aeval_algHom_apply] at h2
  exact (injective_algClToBdR p) (h2.trans (map_zero _).symm)

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_bCrisPlus_fixed_eq_of_iterate {x : BCris hε}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) {m : ℕ} {y x₁ : BCrisPlus ℂ_[p] p}
    (hy : algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = periodTCris hε ^ m * x)
    (hx₁ : algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) x₁ = (phiB hε)^[m] x) :
    ∃ y' : BCrisPlus ℂ_[p] p, (∀ σ : Gal(PadicAlgCl p/K), σ • y' = y') ∧
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y' = x := by
  obtain ⟨k, hk⟩ := bCris_fixed hε hζ x hx
  obtain ⟨k₁, hk₁⟩ := bCris_fixed hε hζ ((phiB hε)^[m] x) fun σ => galB_iterate_phiB hε σ (hx σ) m
  have hk' := hk.trans (algebraMap_intermediateField_bDeRham K k)
  have hk₁' := hk₁.trans (algebraMap_intermediateField_bDeRham K k₁)
  have hιy : iotaPlus ℂ_[p] p y = iota ℂ_[p] p (periodT hε) ^ m * algClToBdR p k :=
    eq_pow_mul_of_map_eq (iotaB hε hζ) (algebraMap 𝔹 𝔹dR) (IsFractionRing.injective 𝔹 𝔹dR)
      ((iotaB_algebraMap hε hζ y).symm.trans (congrArg _ hy)) (iotaB_periodTCris hε hζ) hk'
  have hιx₁ : iotaPlus ℂ_[p] p x₁ = algClToBdR p k₁ :=
    IsFractionRing.injective 𝔹 𝔹dR
      ((iotaB_algebraMap hε hζ x₁).symm.trans ((congrArg _ hx₁).trans hk₁'))
  have hφy : (phiPlus ℂ_[p] p)^[m] y = ((p : BCrisPlus ℂ_[p] p) ^ m *
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) ^ m * x₁ :=
    algebraMap_bCrisPlus_bCris_injective hε hζ ((algebraMap_iterate_phiPlus_eq hε hy m).trans
      ((congrArg (fun z => ((p : BCris hε) ^ m * periodTCris hε) ^ m * z) hx₁.symm).trans
        (map_pow_mul_pow_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (map_natCast _ p) m m
          (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) x₁).symm))
  have hroot := aeval_minpoly_eq_zero_of_iterate hε hζ hιy hιx₁ hφy
  have hint : IsIntegral ℚ_[p] (k : PadicAlgCl p) := Algebra.IsIntegral.isIntegral _
  have hmin : minpoly ℚ_[p] (k : PadicAlgCl p) = minpoly ℚ_[p] (k₁ : PadicAlgCl p) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
  have hk0 : (k : PadicAlgCl p) ∈ maxUnramified p K :=
    mem_maxUnramified.2 ⟨k.2, mem_unramifiedClosure_of_minpoly_eq hmin
      (mem_unramifiedClosure_of_iotaPlus_eq hιx₁)⟩
  exact exists_bCrisPlus_fixed_eq_of_mem_maxUnramified hε hζ hk0 hk'

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_bCrisPlus_fixed_eq (x : BCris hε)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) :
    ∃ y : BCrisPlus ℂ_[p] p, (∀ σ : Gal(PadicAlgCl p/K), σ • y = y) ∧
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = x := by
  obtain ⟨m, a, hs'⟩ := exists_algebraMap_eq_periodTCris_pow_mul hε x
  obtain ⟨x₁, hx₁⟩ := exists_iterate_phiB_eq hε hζ m x hx ⟨a, hs'⟩
  exact exists_bCrisPlus_fixed_eq_of_iterate hε hζ hx hs' hx₁

include hζ in
set_option maxHeartbeats 1600000 in

theorem fixed_bCris_eq_image :
    {x : BCris hε | ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x} =
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) ''
        MulAction.fixedPoints Gal(PadicAlgCl p/K) (BCrisPlus ℂ_[p] p) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_bCrisPlus_fixed_eq hε hζ x hx
    exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, rfl⟩ σ
    exact (galB_algebraMap hε σ y).trans (congrArg _ (hy σ))

include hζ in
set_option maxHeartbeats 1600000 in

theorem bCris_fixed_mem_maxUnramified (x : BCris hε)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) :
    ∃ k ∈ maxUnramified p K, iotaB hε hζ x = algebraMap 𝔹 𝔹dR (algClToBdR p k) := by
  obtain ⟨y, hy, hyx⟩ := exists_bCrisPlus_fixed_eq hε hζ x hx
  obtain ⟨k, hk, hyk⟩ := bCrisPlus_fixed y hy
  exact ⟨k, hk, (congrArg (iotaB hε hζ) hyx).symm.trans
    ((iotaB_algebraMap hε hζ y).trans (congrArg _ hyk))⟩

end ACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

section Algebra

theorem algebraMap_padic_bCris (q : ℚ_[p]) :
    algebraMap ℚ_[p] (BCris hε) q =
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q) :=
  rfl

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem gal_smul_algebraMap_padic_plus (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q :=
  iotaPlus_injective (K := ℂ_[p]) (p := p) (by
    rw [iotaPlus_gal_smul, iotaPlus_algebraMap_padic, gal_smul_algebraMap_bdR])

set_option maxHeartbeats 1600000 in

theorem galB_algebraMap_padic (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    galB hε σ (algebraMap ℚ_[p] (BCris hε) q) = algebraMap ℚ_[p] (BCris hε) q :=
  (galB_algebraMap hε σ _).trans (congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
    (gal_smul_algebraMap_padic_plus σ q))

set_option maxHeartbeats 1600000 in

theorem smulCommClass_galBAction :
    letI := galBAction (K := K) hε
    SMulCommClass Gal(PadicAlgCl p/K) ℚ_[p] (BCris hε) :=
  let _ := galBAction (K := K) hε
  ⟨fun σ q x => (congrArg (galB hε σ) (Algebra.smul_def q x)).trans
    ((map_mul (galB hε σ) _ _).trans ((congrArg (· * galB hε σ x) (galB_algebraMap_padic hε σ q)).trans
      (Algebra.smul_def q (galB hε σ x)).symm))⟩

include hζ in

theorem isDomain_bCris : IsDomain (BCris hε) :=
  Function.Injective.isDomain (iotaB hε hζ) (iotaB_injective hε hζ)

end Algebra

section Invariants

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem algClToBdRField_apply (k : PadicAlgCl p) :
    algClToBdRField p k = algebraMap 𝔹 𝔹dR (algClToBdR p k) :=
  rfl

theorem algClToBdRField_injective : Function.Injective (algClToBdRField p) :=
  (algClToBdRField p).injective

include hζ in
set_option maxHeartbeats 1600000 in

theorem image_iotaB_fixedPoints [FiniteDimensional ℚ_[p] K] :
    letI := galBAction (K := K) hε
    iotaB hε hζ '' MulAction.fixedPoints Gal(PadicAlgCl p/K) (BCris hε) =
      algClToBdRField p '' (maxUnramified p K : Set (PadicAlgCl p)) := by
  let _ := galBAction (K := K) hε
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hxk⟩ := bCris_fixed_mem_maxUnramified hε hζ x hx
    exact ⟨k, hk, hxk.symm⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hxk⟩ := exists_bCris_fixed hε hζ hk
    exact ⟨x, hx, hxk⟩

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_iotaB_eq_iff {β : PadicAlgCl p} :
    (∃ x : BCris hε, iotaB hε hζ x = algClToBdRField p β) ↔ β ∈ unramifiedClosure p := by
  constructor
  · rintro ⟨x, hx⟩
    let L : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.adjoin ℚ_[p] {β}
    haveI : FiniteDimensional ℚ_[p] L :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
    have hβL : β ∈ L := IntermediateField.subset_adjoin ℚ_[p] {β} (Set.mem_singleton β)
    have hfix : ∀ σ : Gal(PadicAlgCl p/L), galB hε σ x = x := fun σ => by
      have hσ : σ β = β := σ.commutes ⟨β, hβL⟩
      apply iotaB_injective hε hζ
      calc iotaB hε hζ (galB hε σ x) = σ • iotaB hε hζ x := iotaB_galB hε hζ σ x
        _ = σ • algClToBdRField p β := by rw [hx]
        _ = algClToBdRField p β := by
          rw [algClToBdRField_apply, gal_smul_algebraMap_bDeRham, gal_smul_algClToBdR, hσ]
        _ = iotaB hε hζ x := hx.symm
    obtain ⟨k, hk, hxk⟩ := bCris_fixed_mem_maxUnramified hε hζ x hfix
    have hβk : β = k := algClToBdRField_injective (hx.symm.trans hxk)
    exact hβk ▸ hk.2
  · intro hβ
    obtain ⟨y, hy⟩ := (mem_algClInBCrisPlus (p := p)).1 (unramifiedClosure_le hβ)
    exact ⟨algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y,
      (iotaB_algebraMap hε hζ y).trans (congrArg _ hy)⟩

end Invariants

end ACris

end GroundTheory.PAdicHodge
end
end
