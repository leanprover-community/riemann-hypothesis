module

public import GroundTheory.PAdicHodge.ACrisBdRGalois
public import GroundTheory.PAdicHodge.BCrisPlusInvariants
public import GroundTheory.PAdicHodge.FontaineLemma
public import GroundTheory.PAdicHodge.FundamentalSeqLog
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt 𝒪 p
local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}

theorem exists_untilt_eq_of_cp (π : 𝒪) : ∃ x : 𝒪♭, PreTilt.untilt x = π := by
  have hp0 : 0 < p := hp.out.pos
  have roots (z : 𝒪) : ∃ r : 𝒪, r ^ p = z := by
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0
    have hnorm : ‖r‖ ^ p ≤ 1 := by
      rw [← norm_pow r p, hr]
      exact mem_normInteger.1 z.2
    have hmem := mem_normInteger.2 ((pow_le_one_iff_of_nonneg (norm_nonneg r) hp0.ne').1 hnorm)
    let r' : 𝒪 := ⟨r, hmem⟩
    exact ⟨r', Subtype.ext ((SubmonoidClass.coe_pow r' p).trans hr)⟩
  choose root hroot using roots
  let y : ℕ → 𝒪 := fun n => root^[n] π
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => by
    simp only [y, Function.iterate_succ_apply', hroot]
  exact ⟨IsPerfectoidField.ofCompatible p y hy, IsPerfectoidField.untilt_ofCompatible p y hy⟩

theorem exists_phi_eq_p_mul_theta_sub_mem (c : 𝒪) :
    ∃ u : ACris ℂ_[p] p, phi (K := ℂ_[p]) (p := p) u = (p : ACris ℂ_[p] p) * u ∧
      theta (K := ℂ_[p]) (p := p) u - (p : 𝒪) ^ 2 * c ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  obtain ⟨x, hx⟩ := exists_untilt_eq_of_cp (p := p) (1 + (p : 𝒪) ^ 2 * c)
  have h1 : PreTilt.untilt x - 1 = (p : 𝒪) ^ 2 * c := by
    rw [hx, add_sub_cancel_left]
  have hmem : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)} := by
    rw [h1, Ideal.mem_span_singleton]
    exact ⟨p * c, by rw [pow_two, mul_assoc]⟩
  exact ⟨logTeich (K := ℂ_[p]) hmem, phi_logTeich (K := ℂ_[p]) hmem,
    theta_logTeich_sub_mem (K := ℂ_[p]) hmem h1⟩

private theorem exists_eigenvector_of_approximation {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* R) (θ : R →+* S) (q : R) (r : S)
    [IsPrecomplete (Ideal.span {q}) R] [IsHausdorff (Ideal.span {q}) R]
    [IsHausdorff (Ideal.span {r}) S] (hf : f q = q) (hθ : θ q = r)
    (hApprox : ∀ c : S, ∃ u : R, f u = q * u ∧ θ u - r ^ 2 * c ∈ Ideal.span {r ^ 3})
    (c : S) : ∃ u : R, f u = q * u ∧ θ u = r ^ 2 * c := by
  choose g hgf hgθ using hApprox
  have he : ∀ c, ∃ e : S, θ (g c) = r ^ 2 * c - r ^ 3 * e := fun c => by
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hgθ c)
    exact ⟨-e, by linear_combination -he⟩
  choose e he using he
  set cs : ℕ → S := fun j => e^[j] c with hcs
  have hcs1 : ∀ j, e (cs j) = cs (j + 1) := fun j => by
    simp only [hcs, Function.iterate_succ_apply']
  set a : ℕ → R := fun j => q ^ j * g (cs j) with ha_def
  have ha : ∀ k, ∃ N, ∀ n, N ≤ n → a n ∈ Ideal.span {q} ^ k := fun k => ⟨k, fun n hn => by
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hn))⟩
  obtain ⟨s, hs⟩ := exists_isAdicSum ha
  refine ⟨s, ?_, ?_⟩
  · have hle : Ideal.span {q} ≤ (Ideal.span {q}).comap f := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hf]
      exact Ideal.mem_span_singleton_self _
    have h1 := (hs.map f hle).congr (b := fun n => q * a n) (fun n => by
      simp only [ha_def, map_mul f, map_pow f, hf, hgf]
      exact mul_left_comm _ _ _)
    exact h1.unique (hs.mul_left _)
  · have hle : Ideal.span {q} ≤ (Ideal.span {r}).comap θ := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hθ]
      exact Ideal.mem_span_singleton_self _
    have h1 := hs.map θ hle
    have htel : ∀ M, ∑ j ∈ Finset.range M, θ (a j) =
        r ^ 2 * c - r ^ (M + 2) * cs M := by
      intro M
      induction M with
      | zero =>
        rw [Finset.sum_range_zero]
        exact (sub_self (r ^ 2 * c)).symm
      | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [ha_def]
        rw [map_mul θ, map_pow θ, hθ, he, hcs1]
        ring
    have h2 : IsAdicSum (Ideal.span {r}) (fun n => θ (a n)) (r ^ 2 * c) :=
        fun k => ⟨k, fun M hM => by
      rw [htel, sub_sub_cancel, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2
        (pow_dvd_pow _ (Nat.le_add_right_of_le hM)))⟩
    exact h1.unique h2

theorem exists_phi_eq_p_mul_theta_eq (c : 𝒪) :
    ∃ u : ACris ℂ_[p] p, phi (K := ℂ_[p]) (p := p) u = (p : ACris ℂ_[p] p) * u ∧
      theta (K := ℂ_[p]) (p := p) u = (p : 𝒪) ^ 2 * c := by
  let f := phi (K := ℂ_[p]) (p := p)
  let θ := theta (K := ℂ_[p]) (p := p)
  exact exists_eigenvector_of_approximation f θ (p : ACris ℂ_[p] p) (p : 𝒪)
    (map_natCast f p) (map_natCast θ p) (exists_phi_eq_p_mul_theta_sub_mem (p := p)) c

section Plus

local notation "𝔹" => BDeRhamPlus 𝒪 p
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p


theorem phiPlus_eq_of_mul_eq {y : (BCrisPlus ℂ_[p] p)} {a : ACris ℂ_[p] p} {k m : ℕ}
    (hy : y * (p : (BCrisPlus ℂ_[p] p)) ^ k = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) a)
    (ha : phi (K := ℂ_[p]) (p := p) a = (p : ACris ℂ_[p] p) ^ m * a) :
    phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y := by
  let f := phiPlus ℂ_[p] p
  let A := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)
  let q : BCrisPlus ℂ_[p] p := p
  have hu : IsUnit (q ^ k) := isUnit_p_bCrisPlus.pow k
  change f y = q ^ m * y
  apply hu.mul_right_cancel
  calc
    f y * q ^ k = f (y * q ^ k) := by rw [map_mul f, map_pow f, map_natCast f]
    _ = f (A a) := congrArg f hy
    _ = A (phi (K := ℂ_[p]) (p := p) a) := phiPlus_algebraMap (K := ℂ_[p]) (p := p) a
    _ = q ^ m * (y * q ^ k) := by
      rw [ha, map_mul A, map_pow A, map_natCast A, ← hy]
    _ = (q ^ m * y) * q ^ k := (mul_assoc _ _ _).symm



theorem exists_phiPlus_eq_theta_eq (c : ℂ_[p]) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) * y ∧ θdR (iotaPlus ℂ_[p] p y) = c := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(p : ℂ_[p]) ^ N * c‖ ≤ 1 := by
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, by simp only [mul_zero, norm_zero, zero_le_one]⟩
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hc))
      (norm_natCast_p_lt_one (p := p))
    refine ⟨N, ?_⟩
    rw [norm_mul, norm_pow]
    calc ‖(p : ℂ_[p])‖ ^ N * ‖c‖ ≤ ‖c‖⁻¹ * ‖c‖ :=
          mul_le_mul_of_nonneg_right hN.le (norm_nonneg c)
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.2 hc)
  let c' : 𝒪 := ⟨(p : ℂ_[p]) ^ N * c, mem_normInteger.2 hN⟩
  obtain ⟨u, hφ, hθ⟩ := exists_phi_eq_p_mul_theta_eq (p := p) c'
  obtain ⟨y, hy⟩ : ∃ y : (BCrisPlus ℂ_[p] p), y * (p : (BCrisPlus ℂ_[p] p)) ^ (N + 2) = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) u :=
    ⟨algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) u * Ring.inverse (p : (BCrisPlus ℂ_[p] p)) ^ (N + 2), by
      rw [mul_assoc, ← mul_pow, Ring.inverse_mul_cancel _ isUnit_p_bCrisPlus, one_pow, mul_one]⟩
  refine ⟨y, by simpa only [pow_one] using
    phiPlus_eq_of_mul_eq (p := p) hy (m := 1) (by simpa only [pow_one] using hφ), ?_⟩
  let f := (θdR).comp (iotaPlus ℂ_[p] p)
  have hp0 : (p : ℂ_[p]) ^ (N + 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  change f y = c
  apply mul_right_cancel₀ hp0
  calc
    f y * (p : ℂ_[p]) ^ (N + 2) = f (y * (p : BCrisPlus ℂ_[p] p) ^ (N + 2)) := by
      rw [map_mul f, map_pow f, map_natCast f]
    _ = (theta (K := ℂ_[p]) (p := p) u : ℂ_[p]) :=
      (congrArg f hy).trans (thetaField_iotaPlus_algebraMap (K := ℂ_[p]) (p := p) u)
    _ = (p : ℂ_[p]) ^ 2 * ((p : ℂ_[p]) ^ N * c) := by
      rw [hθ, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast]
    _ = c * (p : ℂ_[p]) ^ (N + 2) := by
      rw [mul_left_comm, ← mul_assoc, ← pow_add]
      exact mul_comm _ _



theorem exists_phiPlus_eq_pow_theta_eq {m : ℕ} (hm : 1 ≤ m) (c : ℂ_[p]) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y ∧ θdR (iotaPlus ℂ_[p] p y) = c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨y1, h1, h1'⟩ := exists_phiPlus_eq_theta_eq (p := p) c
  obtain ⟨y0, h0, h0'⟩ := exists_phiPlus_eq_theta_eq (p := p) 1
  refine ⟨y1 * y0 ^ k, ?_, ?_⟩
  · let f := phiPlus ℂ_[p] p
    change f (y1 * y0 ^ k) = _
    rw [map_mul f, map_pow f, h1, h0, mul_pow, pow_succ']
    exact mul_mul_mul_comm _ _ _ _
  · let f := (θdR).comp (iotaPlus ℂ_[p] p)
    have hf1 : f y1 = c := h1'
    have hf0 : f y0 = 1 := h0'
    change f (y1 * y0 ^ k) = c
    rw [map_mul f, map_pow f, hf1, hf0, one_pow, mul_one]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

abbrev periodTPlus : (BCrisPlus ℂ_[p] p) := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)


theorem phiPlus_periodTPlus : phiPlus ℂ_[p] p (periodTPlus hε) = (p : (BCrisPlus ℂ_[p] p)) * periodTPlus hε := by
  let A := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)
  let t := periodT (K := ℂ_[p]) hε
  calc
    phiPlus ℂ_[p] p (A t) = A (phi (K := ℂ_[p]) (p := p) t) :=
      phiPlus_algebraMap (K := ℂ_[p]) (p := p) t
    _ = A ((p : ACris ℂ_[p] p) * t) := congrArg A (phi_periodT_eq_mul (K := ℂ_[p]) hε)
    _ = (p : BCrisPlus ℂ_[p] p) * A t := by rw [map_mul A, map_natCast A]


theorem iotaPlus_periodTPlus : iotaPlus ℂ_[p] p (periodTPlus hε) = fontaineT ε hε := by
  exact (iotaPlus_algebraMap (K := ℂ_[p]) (p := p) (periodT (K := ℂ_[p]) hε)).trans
    (iota_periodT (p := p) hε)


include hζ in
theorem mem_span_fontaineT_of_theta_eq_zero {r : 𝔹} (hr : θdR r = 0) :
    r ∈ Ideal.span {fontaineT ε hε} := by
  have hker : r ∈ RingHom.ker θdR := RingHom.mem_ker.mpr hr
  have heq := (IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[p]) (p := p)).symm.trans
    (maximalIdeal_eq_span_fontaineT hε hζ)
  exact heq ▸ hker

private theorem map_add_mul_pow_of_eigenvectors {R : Type*} [CommRing R] (f : R →+* R)
    {q y t z : R} {m n k : ℕ} (hm : n + k = m) (hy : f y = q ^ m * y)
    (ht : f t = q * t) (hz : f z = q ^ k * z) :
    f (y + t ^ n * z) = q ^ m * (y + t ^ n * z) := by
  rw [map_add f, map_mul f, map_pow f, hy, ht, hz, mul_pow, mul_mul_mul_comm, ← pow_add, hm, mul_add]

private theorem map_sub_mem_span_pow_succ {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {t y z : R} {s w d : S} {n : ℕ} (ht : f t = s) (hd : d * s ^ n = f y - w)
    (h : d + f z ∈ Ideal.span {s}) :
    f (y + t ^ n * z) - w ∈ Ideal.span {s ^ (n + 1)} := by
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 h
  refine Ideal.mem_span_singleton'.2 ⟨e, ?_⟩
  rw [map_add f, map_mul f, map_pow f, ht, add_sub_right_comm, ← hd, mul_comm d,
    ← mul_add, ← he, pow_succ]
  exact mul_left_comm e _ s

include hζ in
theorem exists_phiPlus_eq_pow_iotaPlus_sub_mem {m n : ℕ} (hnm : n ≤ m) (w : 𝔹) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y ∧
      iotaPlus ℂ_[p] p y - w ∈ Ideal.span {fontaineT ε hε ^ n} := by
  induction n with
  | zero =>
    refine ⟨0, by rw [map_zero (phiPlus ℂ_[p] p), mul_zero], ?_⟩
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  | succ n ih =>
    have hnm' : n ≤ m := (Nat.le_succ n).trans hnm
    obtain ⟨y, hy, hyw⟩ := ih hnm'
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hyw
    obtain ⟨z, hz, hz'⟩ := exists_phiPlus_eq_pow_theta_eq (p := p) (m := m - n)
      (Nat.le_sub_of_add_le' hnm) (-θdR d)
    refine ⟨y + periodTPlus hε ^ n * z, ?_, ?_⟩
    · exact map_add_mul_pow_of_eigenvectors (phiPlus ℂ_[p] p) (n := n)
        (Nat.add_sub_of_le hnm') hy (phiPlus_periodTPlus hε) hz
    · have h0 : θdR (d + iotaPlus ℂ_[p] p z) = 0 := by
        rw [map_add θdR, hz', add_neg_cancel]
      exact map_sub_mem_span_pow_succ (iotaPlus ℂ_[p] p) (z := z)
        (iotaPlus_periodTPlus hε) hd (mem_span_fontaineT_of_theta_eq_zero hε hζ h0)

end Plus

end ACris

end GroundTheory.PAdicHodge
