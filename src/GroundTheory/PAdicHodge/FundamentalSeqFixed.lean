module

public import GroundTheory.PAdicHodge.FundamentalSeqSurj
public import GroundTheory.PAdicHodge.BCrisPlusInvariants
import GroundTheory.PAdicHodge.ACrisFrobFixed
import GroundTheory.PAdicHodge.FontaineLemma
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]

section Residue

theorem prod_range_X_sub_C_zmod :
    ∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ZMod p)) = X ^ p - X := by
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic :=
    (monic_X_pow p).sub_of_left (by rw [degree_X, degree_X_pow]; exact_mod_cast hp.out.one_lt)
  have hr : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    simpa [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p :=
    Polynomial.natDegree_X_pow_sub_X (R := (ZMod p)) hp.out.one_lt
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hr, hdeg, Finset.card_val, Finset.card_univ, ZMod.card])
  rw [hr, ← Finset.prod_eq_multiset_prod] at h
  rw [← h]
  refine Finset.prod_nbij' (fun a => (a : ZMod p)) (fun a => a.val) (fun a _ => Finset.mem_univ _)
    (fun a _ => Finset.mem_range.2 (ZMod.val_lt a)) (fun a ha => ?_) (fun a _ => ZMod.natCast_zmod_val a)
    (fun a _ => rfl)
  exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)

theorem C_dvd_of_map_eq_zero {F : ℤ[X]} (h : F.map (Int.castRingHom (ZMod p)) = 0) :
    C (p : ℤ) ∣ F := by
  rw [C_dvd_iff_dvd_coeff]
  intro i
  have h1 : (F.coeff i : ZMod p) = 0 := by
    have := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f i) h
    simpa only [coeff_map, eq_intCast, coeff_zero] using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1

theorem exists_prod_range_X_sub_C_eq :
    ∃ G : ℤ[X], ∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ℤ)) = X ^ p - X + C (p : ℤ) * G := by
  have hmap : (∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ℤ)) - (X ^ p - X)).map
      (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_prod, sub_eq_zero]
    have e1 : Polynomial.map (Int.castRingHom (ZMod p)) (X ^ p - X) = X ^ p - X := by simp
    rw [e1, ← prod_range_X_sub_C_zmod]
    exact Finset.prod_congr rfl fun i _ => by simp
  obtain ⟨G, hG⟩ := C_dvd_of_map_eq_zero hmap
  exact ⟨G, by rw [← hG]; ring⟩

theorem exists_prod_range_sub_eq (v : 𝒪) :
    ∃ g : 𝒪, ∏ a ∈ Finset.range p, (v - (a : 𝒪)) = v ^ p - v + (p : 𝒪) * g := by
  obtain ⟨G, hG⟩ := exists_prod_range_X_sub_C_eq (p := p)
  refine ⟨aeval v G, ?_⟩
  have h := congrArg (aeval v) hG
  simpa [map_prod] using h

theorem norm_intCast_eq_one {n : ℤ} (hn0 : n ≠ 0) (hn : n.natAbs < p) : ‖(n : ℂ_[p])‖ = 1 := by
  have h1 : ‖(n : ℚ_[p])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one n) (not_lt.1 fun hlt => ?_)
    have hd := Padic.norm_intCast_lt_one_iff.1 hlt
    have := Int.natAbs_dvd_natAbs.2 hd
    simp only [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hn0) this) (by omega)
  have h2 := PadicComplex.norm_extends' (p := p) (n : ℚ_[p])
  rw [h1, PadicComplex.coe_eq, map_intCast, map_intCast] at h2
  exact h2

theorem dvd_iff_norm_le {a b : 𝒪} (hb : b ≠ 0) : b ∣ a ↔ ‖(a : ℂ_[p])‖ ≤ ‖(b : ℂ_[p])‖ := by
  have hb' : (b : ℂ_[p]) ≠ 0 := fun h => hb (Subtype.ext h)
  constructor
  · rintro ⟨c, rfl⟩
    rw [MulMemClass.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (mem_normInteger.1 c.2)
  · intro h
    refine ⟨⟨(a : ℂ_[p]) / b, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    · rw [MulMemClass.coe_mul]
      field_simp

theorem natCast_p_ne_zero' : (p : 𝒪) ≠ 0 := fun h => by
  have := congrArg (fun x : 𝒪 => (x : ℂ_[p])) h
  simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
  exact hp.out.ne_zero this



theorem exists_natCast_dvd_sub_of_dvd_pow_sub {v : 𝒪} (hv : (p : 𝒪) ∣ v ^ p - v) :
    ∃ a : ℕ, a < p ∧ (p : 𝒪) ∣ v - a := by
  obtain ⟨g, hg⟩ := exists_prod_range_sub_eq v
  have hprod : (p : 𝒪) ∣ ∏ a ∈ Finset.range p, (v - (a : 𝒪)) := by
    rw [hg]
    exact dvd_add hv (dvd_mul_right _ _)
  rw [dvd_iff_norm_le natCast_p_ne_zero'] at hprod
  have hnp : ‖((p : 𝒪) : ℂ_[p])‖ < 1 := by
    simpa using norm_natCast_p_lt_one (p := p)
  simp only [SubmonoidClass.coe_finsetProd, norm_prod] at hprod
  have hle : ∀ a : ℕ, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ ≤ 1 := fun a => mem_normInteger.1 (v - a).2
  by_cases hex : ∃ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ < 1
  · obtain ⟨a, ha, hlt⟩ := hex
    refine ⟨a, Finset.mem_range.1 ha, ?_⟩
    rw [dvd_iff_norm_le natCast_p_ne_zero']
    rw [Finset.prod_eq_single_of_mem a ha] at hprod
    · exact hprod
    · intro b hb hba
      have hab : ‖(((a : ℤ) - b : ℤ) : ℂ_[p])‖ = 1 := norm_intCast_eq_one (by omega)
        (by have := Finset.mem_range.1 ha; have := Finset.mem_range.1 hb; omega)
      have e : ((v - (b : 𝒪) : 𝒪) : ℂ_[p]) = ((v - (a : 𝒪) : 𝒪) : ℂ_[p]) +
          (((a : ℤ) - b : ℤ) : ℂ_[p]) := by push_cast; ring
      rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hab]; exact hlt.ne),
        hab, max_eq_right hlt.le]
  · push Not at hex
    have h1 : ∏ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ = 1 :=
      Finset.prod_eq_one fun a ha => le_antisymm (hle a) (hex a ha)
    rw [h1] at hprod
    exact absurd hprod (not_le.2 hnp)

end Residue

section Approx



theorem exists_int_dvd_sub (m : ℕ) : ∀ v : 𝒪, (∃ c : ℕ → 𝒪, ∀ k : ℕ,
    (p : 𝒪) ^ m ∣ v - ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c i ^ p ^ k) →
    ∃ z : ℤ, (p : 𝒪) ^ m ∣ v - z := by
  induction m with
  | zero => intro v _; exact ⟨0, by simp⟩
  | succ m ih =>
    rintro v ⟨c, hc⟩
    have h0 : ∀ k, (p : 𝒪) ∣ v - c 0 ^ p ^ k := fun k => by
      have h := (dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hc k)
      rw [Finset.sum_range_succ', pow_zero, one_mul] at h
      have hs : (p : 𝒪) ∣ ∑ i ∈ Finset.range m, (p : 𝒪) ^ (i + 1) * c (i + 1) ^ p ^ k :=
        Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (dvd_pow_self _ i.succ_ne_zero) _
      convert dvd_add h hs using 1
      ring
    have hv1 : (p : 𝒪) ∣ v ^ p - v := by
      have e1 : (p : 𝒪) ∣ v ^ p - c 0 ^ p := by
        have h := dvd_sub_pow_of_dvd_sub (by simpa using h0 0) 1
        rw [pow_one] at h
        exact (dvd_pow_self (p : 𝒪) two_ne_zero).trans h
      have e2 := h0 1
      rw [pow_one] at e2
      convert dvd_sub e1 e2 using 1
      ring
    obtain ⟨a, hap, ha⟩ := exists_natCast_dvd_sub_of_dvd_pow_sub hv1
    have hca : (p : 𝒪) ∣ c 0 - a := by
      have h := h0 0
      rw [pow_zero, pow_one] at h
      convert dvd_sub ha h using 1
      ring
    have hfa : (p : 𝒪) ∣ (a : 𝒪) ^ p - a := by
      have hz : (p : ℤ) ∣ (a : ℤ) ^ p - a := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.pow_card, sub_self]
      have := map_dvd (Int.castRingHom 𝒪) hz
      simpa using this
    have hak : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (a : 𝒪) ^ p ^ (m + j) - (a : 𝒪) ^ p ^ m := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        have h1 := dvd_sub_pow_of_dvd_sub hfa (m + j)
        have e : ((a : 𝒪) ^ p) ^ p ^ (m + j) = (a : 𝒪) ^ p ^ (m + (j + 1)) := by
          rw [← pow_mul, ← pow_succ']
          rfl
        rw [e] at h1
        have h2 := (pow_dvd_pow (p : 𝒪) (by omega : m + 1 ≤ m + j + 1)).trans h1
        convert dvd_add h2 ihj using 1
        ring
    have hk : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (v - (a : 𝒪) ^ p ^ m) -
        (p : 𝒪) * ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + j) := by
      intro j
      have h1 := hc (m + j)
      rw [Finset.sum_range_succ', pow_zero, one_mul] at h1
      have h2 : (p : 𝒪) ^ (m + 1) ∣ c 0 ^ p ^ (m + j) - (a : 𝒪) ^ p ^ (m + j) :=
        (pow_dvd_pow _ (by omega)).trans (dvd_sub_pow_of_dvd_sub hca (m + j))
      convert dvd_add (dvd_add h1 h2) (hak j) using 1
      simp only [Finset.mul_sum, ← mul_assoc, ← pow_succ']
      ring
    have hpz : (p : 𝒪) ∣ v - (a : 𝒪) ^ p ^ m := by
      have h := dvd_add ((dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hk 0))
        (dvd_mul_right (p : 𝒪) (∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + 0)))
      rwa [sub_add_cancel] at h
    obtain ⟨v', hv'⟩ := hpz
    have hv'c : ∀ k, (p : 𝒪) ^ m ∣
        v' - ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * (c (i + 1) ^ p ^ m) ^ p ^ k := by
      intro k
      have h := hk k
      rw [hv', ← mul_sub, pow_succ'] at h
      have h' := (mul_dvd_mul_iff_left natCast_p_ne_zero').1 h
      have e : ∀ i, c (i + 1) ^ p ^ (m + k) = (c (i + 1) ^ p ^ m) ^ p ^ k := fun i => by
        rw [pow_add, pow_mul]
      simp only [e] at h'
      exact h'
    obtain ⟨z', hz'⟩ := ih v' ⟨fun i => c (i + 1) ^ p ^ m, hv'c⟩
    refine ⟨(a : ℤ) ^ p ^ m + p * z', ?_⟩
    have e : v - (((a : ℤ) ^ p ^ m + p * z' : ℤ) : 𝒪) = (p : 𝒪) * (v' - z') := by
      push_cast
      linear_combination hv'
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hz'

theorem norm_algebraMap_padic (q : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] q‖ = ‖q‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
  exact PadicComplex.norm_extends' p q

theorem isClosed_range_algebraMap_padic : IsClosed (Set.range (algebraMap ℚ_[p] ℂ_[p])) :=
  (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[p] ℂ_[p])
    norm_algebraMap_padic).isUniformInducing.isComplete_range.isClosed



theorem theta_mem_range_of_phi_eq {y : ACris ℂ_[p] p} (hy : phi ℂ_[p] p y = y) :
    ∃ q : ℚ_[p], ((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] q := by
  have happrox : ∀ m : ℕ, ∃ z : ℤ,
      ‖((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) - (z : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simpa using mem_normInteger.1 (theta ℂ_[p] p y).2⟩
    obtain ⟨c, hc⟩ := exists_theta_eq_sum_of_phi_iterate (N := 1) le_rfl
      (by rw [Function.iterate_one]; exact hy) hm
    obtain ⟨z, hz⟩ := exists_int_dvd_sub m (theta ℂ_[p] p y) ⟨c, fun k => by
      obtain ⟨e, he⟩ := hc k
      refine ⟨e, Subtype.ext ?_⟩
      simp only [one_mul] at he
      push_cast
      rw [he]
      ring⟩
    refine ⟨z, ?_⟩
    have h := (dvd_iff_norm_le (pow_ne_zero m natCast_p_ne_zero')).1 hz
    simpa using h
  have hmem : ((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) ∈ closure (Set.range (algebraMap ℚ_[p] ℂ_[p])) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (norm_natCast_p_lt_one (p := p))
    obtain ⟨z, hz⟩ := happrox m
    refine ⟨algebraMap ℚ_[p] ℂ_[p] z, ⟨z, rfl⟩, ?_⟩
    rw [dist_eq_norm, map_intCast]
    exact hz.trans_lt hm
  rw [isClosed_range_algebraMap_padic.closure_eq] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq.symm⟩

end Approx

section Plus

local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p

theorem mem_pow_of_p_pow_mul_phi_eq {a : ACris ℂ_[p] p} {m : ℕ} (hm : 1 ≤ m)
    (ha : (p : ACris ℂ_[p] p) ^ m * phi ℂ_[p] p a = a) (j : ℕ) : a ∈ 𝔭 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ih ⊢
    obtain ⟨b, hb⟩ := ih
    refine ⟨(p : ACris ℂ_[p] p) ^ (m - 1) * phi ℂ_[p] p b, ?_⟩
    conv_rhs => rw [← ha, ← hb]
    rw [map_mul, map_pow, map_natCast]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

private theorem exists_mul_p_pow_eq_algebraMap (y : BCrisPlus ℂ_[p] p) :
    ∃ (k : ℕ) (a : ACris ℂ_[p] p), y * (p : BCrisPlus ℂ_[p] p) ^ k =
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) a := by
  simpa only [map_natCast (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p))] using
    IsLocalization.Away.surj (p : ACris ℂ_[p] p) y

private theorem map_mul_natCast_pow {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (y : R) (n k : ℕ) :
    f (y * (n : R) ^ k) = f y * (n : S) ^ k := by
  rw [map_mul f, map_pow f, map_natCast f]

private theorem eq_zero_of_localized_eigenvector {R S : Type*} [CommRing R] [CommRing S]
    (F : R →+* S) (f : R →+* R) (g : S →+* S) (n : ℕ)
    (hF : Function.Injective F) (hfg : ∀ a, g (F a) = F (f a))
    {y : S} {a : R} {k m : ℕ} (hunit : IsUnit ((n : S) ^ k))
    (ha : y * (n : S) ^ k = F a) (hy : (n : S) ^ m * g y = y)
    (hzero : (n : R) ^ m * f a = a → a = 0) : y = 0 := by
  have hnum : g y * (n : S) ^ k = F (f a) :=
    (map_mul_natCast_pow g y n k).symm.trans ((congrArg g ha).trans (hfg a))
  have he : (n : R) ^ m * f a = a := hF (by
    rw [map_mul F, map_pow F, map_natCast F, ← hnum, ← mul_assoc, hy, ha])
  rw [hzero he, map_zero F] at ha
  exact hunit.mul_left_eq_zero.1 ha

theorem eq_zero_of_p_pow_mul_phiPlus_eq {y : BCrisPlus ℂ_[p] p} {m : ℕ} (hm : 1 ≤ m)
    (hy : (p : BCrisPlus ℂ_[p] p) ^ m * phiPlus ℂ_[p] p y = y) : y = 0 := by
  obtain ⟨k, a, ha⟩ := exists_mul_p_pow_eq_algebraMap y
  exact eq_zero_of_localized_eigenvector
    (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)) (phi ℂ_[p] p) (phiPlus ℂ_[p] p) p
    algebraMap_aCris_injective (phiPlus_algebraMap (K := ℂ_[p]) (p := p))
    (isUnit_p_bCrisPlus.pow k) ha hy fun he => IsHausdorff.haus' (I := 𝔭) a fun j => by
      simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top] using mem_pow_of_p_pow_mul_phi_eq hm he j

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in
theorem iotaPlus_periodTPlus_ne_zero : iotaPlus ℂ_[p] p (periodTPlus hε) ≠ 0 := by
  rw [iotaPlus_periodTPlus]
  exact fontaineT_ne_zero hε hζ


include hζ in
theorem periodTPlus_mul_left_cancel {a b : BCrisPlus ℂ_[p] p}
    (h : periodTPlus hε * a = periodTPlus hε * b) : a = b := by
  let ι := iotaPlus ℂ_[p] p
  exact iotaPlus_injective (K := ℂ_[p]) (p := p) <|
    mul_left_cancel₀ (iotaPlus_periodTPlus_ne_zero hε hζ) <|
      (map_mul ι (periodTPlus hε) a).symm.trans <|
        (congrArg ι h).trans (map_mul ι (periodTPlus hε) b)

private theorem iterate_eq_pow_mul_of_map_eq {R : Type*} [CommRing R] (f : R →+* R)
    {a y : R} (ha : f a = a) (hy : f y = a * y) (k : ℕ) :
    f^[k] y = a ^ k * y := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul f, map_pow f, ha, hy, ← mul_assoc, ← pow_succ]

theorem iterate_phiPlus_eq_pow_mul {y : BCrisPlus ℂ_[p] p} {n : ℕ}
    (hy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y) (k : ℕ) :
    (phiPlus ℂ_[p] p)^[k] y = ((p : BCrisPlus ℂ_[p] p) ^ n) ^ k * y := by
  let f := phiPlus ℂ_[p] p
  exact iterate_eq_pow_mul_of_map_eq f
    ((map_pow f (p : BCrisPlus ℂ_[p] p) n).trans (congrArg (· ^ n) (map_natCast f p))) hy k

private theorem eq_map_div_natCast_pow_of_mul_eq {F K : Type*} [Field F] [Field K]
    (f : F →+* K) {x : K} {q : F} {n k : ℕ} (hn : (n : K) ≠ 0)
    (h : x * (n : K) ^ k = f q) : x = f (q / (n : F) ^ k) := by
  rw [map_div₀ f, map_pow f, map_natCast f]
  exact (eq_div_iff (pow_ne_zero k hn)).2 h

private theorem map_period_factor {R : Type*} [CommRing R] (f : R →+* R) {u t v y a : R}
    (ht : f t = u * t) (htc : Function.Injective (fun x : R => t * x))
    (hv : y = t * v) (hy : f y = a * y) : u * f v = a * v := by
  apply htc
  calc
    t * (u * f v) = f (t * v) := by rw [map_mul f, ht, mul_assoc, mul_left_comm t u]
    _ = a * (t * v) := by rw [← hv, hy]
    _ = t * (a * v) := mul_left_comm _ _ _

include hε hζ in

theorem exists_eq_algebraMap_of_phiPlus_eq {y : BCrisPlus ℂ_[p] p}
    (hy : phiPlus ℂ_[p] p y = y) : ∃ q : ℚ_[p], y = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  let f := phiPlus ℂ_[p] p
  let A := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)
  let P := algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p)
  let θ := (θdR).comp (iotaPlus ℂ_[p] p)
  obtain ⟨k, a, hs⟩ := exists_mul_p_pow_eq_algebraMap y
  have hφa : phi ℂ_[p] p a = a := by
    apply algebraMap_aCris_injective
    calc
      A (phi ℂ_[p] p a) = f (A a) := (phiPlus_algebraMap (K := ℂ_[p]) (p := p) a).symm
      _ = f (y * (p : BCrisPlus ℂ_[p] p) ^ k) := congrArg f hs.symm
      _ = f y * (p : BCrisPlus ℂ_[p] p) ^ k := map_mul_natCast_pow f y p k
      _ = y * (p : BCrisPlus ℂ_[p] p) ^ k := congrArg (· * (p : BCrisPlus ℂ_[p] p) ^ k) hy
      _ = A a := hs
  obtain ⟨q0, hq0⟩ := theta_mem_range_of_phi_eq hφa
  let q : ℚ_[p] := q0 / (p : ℚ_[p]) ^ k
  let y' := y - P q
  have hy' : f y' = y' := (map_sub f y (P q)).trans
    (congrArg₂ (· - ·) hy (phiPlus_algebraMap_padic q))
  have hθq : θ (P q) = algebraMap ℚ_[p] ℂ_[p] q :=
    (congrArg θdR (iotaPlus_algebraMap_padic q)).trans (thetaBDeRhamPlusField_algebraMap p q)
  have hθy : θ y = algebraMap ℚ_[p] ℂ_[p] q := by
    apply eq_map_div_natCast_pow_of_mul_eq (algebraMap ℚ_[p] ℂ_[p]) (q := q0) (n := p) (k := k)
      (Nat.cast_ne_zero.2 hp.out.ne_zero)
    exact (map_mul_natCast_pow θ y p k).symm.trans <|
      (congrArg θ hs).trans <| (thetaField_iotaPlus_algebraMap (K := ℂ_[p]) (p := p) a).trans hq0
  have hθ : θ y' = 0 := (map_sub θ y (P q)).trans (sub_eq_zero.mpr (hθy.trans hθq.symm))
  have hall : ∀ n, θ (f^[n] y') = 0 := fun n =>
    (congrArg θ (Function.iterate_fixed hy' n)).trans hθ
  let t := periodTPlus hε
  have hmem : y' ∈ Ideal.span {t} := hy' ▸ phiPlus_mem_span_periodT hε hζ hall
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  have hyt : y' = t * v := hv.symm.trans (mul_comm v t)
  have h2 : (p : BCrisPlus ℂ_[p] p) ^ 1 * f v = v := by
    have hf : f y' = 1 * y' := hy'.trans (one_mul y').symm
    simpa only [pow_one, one_mul] using
      map_period_factor f (phiPlus_periodTPlus hε) (fun {_ _} h => periodTPlus_mul_left_cancel hε hζ h) hyt hf
  have hv0 : v = 0 := eq_zero_of_p_pow_mul_phiPlus_eq le_rfl h2
  exact ⟨q, sub_eq_zero.mp (hyt.trans ((congrArg (t * ·) hv0).trans (mul_zero t)))⟩

private theorem exists_period_factor {R : Type*} [CommRing R] (f : R →+* R) {u t y w : R}
    {n : ℕ} (hu : IsUnit u) (ht : f t = u * t) (htc : Function.Injective (fun x : R => t * x))
    (hy : f y = u ^ (n + 1) * y) (hw : w * t = f y) :
    ∃ v, y = t * v ∧ f v = u ^ n * v := by
  let d := Ring.inverse u ^ (n + 1)
  have hd : d * u ^ (n + 1) = 1 := by
    dsimp only [d]
    rw [← mul_pow, Ring.inverse_mul_cancel _ hu, one_pow]
  have hv : y = t * (d * w) := calc
    y = d * (u ^ (n + 1) * y) := by rw [← mul_assoc, hd, one_mul]
    _ = d * (w * t) := by rw [hw, hy]
    _ = t * (d * w) := (mul_rotate' t d w).symm
  refine ⟨d * w, hv, hu.mul_left_cancel ?_⟩
  rw [← mul_assoc, ← pow_succ']
  exact map_period_factor f ht htc hv hy

private theorem mem_span_pow_of_mul_mem_span_pow_succ {R : Type*} [CommRing R]
    {t x : R} {n : ℕ} (ht : Function.Injective (fun a : R => t * a))
    (h : t * x ∈ Ideal.span {t ^ (n + 1)}) : x ∈ Ideal.span {t ^ n} := by
  rw [Ideal.mem_span_singleton, pow_succ'] at h
  obtain ⟨a, ha⟩ := h
  exact Ideal.mem_span_singleton.2 ⟨a, ht (ha.trans (mul_assoc _ _ _))⟩


include hζ in

theorem exists_eq_algebraMap_mul_pow_of_phiPlus_eq (n : ℕ) : ∀ {y : BCrisPlus ℂ_[p] p},
    phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y →
    iotaPlus ℂ_[p] p y ∈ Ideal.span {fontaineT ε hε ^ n} →
    ∃ q : ℚ_[p], y = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * periodTPlus hε ^ n := by
  induction n with
  | zero =>
    intro y hy _
    obtain ⟨q, hq⟩ := exists_eq_algebraMap_of_phiPlus_eq hε hζ (by rw [hy, pow_zero, one_mul])
    exact ⟨q, by rw [hq, pow_zero, mul_one]⟩
  | succ n ih =>
    intro y hy hι
    let f := phiPlus ℂ_[p] p
    let ι := iotaPlus ℂ_[p] p
    let θ := (θdR).comp ι
    let t := periodTPlus hε
    have hθ0 : θ y = 0 := by
      have hT : fontaineT ε hε ^ (n + 1) ∈ RingHom.ker θdR := by
        rw [← IsPerfectoidField.maximalIdeal_bDeRhamPlus, maximalIdeal_eq_span_fontaineT hε hζ]
        exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ n.succ_pos
      exact RingHom.mem_ker.1 ((Ideal.span_singleton_le_iff_mem (RingHom.ker θdR)).2 hT hι)
    have hall : ∀ k, θ (f^[k] y) = 0 := fun k =>
      (congrArg θ (iterate_phiPlus_eq_pow_mul hy k)).trans <|
        (map_mul θ _ y).trans ((congrArg (θ _ * ·) hθ0).trans (mul_zero _))
    have hmem : f y ∈ Ideal.span {t} := phiPlus_mem_span_periodT hε hζ hall
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
    obtain ⟨y1, hyt, hy1⟩ := exists_period_factor f isUnit_p_bCrisPlus
      (phiPlus_periodTPlus hε) (fun {_ _} h => periodTPlus_mul_left_cancel hε hζ h) hy hw
    have hιy : ι y = fontaineT ε hε * ι y1 := (congrArg ι hyt).trans <|
      (map_mul ι t y1).trans (congrArg (· * ι y1) (iotaPlus_periodTPlus hε))
    have hι1 : ι y1 ∈ Ideal.span {fontaineT ε hε ^ n} :=
      mem_span_pow_of_mul_mem_span_pow_succ (fun {_ _} h => mul_left_cancel₀ (fontaineT_ne_zero hε hζ) h)
        (hιy ▸ hι)
    obtain ⟨q, hq⟩ := ih hy1 hι1
    exact ⟨q, by rw [hyt, hq, mul_left_comm, ← pow_succ' t n]⟩

end Plus

end ACris

end GroundTheory.PAdicHodge
