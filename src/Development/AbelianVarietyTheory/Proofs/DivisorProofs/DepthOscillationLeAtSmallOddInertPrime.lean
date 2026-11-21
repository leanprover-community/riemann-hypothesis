import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvaria
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadii
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowA
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNat
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthUpperBoundOddUnramifiedPrime

section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthRadii

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}

theorem ordGe_mono {g : MvPowerSeries (Fin M) C} {r s : ℝ} (h : OrdGe v ρ g r) (hs : s ≤ r) :
    OrdGe v ρ g s := by
  intro α
  refine le_trans (WithTop.coe_le_coe.mpr ?_) (h α)
  linarith

theorem ordGe_one : OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0 := by
  intro α
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

theorem ordGe_mul {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg : OrdGe v ρ g r)
    (hh : OrdGe v ρ h s) : OrdGe v ρ (g * h) (r + s) := by
  intro α
  rw [MvPowerSeries.coeff_mul]
  apply AddValuation.map_le_sum
  rintro ⟨β, γ⟩ hβγ
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hβγ
  rw [AddValuation.map_mul]
  have e : r + s - ∑ m, ρ m * ((α m : ℕ) : ℝ) =
      (r - ∑ m, ρ m * ((β m : ℕ) : ℝ)) + (s - ∑ m, ρ m * ((γ m : ℕ) : ℝ)) := by
    rw [← hβγ]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hg β) (hh γ)

theorem ordGe_pow {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg : OrdGe v ρ g r) (N : ℕ) :
    OrdGe v ρ (g ^ N) ((N : ℝ) * r) := by
  induction N with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact ordGe_one
  | succ N ih =>
    rw [pow_succ]
    have e : ((N + 1 : ℕ) : ℝ) * r = (N : ℝ) * r + r := by push_cast; ring
    rw [e]
    exact ordGe_mul ih hg

def Agree (D : ℕ) (g g' : MvPowerSeries (Fin M) C) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D → coeff α g = coeff α g'

theorem agree_mono {D D' : ℕ} {g g' : MvPowerSeries (Fin M) C} (h : Agree D g g') (hD : D' ≤ D) :
    Agree D' g g' := fun α hα => h α (lt_of_lt_of_le hα hD)

theorem agree_mul {D : ℕ} {g g' h h' : MvPowerSeries (Fin M) C} (hg0 : constantCoeff g = 0)
    (hg0' : constantCoeff g' = 0) (hh0 : constantCoeff h = 0) (hh0' : constantCoeff h' = 0)
    (hg : Agree D g g') (hh : Agree D h h') : Agree (D + 1) (g * h) (g' * h') := by
  intro α hα
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨β, γ⟩ hβγ
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hβγ
  dsimp only
  have hdeg : Finsupp.degree β + Finsupp.degree γ = Finsupp.degree α := by
    rw [← hβγ, map_add]
  by_cases hβ : β = 0
  · subst hβ
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, hg0', zero_mul]
  by_cases hγ : γ = 0
  · subst hγ
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0, hh0', mul_zero]

  have hβd : Finsupp.degree β ≠ 0 := fun h0 => hβ ((Finsupp.degree_eq_zero_iff β).mp h0)
  have hγd : Finsupp.degree γ ≠ 0 := fun h0 => hγ ((Finsupp.degree_eq_zero_iff γ).mp h0)
  rw [hg β (by omega), hh γ (by omega)]

theorem agree_pow_succ {D : ℕ} {g g' : MvPowerSeries (Fin M) C} (hg0 : constantCoeff g = 0)
    (hg0' : constantCoeff g' = 0) (hg : Agree D g g') (k : ℕ) :
    Agree D (g ^ (k + 1)) (g' ^ (k + 1)) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [pow_succ g (k + 1), pow_succ g' (k + 1)]
    refine agree_mono (agree_mul ?_ ?_ hg0 hg0' ih hg) (Nat.le_succ D)
    · rw [map_pow, hg0, zero_pow (Nat.succ_ne_zero k)]
    · rw [map_pow, hg0', zero_pow (Nat.succ_ne_zero k)]

theorem agree_pow {D : ℕ} {g g' : MvPowerSeries (Fin M) C} (hg0 : constantCoeff g = 0)
    (hg0' : constantCoeff g' = 0) (hg : Agree D g g') {N : ℕ} (hN : 2 ≤ N) :
    Agree (D + 1) (g ^ N) (g' ^ N) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  rw [pow_succ g (k + 1), pow_succ g' (k + 1)]
  exact agree_mul (by rw [map_pow, hg0, zero_pow (Nat.succ_ne_zero k)])
    (by rw [map_pow, hg0', zero_pow (Nat.succ_ne_zero k)]) hg0 hg0' (agree_pow_succ hg0 hg0' hg k) hg

end

end GlobalTheory.DepthRadii

namespace GlobalTheory.DepthRadii

theorem radius_neg_one {p : ℕ} (hp : 3 ≤ p) : radius p (-1) = 1 / ((p : ℝ) - 1) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have h1 : -(2 * (-1 : ℤ) + 1) = 1 := by norm_num
  rw [h1, zpow_one]
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [div_eq_div_iff h3 h2]
  ring

theorem radius_anti {p : ℕ} (hp : 3 ≤ p) {j k : ℤ} (h : j ≤ k) : radius p k ≤ radius p j := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have : (p : ℝ) ^ (-(2 * k + 1)) ≤ (p : ℝ) ^ (-(2 * j + 1)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  exact div_le_div_of_nonneg_right (by linarith) hden.le

theorem radius_le_top {p : ℕ} (hp : 3 ≤ p) {k : ℤ} (h : -1 ≤ k) : radius p k ≤ 1 / ((p : ℝ) - 1) := by
  rw [← radius_neg_one hp]
  exact radius_anti hp h

theorem radius_ge {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : 1 / ((p : ℝ) ^ 2 - 1) ≤ radius p k := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have : 0 < (p : ℝ) ^ (-(2 * k + 1)) := zpow_pos (by linarith) _
  exact div_le_div_of_nonneg_right (by linarith) hden.le

theorem radius_pos {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : 0 ≤ radius p k := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  exact le_trans (div_nonneg zero_le_one hden.le) (radius_ge hp k)

theorem radius_rec {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : (p : ℝ) ^ 2 * radius p k - 1 = radius p (k - 1) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have hden : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have e : (p : ℝ) ^ (-(2 * (k - 1) + 1)) = (p : ℝ) ^ 2 * (p : ℝ) ^ (-(2 * k + 1)) := by
    rw [show -(2 * (k - 1) + 1) = (2 : ℤ) + -(2 * k + 1) by ring, zpow_add₀ hp0, zpow_two, sq]
  rw [e, mul_div_assoc', div_sub_one hden]
  congr 1
  ring

theorem big_pow {p : ℝ} (hp : 3 ≤ p) (m : ℕ) :
    (p + 1) + ((m : ℝ) + 2) * (p ^ 2 - 1) ≤ p ^ (m + 3) := by
  have h0 : (0 : ℝ) ≤ p - 3 := by linarith
  have h1 : p + 1 ≤ p ^ 3 := by nlinarith [mul_nonneg (sq_nonneg p) h0, sq_nonneg p]
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    nlinarith [mul_nonneg (sq_nonneg p) h0, mul_nonneg (by linarith : (0 : ℝ) ≤ p)
      (by linarith : (0 : ℝ) ≤ p - 1)]
  | succ m ih =>
    have h3 : p ^ 3 ≤ p ^ (m + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [show m + 1 + 3 = (m + 3) + 1 by ring, pow_succ p (m + 3)]
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1) (by linarith : (0 : ℝ) ≤ p ^ (m + 3) - (p + 1))]

theorem term_bound {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ} (hp : 3 ≤ p)
    {d : ℕ} (dp : Fin d → ℤ) (c : Fin d → ℕ → Fin d → C) (hdp : ∀ a, -1 ≤ dp a)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b))
    (a : Fin d) (n : ℕ) (b : Fin d) (hn : 1 ≤ n) (hne : c a n b ≠ 0) :
    ((radius p (dp b) - (p : ℝ) ^ n * radius p (dp a) : ℝ) : WithTop ℝ) ≤ v (c a n b) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpm : 0 < (p : ℝ) - 1 := by linarith
  have hQ : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  rcases lt_or_ge (dp a) 0 with ha | ha
  ·
    have ha' : dp a = -1 := by have := hdp a; omega
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hc a n b)
    rw [ha', radius_neg_one hp]
    have hb := radius_le_top hp (hdp b)
    set w := 1 / ((p : ℝ) - 1) with hwdef
    have hw : ((p : ℝ) - 1) * w = 1 := mul_one_div_cancel hpm.ne'
    have hw0 : 0 < w := one_div_pos.mpr hpm
    have hbern : 1 + (n : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ n := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) - 1 by linarith) n
      simpa using this
    have hprod := mul_nonneg (sub_nonneg.mpr hbern) hw0.le
    have hnw : (n : ℝ) * (((p : ℝ) - 1) * w) = n := by rw [hw, mul_one]
    nlinarith [hprod, hnw, hb]
  · obtain ⟨hc1, hcn, hc2⟩ := hgood a ha
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hcn n b hn)
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
    · subst h1
      exact absurd (show c a 1 b = 0 by rw [hc1]; rfl) hne
    ·
      subst h2
      have hb : dp a - 1 ≤ dp b := hc2 b hne
      have := radius_anti hp hb
      rw [← radius_rec hp] at this
      push_cast
      linarith
    ·
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hb := radius_le_top hp (hdp b)
      have hge := radius_ge hp (dp a)
      have hbig := big_pow hp' m
      set u := 1 / ((p : ℝ) ^ 2 - 1) with hudef
      have hu : ((p : ℝ) ^ 2 - 1) * u = 1 := mul_one_div_cancel hQ.ne'
      have hu0 : 0 < u := one_div_pos.mpr hQ
      have hC : 1 / ((p : ℝ) - 1) = ((p : ℝ) + 1) * u := by
        rw [hudef, mul_one_div, div_eq_div_iff hpm.ne' hQ.ne']
        ring
      have hA := mul_le_mul_of_nonneg_right hbig hu0.le
      have hB := mul_le_mul_of_nonneg_left hge (pow_nonneg (by linarith : (0 : ℝ) ≤ p) (m + 3))
      have hu' : ((m : ℝ) + 2) * (((p : ℝ) ^ 2 - 1) * u) = (m : ℝ) + 2 := by rw [hu, mul_one]
      push_cast
      nlinarith [hA, hB, hb, hC, hu']

end GlobalTheory.DepthRadii

namespace GlobalTheory.DepthRadii

noncomputable section

variable {C : Type} [Field C] {d M : ℕ}

def Phi (p : ℕ) (c : Fin d → ℕ → Fin d → C) (z t : Fin d → MvPowerSeries (Fin M) C) :
    Fin d → MvPowerSeries (Fin M) C :=
  fun b => z b - lgSum p c t b + t b

theorem coeff_Phi {p : ℕ} {c : Fin d → ℕ → Fin d → C} (hc0 : ∀ a, c a 0 = Pi.single a 1)
    (z t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) (α : Fin M →₀ ℕ) :
    coeff α (Phi p c z t b) = coeff α (z b) - ∑ n ∈ Finset.range (Finsupp.degree α),
      ∑ a, c a (n + 1) b * coeff α (t a ^ (p ^ (n + 1))) := by
  have hl : coeff α (lgSum p c t b) = ∑ n ∈ Finset.range (Finsupp.degree α + 1),
      ∑ a, c a n b * coeff α (t a ^ (p ^ n)) := rfl
  have h0 : ∑ a, c a 0 b * coeff α (t a ^ (p ^ 0)) = coeff α (t b) := by
    simp only [hc0, pow_zero, pow_one, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Phi, map_add, map_sub, hl, Finset.sum_range_succ', h0]
  ring

def iterT (p : ℕ) (c : Fin d → ℕ → Fin d → C) (z : Fin d → MvPowerSeries (Fin M) C) :
    ℕ → Fin d → MvPowerSeries (Fin M) C :=
  fun k => Nat.rec (motive := fun _ => Fin d → MvPowerSeries (Fin M) C) 0
    (fun _ t => Phi p c z t) k

def limT (p : ℕ) (c : Fin d → ℕ → Fin d → C) (z : Fin d → MvPowerSeries (Fin M) C) :
    Fin d → MvPowerSeries (Fin M) C :=
  fun b α => coeff α (iterT p c z (Finsupp.degree α + 1) b)

section
variable {p : ℕ} {c : Fin d → ℕ → Fin d → C} {z : Fin d → MvPowerSeries (Fin M) C}
  (hp : 3 ≤ p) (hc0 : ∀ a, c a 0 = Pi.single a 1)
  (hz : ∀ b (α : Fin M →₀ ℕ), Finsupp.degree α ≠ 1 → coeff α (z b) = 0)
include hc0 hz

theorem const_Phi (t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) :
    constantCoeff (Phi p c z t b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Phi hc0]
  simp only [map_zero, Finset.range_zero, Finset.sum_empty, sub_zero]
  exact hz b 0 (by simp)

theorem const_iterT (k : ℕ) (b : Fin d) : constantCoeff (iterT p c z k b) = 0 := by
  cases k with
  | zero => show constantCoeff (0 : MvPowerSeries (Fin M) C) = 0; exact map_zero _
  | succ k => exact const_Phi hc0 hz _ b

include hp

theorem agree_Phi {D : ℕ} {s s' : Fin d → MvPowerSeries (Fin M) C}
    (hs : ∀ b, constantCoeff (s b) = 0) (hs' : ∀ b, constantCoeff (s' b) = 0)
    (h : ∀ b, Agree D (s b) (s' b)) (b : Fin d) :
    Agree (D + 1) (Phi p c z s b) (Phi p c z s' b) := by
  intro α hα
  rw [coeff_Phi hc0, coeff_Phi hc0]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro a _
  have hN : 2 ≤ p ^ (n + 1) := le_trans (by omega) (le_self_pow (by omega) (Nat.succ_ne_zero n))
  rw [agree_pow (hs a) (hs' a) (h a) hN α hα]

theorem agree_iterT (k : ℕ) (b : Fin d) :
    Agree k (iterT p c z k b) (iterT p c z (k + 1) b) := by
  induction k generalizing b with
  | zero => intro α hα; exact absurd hα (Nat.not_lt_zero _)
  | succ k ih =>
    exact agree_Phi hp hc0 hz (const_iterT hc0 hz k) (const_iterT hc0 hz (k + 1)) ih b

theorem agree_iterT_le (k m : ℕ) (hkm : k ≤ m) (b : Fin d) :
    Agree k (iterT p c z k b) (iterT p c z m b) := by
  induction m, hkm using Nat.le_induction with
  | base => intro α _; rfl
  | succ m hkm ih =>
    intro α hα
    rw [ih α hα]
    exact agree_iterT hp hc0 hz m b α (lt_of_lt_of_le hα hkm)

theorem agree_limT (K : ℕ) (b : Fin d) : Agree K (limT p c z b) (iterT p c z K b) := by
  intro α hα
  show coeff α (iterT p c z (Finsupp.degree α + 1) b) = coeff α (iterT p c z K b)
  exact agree_iterT_le hp hc0 hz _ _ (by omega) b α (Nat.lt_succ_self _)

theorem const_limT (b : Fin d) : constantCoeff (limT p c z b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show coeff 0 (iterT p c z (Finsupp.degree (0 : Fin M →₀ ℕ) + 1) b) = 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact const_iterT hc0 hz _ b

theorem lgSum_limT (b : Fin d) : lgSum p c (limT p c z) b = z b := by
  ext α

  have hT := agree_limT hp hc0 hz (Finsupp.degree α + 1)
  have hlim0 := const_limT hp hc0 hz
  have hT0 := const_iterT (p := p) hc0 hz (Finsupp.degree α + 1)
  have h1 : coeff α (lgSum p c (limT p c z) b) =
      coeff α (lgSum p c (iterT p c z (Finsupp.degree α + 1)) b) := by
    show ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (limT p c z a ^ (p ^ n)) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1),
        ∑ a, c a n b * coeff α (iterT p c z (Finsupp.degree α + 1) a ^ (p ^ n))
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro a _
    have hpn : p ^ n = (p ^ n - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [hpn, agree_pow_succ (hlim0 a) (hT0 a) (hT a) _ α (Nat.lt_succ_self _)]
  have h2 : coeff α (Phi p c z (iterT p c z (Finsupp.degree α + 1)) b) =
      coeff α (iterT p c z (Finsupp.degree α + 1) b) :=
    (agree_iterT hp hc0 hz (Finsupp.degree α + 1) b α (Nat.lt_succ_self _)).symm
  simp only [Phi, map_add, map_sub] at h2
  rw [h1]
  linear_combination -h2

end

end

end GlobalTheory.DepthRadii

namespace GlobalTheory.DepthRadii

variable {C : Type} [Field C] {d M : ℕ}

theorem ordGe_Phi {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {p : ℕ} (hp : 3 ≤ p)
    {c : Fin d → ℕ → Fin d → C} (hc0 : ∀ a, c a 0 = Pi.single a 1) (dp : Fin d → ℤ)
    (hdp : ∀ a, -1 ≤ dp a)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b))
    {z s : Fin d → MvPowerSeries (Fin M) C} (hzb : ∀ b, OrdGe v ρ (z b) (radius p (dp b)))
    (hs : ∀ b, OrdGe v ρ (s b) (radius p (dp b))) (b : Fin d) :
    OrdGe v ρ (Phi p c z s b) (radius p (dp b)) := by
  intro α
  rw [coeff_Phi hc0]
  apply AddValuation.map_le_sub v (hzb b α)
  apply AddValuation.map_le_sum
  intro n _
  apply AddValuation.map_le_sum
  intro a _
  by_cases hne : c a (n + 1) b = 0
  · rw [hne, zero_mul, AddValuation.map_zero]; exact le_top
  have h1 := term_bound v hp dp c hdp hc hgood a (n + 1) b (by omega) hne
  have h2 := ordGe_pow (hs a) (p ^ (n + 1)) α
  rw [AddValuation.map_mul]
  calc ((radius p (dp b) - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ)
      = ((radius p (dp b) - (p : ℝ) ^ (n + 1) * radius p (dp a) : ℝ) : WithTop ℝ) +
        ((((p ^ (n + 1) : ℕ) : ℝ) * radius p (dp a) - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add]; congr 1; push_cast; ring
    _ ≤ _ := add_le_add h1 h2

end GlobalTheory.DepthRadii

private theorem ordGe_iterT {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d M : ℕ}
    {ρ : Fin M → ℝ} {p : ℕ} (hp : 3 ≤ p) {c : Fin d → ℕ → Fin d → C}
    (hc0 : ∀ a, c a 0 = Pi.single a 1) (dp : Fin d → ℤ) (hdp : ∀ a, -1 ≤ dp a)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b))
    {z : Fin d → MvPowerSeries (Fin M) C} (hzb : ∀ b, OrdGe v ρ (z b) (radius p (dp b))) :
    ∀ (k : ℕ) (b : Fin d), OrdGe v ρ (GlobalTheory.DepthRadii.iterT p c z k b) (radius p (dp b)) := by
  intro k
  induction k with
  | zero =>
    intro b α
    show _ ≤ v (coeff α (0 : MvPowerSeries (Fin M) C))
    rw [map_zero, AddValuation.map_zero]
    exact le_top
  | succ k ih =>
    intro b
    exact GlobalTheory.DepthRadii.ordGe_Phi hp hc0 dp hdp hc hgood hzb ih b

private theorem ordGe_subst' {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d M : ℕ}
    {ρ : Fin M → ℝ} {t : Fin d → MvPowerSeries (Fin M) C}
    (ht0 : ∀ b, constantCoeff (t b) = 0) (ht : ∀ b, OrdGe v ρ (t b) 0)
    (f : MvPowerSeries (Fin d) C) (hf : MvIsInt v f) : OrdGe v ρ (subst t f) 0 := by

  have hprod : ∀ β : Fin d →₀ ℕ, OrdGe v ρ (β.prod fun s e => t s ^ e) 0 := by
    intro β
    have key : ∀ s : Finset (Fin d), OrdGe v ρ (∏ i ∈ s, t i ^ β i) 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.prod_empty]; exact GlobalTheory.DepthRadii.ordGe_one
      | insert i s hi ih =>
        rw [Finset.prod_insert hi]
        have h1 := GlobalTheory.DepthRadii.ordGe_mono (GlobalTheory.DepthRadii.ordGe_pow (ht i) (β i))
          (mul_zero ((β i : ℕ) : ℝ)).symm.le
        have := GlobalTheory.DepthRadii.ordGe_mul h1 ih
        rwa [add_zero] at this
    exact key β.support
  intro α
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ht0)]
  apply finsum_induction (fun x => ((0 - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ v x)
  · rw [AddValuation.map_zero]; exact le_top
  · intro x y hx hy
    exact le_trans (le_min hx hy) (AddValuation.map_add v x y)
  · intro β
    rw [smul_eq_mul, AddValuation.map_mul]
    have h1 : (0 : WithTop ℝ) ≤ v (coeff β f) := hf β
    calc ((0 - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ)
        = 0 + ((0 - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ) := (zero_add _).symm
      _ ≤ _ := add_le_add h1 (hprod β α)

theorem GlobalTheory.DepthRadii.exists_solution_ordGe_radius : LowBStatement := by
  intro C _ _ _ v p _ hp hvp d M dp c hdp hc0 hc hgood ρ hρ z hz hzb
  have hlim : ∀ b, OrdGe v ρ (GlobalTheory.DepthRadii.limT p c z b) (radius p (dp b)) := by
    intro b α
    exact ordGe_iterT hp hc0 dp hdp hc hgood hzb (Finsupp.degree α + 1) b α
  refine ⟨GlobalTheory.DepthRadii.limT p c z, GlobalTheory.DepthRadii.const_limT hp hc0 hz,
    GlobalTheory.DepthRadii.lgSum_limT hp hc0 hz, hlim, ?_⟩
  intro f hf
  exact ordGe_subst' (GlobalTheory.DepthRadii.const_limT hp hc0 hz)
    (fun b => GlobalTheory.DepthRadii.ordGe_mono (hlim b) (GlobalTheory.DepthRadii.radius_pos hp _)) f hf
end

section
section
namespace GlobalTheory

theorem digit_le_logb_succ (p d : ℕ) (hp : 1 < p) (hd : d < p) :
    (d : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((d : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdle : (d : ℝ) ≤ (p : ℝ) - 1 := by
    have h : ((d : ℝ) + 1) ≤ p := by exact_mod_cast hd
    linarith
  set t : ℝ := (d : ℝ) / ((p : ℝ) - 1) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) hpm.le
  have ht1 : t ≤ 1 := (div_le_one hpm).2 hdle
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2
    (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by simp only [Set.mem_Ioi]; linarith : (p : ℝ) ∈ Set.Ioi 0)
    (sub_nonneg.2 ht1) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc
  have heq : (1 - t) + t * p = (d : ℝ) + 1 := by
    rw [ht]; field_simp; ring
  rw [heq] at hconc
  have hmul : (d : ℝ) * Real.log p = ((p : ℝ) - 1) * (t * Real.log p) := by
    rw [ht]; field_simp
  rw [Real.logb, ← mul_div_assoc, le_div_iff₀ hlogp, hmul]
  exact mul_le_mul_of_nonneg_left hconc hpm.le

theorem digits_sum_le_logb (p n : ℕ) (hp : p.Prime) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' hp.one_lt hn, List.sum_cons, Nat.cast_add]
      have hdiv := Nat.div_add_mod n p
      have hdp : n % p < p := Nat.mod_lt n hp.pos
      have ihq := ih (n / p) (Nat.div_lt_self hn hp.one_lt)
      have hd := digit_le_logb_succ p (n % p) hp.one_lt hdp
      have hprod : (((n / p : ℕ) : ℝ) + 1) * (((n % p : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
        have h1 : (n / p + 1) * (n % p + 1) ≤ n + 1 := by
          have : (n / p) * (n % p + 1) ≤ (n / p) * p := Nat.mul_le_mul_left _ hdp
          nlinarith
        exact_mod_cast h1
      have hlog : Real.logb p (((n / p : ℕ) : ℝ) + 1) + Real.logb p (((n % p : ℕ) : ℝ) + 1)
          ≤ Real.logb p ((n : ℝ) + 1) := by
        rw [← Real.logb_mul (by positivity) (by positivity)]
        exact Real.logb_le_logb_of_le hp1 (by positivity) hprod
      nlinarith [mul_le_mul_of_nonneg_left hlog hpm]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digits_sum_le_mul_logb : ∀ (p n : ℕ), p.Prime → (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  atlas_forward_decl GlobalTheory.digits_sum_le_logb
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addValuation_natCast_eq_padicValNat' : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ n : ℕ, n ≠ 0 → v (n : C) = (((padicValNat p n : ℕ) : ℝ) : WithTop ℝ) := by
  first | exact @GlobalTheory.addValuation_natCast_eq_padicValNat | exact GlobalTheory.addValuation_natCast_eq_padicValNat | (intros; apply GlobalTheory.addValuation_natCast_eq_padicValNat <;> assumption)
end

section
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowCount

theorem v_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : ℤ) :
    0 ≤ v (z : C) := by
  have hn : ∀ n : ℕ, 0 ≤ v (n : C) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact le_trans (le_min ih (by simp)) (v.map_add _ _)
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast hn n
  · push_cast; rw [v.map_neg]; exact hn n

theorem low_count_first_bound : FactorialWeightedSumBound := by
  intro C _ _ v M ρ g hg P B hB
  apply AddValuation.map_le_sum
  intro α hα
  rw [v.map_mul, v.map_mul]
  have h1 := hB α hα
  have h2 := hg α
  have h3 := v_intCast_nonneg v (P.coeff α)
  have h4 : (((B + ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) + (((0 - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ)
      ≤ v ((∏ m, (α m).factorial : ℕ) : C) + v (coeff α g) := add_le_add h1 h2
  rw [← WithTop.coe_add] at h4
  have h5 : (B + ∑ m, ρ m * α m) + (0 - ∑ m, ρ m * α m) = B := by ring
  rw [h5] at h4
  calc ((B : ℝ) : WithTop ℝ) = 0 + ((B : ℝ) : WithTop ℝ) := by simp
    _ ≤ _ := by rw [add_assoc]; exact add_le_add h3 h4

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem logb_two_le (p : ℕ) (hp : 3 ≤ p) : Real.logb p 2 ≤ 7 / 8 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have h3 : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) hp'
  have h : 8 * Real.log 2 ≤ 7 * Real.log 3 := by
    have := Real.log_le_log (by norm_num) (show (2:ℝ) ^ 8 ≤ 3 ^ 7 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  rw [Real.logb, div_le_iff₀ hlp]
  linarith

theorem low_count_third_bound : RadiusExponentInequality := by
  intro p i cr K ex hp hex hcr hK hK2
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith
  have hex' : (1 : ℝ) ≤ ex := by exact_mod_cast hex
  set D : ℝ := (p : ℝ) ^ 2 - 1 with hD
  have hD8 : 8 ≤ D := by nlinarith
  set q : ℝ := (p : ℝ) ^ (-(2 * (K : ℤ) + 1)) with hq
  have hq0 : 0 ≤ q := zpow_nonneg (by linarith) _
  have hqe : (ex : ℝ) * q ≤ 1 := by
    have hpos : (0 : ℝ) < (p : ℝ) ^ (2 * K + 1) := by positivity
    have : q = 1 / (p : ℝ) ^ (2 * K + 1) := by
      rw [hq, zpow_neg, one_div, show (2 * (K : ℤ) + 1) = ((2 * K + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    rw [this, mul_one_div, div_le_one hpos]
    exact_mod_cast hK
  have hrK : radius p K = (1 + q) / D := rfl
  have hrm : radius p (-1) = (1 + p) / D := by
    rw [hD]; simp only [radius]; norm_num
  have hpm : 1 / ((p : ℝ) - 1) = (1 + p) / D := by
    rw [hD, div_eq_div_iff (by linarith) (by nlinarith)]; ring
  have hL : Real.logb p (ex + 1) ≤ Real.logb p ex + 7 / 8 := by
    have h2 : ((ex : ℝ) + 1) ≤ ex * 2 := by linarith
    have := Real.logb_le_logb_of_le hp1 (by linarith) h2
    rw [Real.logb_mul (by linarith) (by norm_num)] at this
    linarith [logb_two_le p hp]
  have hi : (cr : ℝ) ≤ i := by exact_mod_cast hcr
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hii : (i : ℝ) ≤ (i : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ i := by exact_mod_cast h
      nlinarith
  refine ⟨?_, ?_⟩
  · rw [hrK, hrm]
    have hdiv : (i : ℝ) * ex / ((p : ℝ) - 1) = i * ex * (1 / ((p : ℝ) - 1)) := by ring
    rw [hdiv, hpm]
    have key : ((i : ℝ) - cr) * ex * (ex * q) ≤ ((i : ℝ) - cr) * ex := by
      have := mul_le_mul_of_nonneg_left hqe (mul_nonneg (sub_nonneg.2 hi) (by positivity : (0:ℝ) ≤ ex))
      linarith
    have e : (i : ℝ) * ex * ((1 + p) / D) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) - i * ex * ((1 + q) / D)
        - ex * cr * ((1 + p) / D - (1 + q) / D)
        - ((((i : ℝ) - cr) * ex * p / D) - (i : ℝ) ^ 2 * (Real.logb p ex + 1))
        = (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) - ((i : ℝ) - cr) * (ex * q) / D := by
      field_simp; ring
    have h1 : ((i : ℝ) - cr) * (ex * q) / D ≤ i / 8 := by
      rw [div_le_iff₀ (by linarith)]
      have : ((i : ℝ) - cr) * (ex * q) ≤ (i : ℝ) - cr :=
        by nlinarith [mul_le_mul_of_nonneg_left hqe (sub_nonneg.2 hi)]
      nlinarith
    have h2 : (i : ℝ) ^ 2 / 8 ≤ (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) := by
      nlinarith [sq_nonneg (i : ℝ)]
    linarith
  · rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      have : 0 ≤ Real.logb p ex := Real.logb_nonneg hp1 hex'
      push_cast; linarith
    · rcases hK2 with h | h
      · omega
      · have h' : ((p : ℝ) ^ (2 * K - 1) : ℝ) ≤ ex := by exact_mod_cast h.le
        have := Real.logb_le_logb_of_le hp1 (by positivity) h'
        rw [Real.logb_pow, Real.logb_self_eq_one hp1] at this
        have hc : ((2 * K - 1 : ℕ) : ℝ) = 2 * (K : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hc] at this
        linarith

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem rows_eq {i ex : ℕ} (α : Fin i × Fin i →₀ ℕ) (hdeg : Finsupp.degree α = i * ex)
    (hrow : ∀ e : Fin i, ∑ c : Fin i, α (e, c) ≤ ex) : ∀ e : Fin i, ∑ c : Fin i, α (e, c) = ex := by
  have hs : ∑ e : Fin i, ∑ c : Fin i, α (e, c) = ∑ e : Fin i, ex := by
    rw [← Fintype.sum_prod_type' (fun e c => α (e, c))]
    rw [Finsupp.degree_eq_sum] at hdeg
    simp [hdeg, mul_comm]
  intro e
  exact (Finset.sum_eq_sum_iff_of_le (fun e _ => hrow e)).1 hs e (Finset.mem_univ e)

theorem count_lt (i cr : ℕ) (hcr : cr ≤ i) (a b : ℝ) :
    ∑ e : Fin i, (if e.val < cr then a else b) = cr * a + (i - cr) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < cr then a else b) i, Finset.sum_ite]
  have h1 : (Finset.range i).filter (· < cr) = Finset.range cr := by
    ext k; simp; omega
  have h2 : ((Finset.range i).filter (fun k => ¬ k < cr)).card = i - cr := by
    have : (Finset.range i).filter (fun k => ¬ k < cr) = Finset.Ico cr i := by
      ext k; simp; omega
    rw [this, Nat.card_Ico]
  rw [Finset.sum_const, Finset.sum_const, h1, h2, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
  push_cast [hcr]; ring

theorem low_count_second_bound : FactorialMultiindexBound := by
  intro C _ _ v p hp hp3 hv i cr K ex hcr α hdeg hrow
  have hR := rows_eq α hdeg hrow
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, ?_⟩
  · apply le_of_eq
    rw [Fintype.sum_prod_type]
    have : ∀ e : Fin i, ∑ c : Fin i, (if (e, c).1.val < cr then radius p (-1) else radius p K) * (α (e, c) : ℝ)
        = (if e.val < cr then radius p (-1) else radius p K) * ex := by
      intro e
      rw [← hR e, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => this e), ← Finset.sum_mul, count_lt i cr hcr]
    ring
  · have hN : (∏ x, (α x).factorial : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
    rw [GlobalTheory.T.addValuation_natCast_eq_padicValNat' C v p hp hv _ hN]
    rw [WithTop.coe_le_coe]
    rw [GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp]
    have hle : ∀ x : Fin i × Fin i, α x ≤ ex := by
      intro x
      rw [← hR x.1]
      exact Finset.single_le_sum (f := fun c => α (x.1, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ x.2)
    have hterm : ∀ x : Fin i × Fin i, (α x : ℝ) / ((p : ℝ) - 1) - Real.logb p ((ex : ℝ) + 1)
        ≤ (padicValNat p (α x).factorial : ℝ) := by
      intro x
      rw [GlobalTheory.LegendreBounds.legendre_real p hp]
      have hd := GlobalTheory.T.digits_sum_le_mul_logb p (α x) hp
      have hlog : Real.logb p ((α x : ℝ) + 1) ≤ Real.logb p ((ex : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by have := hle x; push_cast; exact_mod_cast (by omega : α x + 1 ≤ ex + 1))
      have h0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [sub_div]
      have : (((Nat.digits p (α x)).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((ex : ℝ) + 1) := by
        rw [div_le_iff₀ h0]; nlinarith
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hterm x)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at hsum
    have htot : (∑ x : Fin i × Fin i, (α x : ℝ)) = i * ex := by
      rw [Finsupp.degree_eq_sum] at hdeg; exact_mod_cast hdeg
    rw [htot] at hsum
    push_cast at hsum ⊢
    nlinarith [hsum]

theorem lowC_all : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality :=
  ⟨low_count_first_bound, low_count_second_bound, low_count_third_bound⟩

end GlobalTheory.LowCount
end

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_count_all_bounds : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality := by
  atlas_forward_decl GlobalTheory.LowCount.lowC_all
end

section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def intSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp [AddValuation.map_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by simp [AddValuation.map_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, AddValuation.map_neg] at *
    exact ha

theorem isIntV_iff (v : AddValuation C (WithTop ℝ)) (x : C) : IsIntV v x ↔ x ∈ intSubring v :=
  Iff.rfl

theorem int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  show 0 ≤ v a
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := fun h' => hb ((AddValuation.top_iff v).1 h')
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hb'
  rcases eq_or_ne (v a) ⊤ with ha | ha
  · rw [ha]; exact le_top
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ha
  rw [← hr, ← hs, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [← hs]
  exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def Reduces (v : AddValuation C (WithTop ℝ)) {i n : ℕ} (M : Matrix (Fin i) (Fin n) C) : Prop :=
  ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ n ∧ (∀ a b, IsIntV v (g a b)) ∧
    v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e, (g * M) a e = 0

theorem pivot_step (v : AddValuation C (WithTop ℝ)) {i' n : ℕ}
    (ih : ∀ M' : Matrix (Fin i') (Fin n) C, Reduces v M')
    (M : Matrix (Fin (i' + 1)) (Fin (n + 1)) C) (h0 : M 0 0 ≠ 0)
    (hmin : ∀ b, v (M 0 0) ≤ v (M b 0)) : Reduces v M := by
  have hq : ∀ c : Fin i', IsIntV v (M c.succ 0 / M 0 0) := fun c =>
    int_of_le v h0 (by rw [div_mul_cancel₀ _ h0]; exact hmin c.succ)
  obtain ⟨g', cr', hc1, hc2, hint, hdet, hz⟩ :=
    ih (Matrix.of fun c e' => M c.succ e'.succ - M c.succ 0 / M 0 0 * M 0 e'.succ)
  have hw : ∀ a'', IsIntV v (-∑ c, g' a'' c * (M c.succ 0 / M 0 0)) := fun a'' =>
    (isIntV_iff v _).2 (neg_mem (Subring.sum_mem _ fun c _ =>
      mul_mem ((isIntV_iff v _).1 (hint a'' c)) ((isIntV_iff v _).1 (hq c))))
  refine ⟨Matrix.of fun a b => Fin.cases (motive := fun _ => C)
      (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
      (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
        (fun b'' => g' a'' b'') b) a,
    cr' + 1, by omega, by omega, ?_, ?_, ?_⟩
  · intro a b
    cases a using Fin.cases <;> cases b using Fin.cases <;>
      simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · simp [IsIntV]
    · simp [IsIntV]
    · exact hw _
    · exact hint _ _
  · have hsub : (Matrix.of fun a b => Fin.cases (motive := fun _ => C)
        (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
        (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
          (fun b'' => g' a'' b'') b) a).submatrix Fin.succ Fin.succ = g' := by
      ext a b
      simp
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, Fin.succAbove_zero, hsub,
      mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
    exact hdet
  · intro a ha e
    obtain ⟨a'', rfl⟩ := Fin.exists_succ_eq.2 (show a ≠ 0 by rintro rfl; simp at ha)
    have ha' : cr' ≤ a''.val := by rw [Fin.val_succ] at ha; omega
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    cases e using Fin.cases with
    | zero =>
      rw [neg_mul, Finset.sum_mul, neg_add_eq_zero]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_assoc, div_mul_cancel₀ _ h0]
    | succ e' =>
      have h1 := hz a'' ha' e'
      simp only [Matrix.mul_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib] at h1
      have e1 : ∑ c, g' a'' c * (M c.succ 0 / M 0 0 * M 0 e'.succ) =
          (∑ c, g' a'' c * (M c.succ 0 / M 0 0)) * M 0 e'.succ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [e1] at h1
      linear_combination h1

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

theorem one_int (v : AddValuation C (WithTop ℝ)) {i : ℕ} (a b : Fin i) :
    IsIntV v ((1 : Matrix (Fin i) (Fin i) C) a b) := by
  show 0 ≤ v _
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem reduces_all (v : AddValuation C (WithTop ℝ)) :
    ∀ (n i : ℕ) (M : Matrix (Fin i) (Fin n) C), Reduces v M := by
  intro n
  induction n with
  | zero =>
    intro i M
    exact ⟨1, 0, Nat.zero_le _, le_rfl, one_int v, by simp, fun a _ e => e.elim0⟩
  | succ n ih =>
    intro i M
    cases i with
    | zero => exact ⟨1, 0, le_rfl, Nat.zero_le _, one_int v, by simp, fun a _ => a.elim0⟩
    | succ i' =>
      obtain ⟨b0, -, hb0⟩ :=
        Finset.univ.exists_min_image (fun b => v (M b 0)) Finset.univ_nonempty
      by_cases h0 : M b0 0 = 0
      · have hcol : ∀ b, M b 0 = 0 := fun b => by
          have hb := hb0 b (Finset.mem_univ _)
          rw [h0, AddValuation.map_zero, top_le_iff] at hb
          exact (AddValuation.top_iff v).1 hb
        obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := ih (i' + 1) (Matrix.of fun a e => M a e.succ)
        refine ⟨g, cr, h1, by omega, hint, hdet, fun a ha e => ?_⟩
        cases e using Fin.cases with
        | zero => simp [Matrix.mul_apply, hcol]
        | succ e' => simpa [Matrix.mul_apply] using hz a ha e'
      · obtain ⟨g1, cr, h1, h2, hint, hdet, hz⟩ := pivot_step v (ih i')
          (M.submatrix (Equiv.swap 0 b0) id) (by simpa using h0)
          (fun b => by simpa using hb0 _ (Finset.mem_univ _))
        refine ⟨g1.submatrix id (Equiv.swap 0 b0), cr, h1, h2, fun a b => hint _ _, ?_,
          fun a ha e => ?_⟩
        · rw [Matrix.det_permute', AddValuation.map_mul, hdet, add_zero]
          rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (i' + 1)) b0)) with
            h | h <;> simp [h]
        · have key : ∑ b, g1 a (Equiv.swap 0 b0 b) * M b e =
              ∑ b, g1 a b * M (Equiv.swap 0 b0 b) e := by
            rw [← Equiv.sum_comp (Equiv.swap 0 b0) (fun b => g1 a b * M (Equiv.swap 0 b0 b) e)]
            simp [Equiv.swap_apply_self]
          simpa [Matrix.mul_apply, key] using hz a ha e

end

end GlobalTheory.LowU

theorem GlobalTheory.LowU.adapted_basis : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (i d : ℕ) (u : Fin i → Fin d → C) (S : Finset (Fin d)), IsSatFrame v u →
    ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ S.card ∧ (∀ a b, IsIntV v (g a b)) ∧
      v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e ∈ S, ∑ a', g a a' * u a' e = 0 := by
  intro C _ _ v i d u S _
  obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := GlobalTheory.LowU.reduces_all v S.card i
    (Matrix.of fun a k => u a (S.equivFin.symm k))
  refine ⟨g, cr, h1, h2, hint, hdet, fun a ha e he => ?_⟩
  simpa [Matrix.mul_apply] using hz a ha (S.equivFin ⟨e, he⟩)
end

section
open MvPowerSeries ReciprocityTheory.PGsh

namespace GlobalTheory.LgSubst

theorem coeff_pow_eq_zero_of_degree_lt {M : ℕ} {C : Type} [CommRing C]
    (f : MvPowerSeries (Fin M) C) (hf : constantCoeff f = 0) (m : ℕ) (α : Fin M →₀ ℕ)
    (h : α.degree < m) : coeff α (f ^ m) = 0 := by
  apply coeff_of_lt_order
  have h1 : 1 ≤ f.order := one_le_order_iff_constCoeff_eq_zero.2 hf
  have h2 : (m : ℕ∞) ≤ (f ^ m).order :=
    le_trans (by simpa using nsmul_le_nsmul_right h1 m) (le_order_pow _)
  exact lt_of_lt_of_le (by exact_mod_cast h) h2

theorem coeff_subst_of_pow_support {M : ℕ} {C : Type} [Field C] (p : ℕ) (hp : 2 ≤ p)
    (L : PowerSeries C) (hL : ∀ m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m L = 0)
    (s : MvPowerSeries (Fin M) C) (hs : constantCoeff s = 0) (α : Fin M →₀ ℕ) :
    coeff α (PowerSeries.subst s L) =
      ∑ n ∈ Finset.range (α.degree + 1), PowerSeries.coeff (p ^ n) L * coeff α (s ^ (p ^ n)) := by
  classical
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp
  rw [PowerSeries.coeff_subst hsub]
  rw [finsum_eq_sum_of_support_subset (s := (Finset.range (α.degree + 1)).image (fun n => p ^ n))]
  · rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [smul_eq_mul]
  · intro m hm
    rw [Function.mem_support] at hm
    by_cases hpt : ∃ n, m = p ^ n
    · obtain ⟨n, rfl⟩ := hpt
      rw [Finset.coe_image, Set.mem_image]
      refine ⟨n, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hn
      apply hm
      have hlt : n < p ^ n := Nat.lt_pow_self (by omega)
      rw [coeff_pow_eq_zero_of_degree_lt s hs _ α (by omega), smul_zero]
    · push_neg at hpt
      exact absurd (by rw [hL m hpt, zero_smul]) hm

theorem subst_sum_lgCurve_eq_lgSum : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → ∀ (d M : ℕ) (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), (∀ a, G.IsPTypical p (γ a)) → ∀ (t : Fin d → MvPowerSeries (Fin M) C), (∀ a, constantCoeff (t a) = 0) → ∀ e : Fin d, subst t (∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) e)) = lgSum p (fun a n => G.lc p (γ a) n) t e := by
  intro C _ _ v p hp d M G γ hγ t ht e
  have hts : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have step : ∀ a, subst t (PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) e))
      = PowerSeries.subst (t a) (G.lgCurve (γ a) e) := by
    intro a
    rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X a).const hts]
    simp only [subst_X hts]
    rfl
  rw [← coe_substAlgHom hts, map_sum]
  simp only [coe_substAlgHom, step]
  ext α
  rw [map_sum]
  simp only [coeff_subst_of_pow_support p hp.two_le _ (fun m hm => hγ _ e m hm) _ (ht _) α]
  rw [Finset.sum_comm]
  rfl

end GlobalTheory.LgSubst
end

section
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthLow

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem radius_nonneg {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : 0 ≤ radius p k := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  refine div_nonneg ?_ (by nlinarith)
  have : (0 : ℝ) < (p : ℝ) ^ (-(2 * k + 1)) := zpow_pos (by linarith) _
  linarith

theorem radius_anti {p : ℕ} (hp : 3 ≤ p) {k l : ℤ} (h : k ≤ l) : radius p l ≤ radius p k := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  refine div_le_div_of_nonneg_right ?_ (by nlinarith)
  have : (p : ℝ) ^ (-(2 * l + 1)) ≤ (p : ℝ) ^ (-(2 * k + 1)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  linarith

theorem ordGe_mono {M : ℕ} {ρ : Fin M → ℝ} {g : MvPowerSeries (Fin M) C} {r r' : ℝ}
    (h : OrdGe v ρ g r) (hr : r' ≤ r) : OrdGe v ρ g r' := fun α =>
  le_trans (WithTop.coe_le_coe.2 (by linarith)) (h α)

theorem coeff_lin {M : ℕ} (x : Fin M → C) (α : Fin M →₀ ℕ) :
    coeff α (∑ m, x m • (X m : MvPowerSeries (Fin M) C)) =
      ∑ m, if α = Finsupp.single m 1 then x m else 0 := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, coeff_X]
  split_ifs <;> simp

theorem coeff_lin_eq_zero {M : ℕ} (x : Fin M → C) (α : Fin M →₀ ℕ) (h : Finsupp.degree α ≠ 1) :
    coeff α (∑ m, x m • (X m : MvPowerSeries (Fin M) C)) = 0 := by
  rw [coeff_lin]
  refine Finset.sum_eq_zero fun m _ => if_neg fun e => h ?_
  rw [e]; simp

theorem ordGe_lin {M : ℕ} (ρ : Fin M → ℝ) (x : Fin M → C) (r : ℝ) (hx : ∀ m, IsIntV v (x m))
    (h : ∀ m, x m ≠ 0 → r ≤ ρ m) :
    OrdGe v ρ (∑ m, x m • (X m : MvPowerSeries (Fin M) C)) r := by
  intro α
  rw [coeff_lin]
  refine v.map_le_sum fun m _ => ?_
  split_ifs with e
  · by_cases h0 : x m = 0
    · rw [h0, v.map_zero]; exact le_top
    · refine le_trans ?_ (hx m)
      have h1 : ∑ k, ρ k * (α k : ℝ) = ρ m := by
        rw [e, Finset.sum_eq_single m]
        · simp
        · intro k _ hk
          simp [Finsupp.single_eq_of_ne hk]
        · simp
      rw [h1, ← WithTop.coe_zero]
      exact WithTop.coe_le_coe.2 (by linarith [h m h0])
  · rw [v.map_zero]; exact le_top

theorem det_int {n : ℕ} (M : Matrix (Fin n) (Fin n) C) (hM : ∀ a b, IsIntV v (M a b)) :
    IsIntV v M.det := by
  let M' : Matrix (Fin n) (Fin n) (PTb.intRing v) := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hMM : (PTb.intRing v).subtype.mapMatrix M' = M := by
    ext a b; rfl
  have := RingHom.map_det (PTb.intRing v).subtype M'
  rw [hMM] at this
  rw [← this]
  exact (M'.det).2

theorem isSatFrame_of_mul {i d : ℕ} {x u : Fin i → Fin d → C} {T : Matrix (Fin d) (Fin d) C}
    (hx : ∀ a b, IsIntV v (x a b)) (hT : ∀ a b, IsIntV v (T a b))
    (hxT : ∀ a e, u a e = ∑ b, x a b * T b e) (hu : IsSatFrame v u) : IsSatFrame v x := by
  obtain ⟨-, r, hr⟩ := hu
  refine ⟨hx, ?_⟩
  have hm : (Matrix.of fun a b => u a (r b)) = (Matrix.of x) * (T.submatrix id r) := by
    ext a b
    simp [Matrix.mul_apply, hxT]
  rw [hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet] at hr
  by_contra hne
  have hlt : (0 : WithTop ℝ) < v (∑ S : {S : Finset (Fin d) // S.card = i},
      ((Matrix.of x).submatrix id (S.1.orderEmbOfFin S.2)).det *
        ((T.submatrix id r).submatrix (S.1.orderEmbOfFin S.2) id).det) := by
    refine v.map_lt_sum (by simp) fun S _ => ?_
    rw [v.map_mul]
    have h1 : (0 : WithTop ℝ) < v ((Matrix.of x).submatrix id (S.1.orderEmbOfFin S.2)).det :=
      lt_of_le_of_ne (det_int _ fun a b => hx _ _) fun e => hne ⟨S.1.orderEmbOfFin S.2, e.symm⟩
    have h2 : (0 : WithTop ℝ) ≤ v ((T.submatrix id r).submatrix (S.1.orderEmbOfFin S.2) id).det :=
      det_int _ fun a b => hT _ _
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_right h2)
  exact hlt.ne' hr

theorem lgSum_change {d M : ℕ} (p : ℕ) (l c : Fin d → ℕ → Fin d → C)
    (T : Matrix (Fin d) (Fin d) C) (h : ∀ a n e, l a n e = ∑ b, c a n b * T b e)
    (t : Fin d → MvPowerSeries (Fin M) C) (e : Fin d) :
    lgSum p l t e = ∑ b, T b e • lgSum p c t b := by
  ext α
  have hc : ∀ (c : Fin d → ℕ → Fin d → C) b, coeff α (lgSum p c t b) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (t a ^ (p ^ n)) :=
    fun _ _ => rfl
  rw [map_sum, hc]
  simp only [coeff_smul, hc, h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem exists_least_exponent {p c : ℕ} (hp : 3 ≤ p) :
    ∃ K : ℕ, c ≤ p ^ (2 * K + 1) ∧ (K = 0 ∨ p ^ (2 * K - 1) < c) := by
  classical
  have hex : ∃ K : ℕ, c ≤ p ^ (2 * K + 1) :=
    ⟨c, le_trans (Nat.lt_pow_self (by omega : 1 < p)).le
      (Nat.pow_le_pow_right (by omega) (by omega))⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · exact Or.inl h0
  · right
    have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show 2 * (Nat.find hex - 1) + 1 = 2 * Nat.find hex - 1 by omega] at h1
    exact not_le.1 h1

theorem sum_two_radii {i cr : ℕ} (h : cr ≤ i) (r s : ℝ) :
    ∑ a : Fin i, (if a.val < cr then r else s) = i * s + cr * (r - s) := by
  have h1 : ∀ a : Fin i, (if a.val < cr then r else s) = s + (if a.val < cr then r - s else 0) := by
    intro a; split_ifs <;> ring
  simp only [h1]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    Fin.card_filter_val_lt, min_eq_right h]
  simp

theorem coeff_in_tangent_basis [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime)
    (hvp : v (p : C) = 1) {d h : ℕ} {ty : Fin d → ZMod h} {G : LogFGL v d}
    {γ : Fin d → Fin d → PowerSeries C} (hB : IsBasis G p ty γ) (dp : Fin d → ℤ)
    (hlc : ∀ a, 0 ≤ dp a → G.lc p (γ a) 1 = 0 ∧
      G.lc p (γ a) 2 ∈ Submodule.span C
        (Set.range fun b : {b // dp a - 1 ≤ dp b} => tangent (γ b.1))) :
    ∃ c : Fin d → ℕ → Fin d → C,
      (∀ a n e, G.lc p (γ a) n e = ∑ b, c a n b * PTb.tmat γ b e) ∧
      (∀ a, c a 0 = Pi.single a 1) ∧
      (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
      (∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b)) := by
  classical
  have hv := pt5v' C v p hp hvp d h ty G γ hB
  obtain ⟨hγ, -, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have hbound : ∀ (w : Fin d → C) (r : WithTop ℝ), (∀ e, r ≤ v (w e)) →
      ∀ b, r ≤ v (Matrix.vecMul w (PTb.tmat γ)⁻¹ b) := by
    intro w r hw b
    simp only [Matrix.vecMul, dotProduct]
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_trans (hw e) (le_add_of_nonneg_right (PTb.isIntV_tmat_inv hγ hdet' e b))
  have hrow : ∀ a, Matrix.vecMul (tangent (γ a)) (PTb.tmat γ)⁻¹ = Pi.single a 1 := by
    intro a
    have e : tangent (γ a) = Matrix.vecMul (Pi.single a 1) (PTb.tmat γ) := by
      rw [Matrix.single_one_vecMul]; rfl
    rw [e, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (PTb.tmat_isUnit_det hdet'),
      Matrix.vecMul_one]
  refine ⟨fun a n => Matrix.vecMul (G.lc p (γ a) n) (PTb.tmat γ)⁻¹, fun a n e => ?_, fun a => ?_,
    fun a n => hbound _ _ ((hv a).1 n), fun a ha => ?_⟩
  · exact (congrFun (PTb.vecMul_inv_tmat hdet' (G.lc p (γ a) n)) e).symm
  · dsimp only
    rw [← PTb.tangent_eq_lc_zero G p (fun b => (hγ a b).1), hrow]
  · obtain ⟨h1, h2⟩ := hlc a ha
    refine ⟨?_, fun n b hn => hbound _ _ (fun e => (hv a).2 h1 n e hn) b, fun b hb => ?_⟩
    · dsimp only
      rw [h1, Matrix.zero_vecMul]
    · by_contra hn
      apply hb
      obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 h2
      dsimp only
      rw [← hy, Matrix.sum_vecMul, Finset.sum_apply]
      refine Finset.sum_eq_zero fun b' _ => ?_
      rw [Matrix.smul_vecMul, hrow, Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
      intro e
      exact hn (e ▸ b'.2)

theorem detDepth_lower : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → 3 ≤ p → ∀ (d h : ℕ), 0 < h → Even h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (j : ℕ), (∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ j) → ∀ (τ : ZMod h), Even τ.val → ∀ (i c : ℕ), 1 ≤ c → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ cr : ℕ, cr ≤ i ∧ (cr : ℝ) ≤ j * (3 / 2 + Real.logb p c / 2) ∧ ((((i : ℝ) - cr) * c * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p c + 1) : ℝ) : EReal) ≤ detDepth G u c := by
  intro C _ _ _ v p hp hvp hp3 d h hh hev ty G μ j hj τ hτ i c hc u hu huτ
  classical
  obtain ⟨K, hK1, hK2⟩ := exists_least_exponent (c := c) hp3
  obtain ⟨γ, dp, hB, hdp, -, hcard, hlc⟩ :=
    GlobalTheory.T.logFGL_depth_stages_lowA C v p hp hp3 hvp d h hh hev ty G μ j K hj
  obtain ⟨cc, hcT, hc0, hcv, hcdp⟩ := coeff_in_tangent_basis hp hvp hB dp hlc
  obtain ⟨⟨Ψ, hΨint, hΨ0, hΨΦ, hΦΨ⟩, hlg⟩ :=
    (GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases.2 C v p hp hvp d h hh ty G μ).2 γ hB
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have hΦ : PTGood v (basisMap G γ) := by
    rw [GlobalTheory.basisMap_eq_ptBasisMap]; exact ptBasisMap_good G hγ

  obtain ⟨x, hxint, hxT, hxτ⟩ : ∃ x : Fin i → Fin d → C, (∀ a b, IsIntV v (x a b)) ∧
      (∀ a e, u a e = ∑ b, x a b * PTb.tmat γ b e) ∧ ∀ a b, ty b ≠ τ → x a b = 0 := by
    refine ⟨fun a => Matrix.vecMul (u a) (PTb.tmat γ)⁻¹,
      fun a b => PTb.isIntV_vecMul_inv hγ hdet' (hu.1 a) b,
      fun a e => (congrFun (PTb.vecMul_inv_tmat hdet' (u a)) e).symm, fun a => ?_⟩
    refine PTb.vecMul_tmat_support ty hdet' (fun b e he => ?_) _ τ fun e he => ?_
    · rw [PTb.tangent_eq_lc_zero G p (fun e => (hγ b e).1)]
      exact (hγty b).2 0 e (by simpa using he)
    · rw [PTb.vecMul_inv_tmat hdet']
      exact huτ a e he
  have hxsat : IsSatFrame v x :=
    isSatFrame_of_mul hxint (fun a b => (hγ a b).2 1) hxT hu
  obtain ⟨g, cr, hcri, hcrS, hgint, hgdet, hgS⟩ :=
    GlobalTheory.LowU.adapted_basis C v i d x (Finset.univ.filter fun b => ty b = τ ∧ dp b < K) hxsat
  obtain ⟨hcount, hKb⟩ := GlobalTheory.T.low_count_all_bounds.2.2 p i cr K c hp3 hc hcri hK1 hK2
  refine ⟨cr, hcri, ?_, ?_⟩
  · have h1 : (cr : ℝ) ≤ ((K : ℝ) + 1) * j := by exact_mod_cast hcrS.trans (hcard τ hτ)
    rw [mul_comm]
    exact h1.trans (mul_le_mul_of_nonneg_right hKb (Nat.cast_nonneg j))

  set ρ : Fin i → ℝ := fun a => if a.val < cr then radius p (-1) else radius p K with hρ
  set x' : Fin i → Fin d → C := fun a b => ∑ a', g a a' * x a' b with hx'
  have hρK : ∀ a, radius p K ≤ ρ a := by
    intro a
    simp only [hρ]
    split_ifs
    · exact radius_anti hp3 (by omega)
    · exact le_rfl
  have hz : ∀ b, OrdGe v ρ (∑ a, x' a b • (X a : MvPowerSeries (Fin i) C)) (radius p (dp b)) := by
    intro b
    refine ordGe_lin ρ _ _ (fun a => ?_) fun a ha => ?_
    · exact (PTb.intRing v).sum_mem fun a' _ => (PTb.intRing v).mul_mem (hgint a a') (hxint a' b)
    · have hb : ty b = τ := by
        by_contra hb
        exact ha (Finset.sum_eq_zero fun a' _ => by rw [hxτ a' b hb, mul_zero])
      by_cases hK : dp b < K
      · have hacr : a.val < cr := by
          by_contra hacr
          exact ha (hgS a (not_lt.1 hacr) b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb, hK⟩))
        simp only [hρ, if_pos hacr]
        exact radius_anti hp3 (hdp b).1
      · exact (radius_anti hp3 (not_lt.1 hK)).trans (hρK a)
  obtain ⟨t, ht0, hteq, htord, -⟩ := GlobalTheory.DepthRadii.exists_solution_ordGe_radius C v p hp hp3 hvp d i dp cc (fun a => (hdp a).1)
    hc0 hcv hcdp ρ (fun a => (radius_nonneg hp3 _).trans (hρK a))
    (fun b => ∑ a, x' a b • (X a : MvPowerSeries (Fin i) C))
    (fun b α hα => coeff_lin_eq_zero _ α hα) hz
  have heq : ∀ e, subst t (subst (basisMap G γ) (G.lg e)) =
      ∑ a, (∑ a', g a a' • u a') e • (X a : MvPowerSeries (Fin i) C) := by
    intro e
    rw [hlg e, GlobalTheory.LgSubst.subst_sum_lgCurve_eq_lgSum C v p hp d i G γ (fun a => (hγty a).1) t ht0 e,
      lgSum_change p _ cc (PTb.tmat γ) hcT]
    simp only [hteq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [hx', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hxT, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ => by ring
  rw [← GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant C v i d c G u g hgdet,
    GlobalTheory.T.differentialOperatorDepth_integral_coordinates C v i d c G _ (basisMap G γ) Ψ
      (fun a => ⟨(hΦ a).2, (hΦ a).1, hΨint a, hΨ0 a⟩) (fun a => ⟨hΨΦ a, hΦΨ a⟩) t ht0 heq]
  refine le_iInf fun f => WithBot.coe_le_coe.2 ?_
  refine GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii C v i d c ρ t _ ht0
    (fun a => ordGe_mono (htord a) (radius_nonneg hp3 _)) (fun α hα => ?_) f.1 f.2
  have hk : ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤
      toE (v ((detPow C i c).coeff α * mfact α)) :=
    (GlobalTheory.T.dividedPowerContentValuation_detPow_bounds C v p hp hvp i c).2.trans (iInf₂_le α hα)
  refine le_trans (WithTop.coe_le_coe.2 ?_) (WithBot.coe_le_coe.1 hk)
  rw [hρ, sum_two_radii hcri]
  linarith

end GlobalTheory.DepthLow
end

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detDepth_lower_bound_saturated_even_type : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → 3 ≤ p → ∀ (d h : ℕ), 0 < h → Even h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (j : ℕ), (∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ j) → ∀ (τ : ZMod h), Even τ.val → ∀ (i c : ℕ), 1 ≤ c → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ cr : ℕ, cr ≤ i ∧ (cr : ℝ) ≤ j * (3 / 2 + Real.logb p c / 2) ∧ ((((i : ℝ) - cr) * c * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p c + 1) : ℝ) : EReal) ≤ detDepth G u c := by
  atlas_forward_decl GlobalTheory.DepthLow.detDepth_lower
end

section
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem inPsi_orbit_parity {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {h : ℕ}
    (hh : 0 < h) (lab : ZMod h → (E →+* ℂ)) (hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s))
    (h0 : InPsi H (lab 0)) : Even h ∧ ∀ s : ZMod h, InPsi H (lab s) ↔ Even s.val := by
  have hn : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Nat.cast_succ, hstep, ih, Nat.even_add_one]
  haveI : NeZero h := ⟨hh.ne'⟩
  refine ⟨(hn h).1 (by simpa [ZMod.natCast_self] using h0), fun s => ?_⟩
  have := hn s.val
  rwa [ZMod.natCast_zmod_val] at this

theorem facBetween_fine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → 1 ≤ k → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundFine p (Dw.p + Dw.q) Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hp2 hdisc hin f k hf hk
  letI := H.starRing
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hL : 0 ≤ Real.logb p k := Real.logb_nonneg hp1 (by exact_mod_cast hk)
  refine ⟨((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1),
    k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)), ?_, ?_⟩
  · intro T io e ho y
    refine ⟨le_nuFac fun Ch X => ?_, fun halg =>
      (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) halg hp2 hdisc f k hf).2 hin⟩
    obtain ⟨hfrob, hty⟩ := GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks E H Dw l Xo c (fun _ => rfl) p hdisc T io X
    obtain ⟨h, hh0, -, lab, horb, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := hty y Ch f.1
    have hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s) := by
      intro s
      rw [((hfrob _ _ (horb.2.1 s)).2 hin)]
      constructor
      · intro h1 h2
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H (lab s) ⟨h2, h1⟩
      · intro h1
        exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H (lab s)).resolve_left h1
    obtain ⟨hev, hpar⟩ := inPsi_orbit_parity hh0 lab hstep (by rw [horb.1]; exact hf)
    have hodd : ∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ Dw.q := by
      intro s hs
      have hn : ¬ InPsi H (lab s) := fun h1 => (Nat.not_even_iff_odd.2 hs) ((hpar s).1 h1)
      have h2 := hcard s
      rw [if_neg hn] at h2
      rw [← h2, Fintype.card_subtype]
    obtain ⟨hsat, hzero, hdep⟩ := hfr 0 f horb.1.symm
    obtain ⟨cr, -, hcr, hlow⟩ := GlobalTheory.T.detDepth_lower_bound_saturated_even_type X.C (vX_vp X) p hp (vX_vp_p X) hp3 d' h hh0 hev ty G' mu Dw.q hodd
      (0 : ZMod h) (by simp) (rk f) k hk (fun a => P.mulVec (frame Ch X f a)) hsat hzero
    rw [nuFacC, ← hdep] at *
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hlow
    have h3 : ((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p ≤ ((rk f : ℝ) - cr) * k * p := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h4 := div_le_div_of_nonneg_right h3 hpp.le
    linarith
  · have hab : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) - 1) := by
      rw [div_le_div_iff₀ hpp (by linarith)]
      nlinarith
    have hkey : boundFine p (Dw.p + Dw.q) Dw.q (rk f) k -
        (k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) -
          (((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1))) =
        (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      unfold boundFine
      push_cast
      ring
    have hpos : 0 ≤ (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      have hb : 0 ≤ 1 / ((p : ℝ) - 1) := by apply div_nonneg <;> linarith
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 + Real.logb p k / 2) (sub_nonneg.2 hab)
      positivity
    linarith

end GlobalTheory.RefSum
end

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_depth_bounded_odd_inert_prime_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → 1 ≤ k → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundFine p (Dw.p + Dw.q) Dw.q (rk f) k := by
  atlas_forward_decl GlobalTheory.RefSum.facBetween_fine
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum.OscInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

open Classical in

theorem two_mul_card_psi_le :
    2 * (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ Module.finrank ℚ E := by
  have hne : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
    intro h
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, Complex.mul_re, him] at h2
    have hd : (2:ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [sq_nonneg H.rt0.re]
  have hinj : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ InPsi H τ)).card := by
    refine Finset.card_le_card_of_injOn (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      unfold InPsi at hτ ⊢
      simp only [RingHom.coe_comp, Function.comp_apply, hτ]
      exact hne
    · intro τ _ σ _ h
      ext x
      have := congrArg (fun g : E →+* ℂ => starRingEnd ℂ (g x)) h
      simpa using this
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => InPsi H τ)
  rw [Finset.card_univ, NumberField.Embeddings.card] at htot
  omega

open Classical in

theorem card_big_fiber_le {Dw : Datum H} {F k m : ℕ} (hS : Shape Dw F k m) (τ : E →+* ℂ) :
    (Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ)).card ≤ m + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  calc _ ≤ (Finset.Ico (k - 2) Dw.p).card := by
        refine Finset.card_le_card_of_injOn (fun f => f.2.val) ?_ ?_
        · intro f hf
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq, Finset.mem_Ico] at hf ⊢
          obtain ⟨⟨hpsi, hk⟩, -⟩ := hf
          have hlt := f.2.isLt
          have hm : Dw.mult f.1 = Dw.p := if_pos hpsi
          have hk' : k ≤ f.2.val + 1 + 1 := hk
          omega
        · intro f hf g hg hfg
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hf hg
          obtain ⟨τ1, j1⟩ := f
          obtain ⟨τ2, j2⟩ := g
          obtain ⟨-, h1'⟩ := hf
          obtain ⟨-, h2'⟩ := hg
          simp only at h1' h2' hfg
          subst h1' h2'
          exact Sigma.ext rfl (heq_of_eq (Fin.ext hfg))
    _ ≤ m + 1 := by rw [Nat.card_Ico]; omega

theorem boundFine_le {p N q i c m M : ℕ} (hp : 2 ≤ p) (hq : q ≤ m) (hi : N ≤ m + i) (hiN : i ≤ N) (hc : 1 ≤ c)
    (hcM : c ≤ M) :
    boundFine p N q i c ≤ (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) + (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hi' : (N : ℝ) ≤ m + i := by exact_mod_cast hi
  have hiN' : (i : ℝ) ≤ N := by exact_mod_cast hiN
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcM' : (c : ℝ) ≤ M := by exact_mod_cast hcM
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.logb p c := Real.logb_nonneg (by linarith) hc'
  have hl : Real.logb p c ≤ Real.logb p M := Real.logb_le_logb_of_le (by linarith) (by linarith) hcM'
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hcm : (0 : ℝ) ≤ c * m := by positivity
  have t1 : (c : ℝ) * ((N : ℝ) - 2 * q - i) * p / ((p : ℝ) ^ 2 - 1) ≤ c * m / ((p : ℝ) - 1) := by
    calc _ ≤ (c : ℝ) * m * p / ((p : ℝ) ^ 2 - 1) := by
          gcongr
          linarith
      _ ≤ _ := by
          rw [div_le_div_iff₀ hp2 hp1]
          nlinarith [mul_nonneg hcm hp1.le]
  have t2 : (c : ℝ) * q * (3 + 1 / 2 * Real.logb p c) / ((p : ℝ) - 1) ≤
      c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by
    gcongr
  have t3 : (i : ℝ) ^ 2 * (Real.logb p c + 1) ≤ (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
    gcongr
  have e : (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) =
      c * m / ((p : ℝ) - 1) + c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by ring
  unfold boundFine
  linarith

open Classical in

theorem sum_bound_le {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} {p : ℕ}
    (hS : Shape Dw F k m) (hB : ExpBd Dw k cx Mb Sm M) (hp : 2 ≤ p) (hM : 1 ≤ M) :
    ∑ f, (if IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f))
      ≤ eSmall F (Dw.p + Dw.q) m Mb Sm M p := by
  have hfib := card_big_fiber_le hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  obtain ⟨hMb, hτ, hSm, hcM⟩ := hB
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hL : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) (by exact_mod_cast hM)
  have hF : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ F := by
    have := two_mul_card_psi_le (H := H)
    omega
  have hF' : ((Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card : ℝ) ≤ F := by exact_mod_cast hF
  set X : ℝ := m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1) with hX
  set Y : ℝ := ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hmaps : ∀ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f),
      f.1 ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ) := fun f hf =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩
  have hbig : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), ((cx f : ℝ) * X + Y) ≤
      F * (Mb * X + (m + 1) * Y) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ _τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), (Mb * X + (m + 1) * Y) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [Finset.filter_filter, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
          have a1 := hτ τ
          have a2 : ((Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ)).card : ℝ) ≤ m + 1 := by
            exact_mod_cast hfib τ
          rw [Nat.cast_sum] at a1
          refine add_le_add (mul_le_mul_of_nonneg_right ?_ hX0) (mul_le_mul_of_nonneg_right ?_ hY0)
          · convert a1
          · convert a2
      _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hF' (by positivity)
  have hsm : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) ≤
      Sm / ((p : ℝ) - 1) := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hSm hp1.le)
    unfold sumSmallSpread boundAll
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr ?_ fun f _ => by rw [Nat.cast_mul]
    ext f
    simp only [Finset.mem_filter, not_isBig_iff]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : Lt1 Dw => IsBig k f)]
  have e : eSmall F (Dw.p + Dw.q) m Mb Sm M p = F * (Mb * X + (m + 1) * Y) + Sm / ((p : ℝ) - 1) := by
    rw [hX, hY]
    unfold eSmall
    ring
  rw [e]
  refine add_le_add (le_trans (Finset.sum_le_sum fun f hf => ?_) hbig) (le_trans (le_of_eq ?_) hsm)
  · have hb : IsBig k f := (Finset.mem_filter.1 hf).2
    have hm : Dw.mult f.1 = Dw.p := if_pos hb.1
    have hr := rk_le f
    have hk := hb.2
    split_ifs with h
    · exact boundFine_le hp h2 (by omega) (by omega) h.2 (hcM f)
    · have h0 : cx f = 0 := by
        by_contra hne
        exact h ⟨hb, by omega⟩
      simp [boundAll, h0, hY0]
  · exact Finset.sum_congr rfl fun f hf => if_neg fun h => (Finset.mem_filter.1 hf).2 h.1

end GlobalTheory.RefSum.OscInert

namespace GlobalTheory.RefSum

theorem oscLe_eSmall_of_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → 1 ≤ M → OscLe Xo c p cx (eSmall F (Dw.p + Dw.q) m Mb Sm M p + 1) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp hp2 hpd hin hM la
  classical
  have key : ∀ f : Lt1 Dw, ∃ A B : ℝ, FacBetween Xo la f (cx f) A B ∧ B - A ≤
      (if IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f)) := by
    intro f
    split_ifs with h
    · exact GlobalTheory.T.factor_depth_bounded_odd_inert_prime_cmType E H Dw l Xo c p la hp2 hpd hin f (cx f) h.1.1 h.2
    · exact ⟨0, _, (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, (sub_zero _).le⟩
  choose A B hAB hle using key
  obtain ⟨-, n, hn⟩ := (GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 A B hAB
  have h1 := OscInert.sum_bound_le hS hB hp.out.two_le hM
  have h2 := (Finset.sum_le_sum fun f (_ : f ∈ Finset.univ) => hle f).trans (by convert h1)
  exact ⟨n, fun T io e ho y => ⟨(hn T io e ho y).1, fun ha => ((hn T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

end GlobalTheory.RefSum

end
end

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_le_at_small_odd_inertPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → 1 ≤ M → OscLe Xo c p cx (eSmall F (Dw.p + Dw.q) m Mb Sm M p + 1) := by
  atlas_forward_decl GlobalTheory.RefSum.oscLe_eSmall_of_inert
end
