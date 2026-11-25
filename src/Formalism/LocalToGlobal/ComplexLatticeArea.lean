module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

/-! # The least positive area in a complex lattice -/

@[expose] public section

noncomputable section

namespace Formalism.ComplexLatticeArea

open Formalism.MainNotions.TaylorLogMetric

def Bf (w₁ w₂ : ℂ) : ℝ := (starRingEnd ℂ w₁ * w₂).im

theorem Bf_swap (w₁ w₂ : ℂ) : Bf w₂ w₁ = -Bf w₁ w₂ := by
  simp only [Bf, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

theorem Bf_sub_zsmul_left (u w w₂ : ℂ) (q : ℤ) : Bf (u - q • w) w₂ = Bf u w₂ - q * Bf w w₂ := by
  simp only [Bf, zsmul_eq_mul, map_sub, map_mul, map_intCast, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem Bf_sub_zsmul_right (w₁ u w : ℂ) (q : ℤ) : Bf w₁ (u - q • w) = Bf w₁ u - q * Bf w₁ w := by
  simp only [Bf, zsmul_eq_mul, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cramer (w₁ w₂ u : ℂ) :
    (Bf u w₂ : ℂ) * w₁ + (Bf w₁ u : ℂ) * w₂ = (Bf w₁ w₂ : ℂ) * u := by
  apply Complex.ext <;>
    simp only [Bf, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem Bf_comb (w₁ w₂ : ℂ) (s t s' t' : ℝ) :
    Bf ((s : ℂ) * w₁ + (t : ℂ) * w₂) ((s' : ℂ) * w₁ + (t' : ℂ) * w₂) = (s * t' - t * s') * Bf w₁ w₂ := by
  simp only [Bf, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cast_toNat (n : ℤ) (h : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

theorem area_spec (Λ : AddSubgroup ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hdisc : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = κ * n)
    (hne : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area Λ = κ * m ∧ ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = area Λ * n := by
  classical

  have abs_witness (u) (hu : u ∈ Λ) (v) (hv : v ∈ Λ) (hne : Bf u v ≠ 0) :
      ∃ n : ℕ, 0 < n ∧ |Bf u v| = κ * n ∧ ∃ x ∈ Λ, ∃ y ∈ Λ, Bf x y = κ * n := by
    obtain ⟨z, hz⟩ := hdisc u hu v hv
    have hz0 : z ≠ 0 := by rintro rfl; exact hne (by simpa using hz)
    have habs : |Bf u v| = κ * z.natAbs := by
      rw [hz, abs_mul, abs_of_pos hκ, Nat.cast_natAbs, Int.cast_abs]
    refine ⟨z.natAbs, Int.natAbs_pos.mpr hz0, habs, ?_⟩
    rcases abs_choice (Bf u v) with hp | hn
    · exact ⟨u, hu, v, hv, hp.symm.trans habs⟩
    · exact ⟨v, hv, u, hu, (Bf_swap u v).trans (hn.symm.trans habs)⟩

  have hQ : ∃ n : ℕ, 0 < n ∧ ∃ u ∈ Λ, ∃ v ∈ Λ, Bf u v = κ * n := by
    obtain ⟨u, hu, v, hv, h⟩ := hne
    obtain ⟨n, hn, _, pair⟩ := abs_witness u hu v hv h
    exact ⟨n, hn, pair⟩
  set m := Nat.find hQ with hm
  obtain ⟨hm0, w₁, h₁, w₂, h₂, hw⟩ := Nat.find_spec hQ
  have hmin : ∀ n : ℕ, 0 < n → ∀ u ∈ Λ, ∀ v ∈ Λ, Bf u v = κ * n → m ≤ n :=
    fun n hn u hu v hv h => Nat.find_min' hQ ⟨hn, u, hu, v, hv, h⟩

  have harea : area Λ = κ * m := by
    unfold area
    refine IsLeast.csInf_eq ⟨⟨by positivity, w₁, h₁, w₂, h₂, ?_⟩, ?_⟩
    · change κ * m = |Bf w₁ w₂|
      rw [hw, abs_of_nonneg (by positivity)]
    · rintro a ⟨ha, u, hu, v, hv, rfl⟩
      change 0 < |Bf u v| at ha
      obtain ⟨n, hn, habs, x, hx, y, hy, hxy⟩ := abs_witness u hu v hv (abs_pos.mp ha)
      change κ * m ≤ |Bf u v|
      rw [habs]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmin n hn x hx y hy hxy) hκ.le
  refine ⟨m, hm0, harea, ?_⟩
  set g := κ * m with hg
  have hg0 : 0 < g := by positivity

  have remainder (n : ℤ) :
      κ * (n : ℝ) - ((n / m : ℤ) : ℝ) * (κ * m) = κ * ((n % m : ℤ) : ℝ) := by
    rw [Int.emod_def]
    push_cast
    ring
  have quotient (n : ℤ)
      (hr : ∃ u ∈ Λ, ∃ v ∈ Λ, Bf u v = κ * ((n % m : ℤ) : ℝ)) :
      κ * (n : ℝ) = g * ((n / m : ℤ) : ℝ) := by
    obtain ⟨u, hu, v, hv, huv⟩ := hr
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm0
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra h
      have hlo := Int.emod_nonneg n hm'.ne'
      have hhi := Int.emod_lt_of_pos n hm'
      have := hmin (n % (m : ℤ)).toNat (by lia) u hu v hv (by rw [huv, cast_toNat _ hlo])
      lia
    have hquot : (m : ℝ) * ((n / m : ℤ) : ℝ) = (n : ℝ) := by
      exact_mod_cast (by simpa [hr0] using Int.mul_ediv_add_emod n (m : ℤ) :
        (m : ℤ) * (n / m) = n)
    rw [hg, mul_assoc, hquot]
  have hleft (u) (hu : u ∈ Λ) : ∃ q : ℤ, Bf u w₂ = g * q := by
    obtain ⟨n, hn⟩ := hdisc u hu w₂ h₂
    refine ⟨n / m, hn.trans (quotient n ⟨_, Λ.sub_mem hu (Λ.zsmul_mem h₁ (n / (m : ℤ))), w₂, h₂, ?_⟩)⟩
    rw [Bf_sub_zsmul_left, hn, hw, remainder]
  have hright (u) (hu : u ∈ Λ) : ∃ q : ℤ, Bf w₁ u = g * q := by
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ u hu
    refine ⟨n / m, hn.trans (quotient n ⟨w₁, h₁, _, Λ.sub_mem hu (Λ.zsmul_mem h₂ (n / (m : ℤ))), ?_⟩)⟩
    rw [Bf_sub_zsmul_right, hn, hw, remainder]

  have hdec : ∀ u ∈ Λ, ∃ s t : ℤ, u = ((s : ℝ) : ℂ) * w₁ + ((t : ℝ) : ℂ) * w₂ := by
    intro u hu
    obtain ⟨s, hs⟩ := hleft u hu
    obtain ⟨t, ht⟩ := hright u hu
    refine ⟨s, t, ?_⟩
    have hc := cramer w₁ w₂ u
    rw [hs, ht, hw] at hc
    have hg0' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
    apply mul_left_cancel₀ hg0'
    rw [← hc]; push_cast; ring
  intro u hu v hv
  obtain ⟨s, t, rfl⟩ := hdec u hu
  obtain ⟨s', t', rfl⟩ := hdec v hv
  refine ⟨s * t' - t * s', ?_⟩
  rw [Bf_comb, hw, harea]; push_cast; ring

end Formalism.ComplexLatticeArea

end
