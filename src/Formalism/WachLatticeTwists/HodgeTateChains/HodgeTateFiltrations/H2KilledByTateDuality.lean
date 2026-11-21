import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.TwistKill

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial



theorem freeAlg : StatFreeAlg := by
  intro ℓ _ w U i V _ _ g hkill x
  constructor
  · have h0 : aeval g ((X - 1) * Rpoly ℓ w U i) x = 0 := by rw [hkill]; rfl
    rw [map_mul, Module.End.mul_apply] at h0
    have h1 : g (aeval g (Rpoly ℓ w U i) x) - aeval g (Rpoly ℓ w U i) x = 0 := by simpa using h0
    exact sub_eq_zero.1 h1
  · obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
    refine ⟨aeval g R' x, ?_⟩
    rw [aeval_split g _ R' hR' x, add_sub_cancel_left]


theorem freePiece : StatFreePiece := by
  intro ℓ _ w m hm h2 hw U i A P H0A cup ⟨hS, ⟨hI1, hI2⟩, hT4, ⟨_, hT3⟩, htf, hHT⟩ hlog y
  have hkill : aeval P.gm ((X - 1) * Rpoly ℓ w U i) = 0 := by
    obtain ⟨q, hq⟩ := (htpoly ℓ w U i).1
    rw [hq, map_mul, hHT, zero_mul]
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ]ˣ, (Rpoly ℓ w U i).eval 1 = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  obtain ⟨a, x, hax⟩ := (hI1 ((ℓ : ℤ_[ℓ]) • P.lam y)).1 (by rw [map_smul]; exact hT4 _)
  obtain ⟨hfix, y', hy'⟩ := freeAlg ℓ w U i P.Wm P.gm hkill a
  generalize aeval P.gm (Rpoly ℓ w U i) a = a0 at hfix hy'
  have h1 : P.infm a0 = ((Rpoly ℓ w U i).eval 1) • P.infm a := by
    have h := (hI2 (a0 - ((Rpoly ℓ w U i).eval 1) • a) 0).2
      ⟨⟨y', hy'⟩, 0, by rw [map_zero, sub_zero]⟩
    rw [map_zero, add_zero, map_sub, map_smul] at h
    exact sub_eq_zero.1 h
  have hfix' : P.gm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a0) = ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a0 := by
    rw [map_smul, hfix]
  obtain ⟨z, hz⟩ := hlog _ hfix'
  have h3 : ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.infm a = P.infm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a0) := by
    rw [map_smul, h1, hc, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨x'', hx''⟩ := hT3 x
  have h4 : (ℓ : ℤ_[ℓ]) • P.infX x = 0 := by
    have h := (hI2 0 ((ℓ : ℤ_[ℓ]) • x)).2 ⟨⟨0, by rw [map_zero, sub_zero]⟩, x'', hx''⟩
    rw [map_zero, zero_add, map_smul] at h
    exact h
  refine ⟨z, 1, ?_⟩
  have h5 : ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i + m + 2)) • y
      = cup z + ((ℓ : ℤ_[ℓ]) ^ m) • (((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.io (P.infX x)) := by
    calc ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i + m + 2)) • y
        = ((ℓ : ℤ_[ℓ]) ^ m) • (((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.io ((ℓ : ℤ_[ℓ]) • P.lam y)) := by
          rw [map_smul, hS, smul_smul, smul_smul, smul_smul]
          congr 1
          ring
      _ = ((ℓ : ℤ_[ℓ]) ^ m) • (P.io (((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.infm a) + ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.io (P.infX x)) := by
          rw [hax, map_add, smul_add, map_smul]
      _ = _ := by rw [h3, smul_add, hz]
  rw [h5, add_sub_cancel_left, pow_one, smul_comm, smul_comm (ℓ : ℤ_[ℓ]), ← map_smul, h4, map_zero, smul_zero,
    smul_zero]


theorem halving : StatHalving := by
  intro α γ P hmono hone hext
  have main : ∀ n, ∀ i j, j - i = n → i < j →
      P i j (∑ x ∈ Finset.Ico i j, α x + (∑ x ∈ Finset.Ico i j, γ x) * Nat.clog 2 (j - i)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j hn hij
      by_cases h1 : j = i + 1
      · subst h1
        have e1 : i + 1 - i = 1 := by omega
        rw [e1, Nat.clog_one_right, Nat.mul_zero, Nat.add_zero, Nat.Ico_succ_singleton,
          Finset.sum_singleton]
        exact hone i
      · have hik : i < i + (j - i) / 2 := by omega
        have hkj : i + (j - i) / 2 < j := by omega
        have A1 := ih (i + (j - i) / 2 - i) (by omega) i (i + (j - i) / 2) rfl hik
        have A2 := ih (j - (i + (j - i) / 2)) (by omega) (i + (j - i) / 2) j rfl hkj
        have A3 := hext i (i + (j - i) / 2) j _ _ hik hkj A1 A2
        refine hmono _ _ _ _ ?_ A3
        have hc : Nat.clog 2 (j - i) = Nat.clog 2 ((j - i + 2 - 1) / 2) + 1 :=
          Nat.clog_of_two_le (by norm_num) (by omega)
        have c1 : Nat.clog 2 (i + (j - i) / 2 - i) ≤ Nat.clog 2 ((j - i + 2 - 1) / 2) :=
          Nat.clog_mono_right 2 (by omega)
        have c2 : Nat.clog 2 (j - (i + (j - i) / 2)) ≤ Nat.clog 2 ((j - i + 2 - 1) / 2) :=
          Nat.clog_mono_right 2 (by omega)
        have sα := Finset.sum_Ico_consecutive α hik.le hkj.le
        have sγ := Finset.sum_Ico_consecutive γ hik.le hkj.le
        rw [hc, ← sα, ← sγ]
        generalize Nat.clog 2 ((j - i + 2 - 1) / 2) = L at c1 c2
        generalize Nat.clog 2 (i + (j - i) / 2 - i) = L1 at c1
        generalize Nat.clog 2 (j - (i + (j - i) / 2)) = L2 at c2
        generalize ∑ x ∈ Finset.Ico i (i + (j - i) / 2), γ x = g1
        generalize ∑ x ∈ Finset.Ico (i + (j - i) / 2) j, γ x = g2
        nlinarith [Nat.mul_le_mul_left g1 c1, Nat.mul_le_mul_left g2 c2]
  intro i j hij
  exact main _ i j rfl hij


end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
