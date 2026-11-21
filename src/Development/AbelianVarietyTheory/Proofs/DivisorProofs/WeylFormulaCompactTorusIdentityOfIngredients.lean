import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
import Mathlib

section
section
open GlobalTheory.PsCo.PcEG

open Finset

namespace GlobalTheory.PsCo.PcEF.VandermondeCompactNoncompactSplit

variable {n : ℕ}

theorem lhs_eq (t : Fin n → ℂ) :
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) =
      ∏ x : Fin n × Fin n, if x.1 < x.2 then t x.1 - t x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext b
  simp

theorem wden_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t =
      ∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  rfl

theorem mode_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2)) =
      ∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false then t x.1 - t x.2 else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (fun x => by simp) (fun x : Fin n × Fin n => t x.1 - t x.2)).symm

theorem sign_eq (ε : Fin n → Bool) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then (-1 : ℂ) else 1) =
      (-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε := by
  rw [← Finset.prod_filter, Finset.prod_const]
  rfl

theorem swap_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then t x.2 - t x.1 else 1) =
      ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1 :=
  Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)

theorem mode_split (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false then t x.1 - t x.2 else 1) =
      (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
        ((∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then (-1 : ℂ) else 1) *
          ∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then t x.2 - t x.1 else 1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨a, b⟩ := x
  rcases lt_trichotomy a b with h | rfl | h
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h, lt_asymm h]
  · cases h1 : ε a <;> simp
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h, lt_asymm h]

theorem lhs_split (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if x.1 < x.2 then t x.1 - t x.2 else 1) =
      (∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1) *
        ((∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
          ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨a, b⟩ := x
  rcases lt_trichotomy a b with h | rfl | h
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h]
  · simp
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [lt_asymm h]

end GlobalTheory.PsCo.PcEF.VandermondeCompactNoncompactSplit

namespace GlobalTheory.PsCo.PcEF

open VandermondeCompactNoncompactSplit in

theorem vandermonde_splits_compactNoncompact : VdmSplit := by
  intro n ε t
  rw [lhs_eq, wden_eq, mode_eq, mode_split, sign_eq, swap_eq, lhs_split]
  have hs : ((-1 : ℂ) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε) * (-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε = 1 := by
    rw [← mul_pow]; norm_num
  generalize (-1 : ℂ) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε = s at hs ⊢
  linear_combination (-((∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1) *
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
    ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1)) * hs

end GlobalTheory.PsCo.PcEF

end
end

section
open GlobalTheory.PsCo.PcEG

namespace GlobalTheory.PsCo.PcEG

theorem numShift_holds : NumShift := by
  intro n ε m c t ht
  unfold ReciprocityTheory.ChartRestriction.TR.Weyl.numK
  have hfilt : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, ε (σ i) = ε i)) =
      Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε) := by
    ext w; simp [funext_iff]
  rw [hfilt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : ∀ i, ε (w i) = ε i := fun i => congrFun (Finset.mem_filter.1 hw).2 i
  rw [mul_assoc]
  congr 1
  have h1 : ∏ i, t (w i) ^ (m i - c (ε i)) =
      (∏ i, t (w i) ^ m i) * ∏ i, t (w i) ^ (-c (ε (w i))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hw', sub_eq_add_neg, zpow_add₀ (ht _)]
  rw [h1]
  congr 1
  · have := Equiv.prod_comp w (fun a => t a ^ m (w.symm a))
    simpa using this
  · exact Equiv.prod_comp w (fun a => t a ^ (-c (ε a)))

end GlobalTheory.PsCo.PcEG
end

section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.HCChar (dsChar)

namespace GlobalTheory.PsCo.PcEF

namespace WeylCompactTorusIdentity

theorem alg {W S C M s p x : ℂ} (hs : s * s = 1) (hp : p * p = 1) (hW : W ≠ 0) (hM : M ≠ 0) (hs0 : s ≠ 0)
    (hx : W * x = S * C) : s * x = p * S / (W * (s * M)) * (p * M * C) := by
  have hden : W * (s * M) ≠ 0 := mul_ne_zero hW (mul_ne_zero hs0 hM)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (M * s * s) * hx + (M * S * C) * hs - (M * S * C) * hp

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem prod_tor_pow_eq_wtVal_mul {n : ℕ} (lam : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) (θ : Fin n → ℝ) (w : Equiv.Perm (Fin n)) :
    ∏ a, tor θ a ^ m (w.symm a) =
      GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ * GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ := by
  show ∏ a, Complex.exp (↑(θ a) * Complex.I) ^ m (w.symm a) = _
  unfold GlobalTheory.HCChar.wtVal
  rw [← Complex.exp_add]
  rw [Finset.prod_congr rfl (fun a _ => (Complex.exp_int_mul (↑(θ a) * Complex.I) (m (w.symm a))).symm),
    ← Complex.exp_sum]
  congr 1
  push_cast
  rw [← add_mul, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h2 : ((m (w.symm a) : ℤ) : ℂ) = ((lam (w.symm a) : ℝ) : ℂ) + ((n : ℂ) - 1) / 2 := by
    have h3 := congrArg (fun r : ℝ => (r : ℂ)) (hm (w.symm a))
    push_cast at h3
    exact h3.symm
  simp only [h2, Function.comp_apply]
  ring

end WeylCompactTorusIdentity

open WeylCompactTorusIdentity in

theorem weylFormulaCompactTorusIdentity_of_ingredients : VdmSplit → PhysTor → NumShift → TorusId := by
  intro hV hP hN n ε lam Λ m hm hΛ θ hinj x hx
  have ht0 : ∀ a, tor θ a ≠ 0 := fun a => Complex.exp_ne_zero _
  obtain ⟨hPD, -⟩ := hP n ε θ
  have hVd := hV n ε (tor θ)
  have hWd : GlobalTheory.HCChar.weylDenom θ * GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ =
      ∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b) := GlobalTheory.HCChar.weylDenom_mul θ
  have hNum : (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
      ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, tor θ a ^ m (w.symm a)) =
      (∑ w ∈ GlobalTheory.HCChar.compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ) *
        GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [prod_tor_pow_eq_wtVal_mul lam m hm θ w]
    ring
  have hx' : ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x =
      ((∑ w ∈ GlobalTheory.HCChar.compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * GlobalTheory.HCChar.wtVal (lam ∘ w.symm) θ) *
        GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) := by
    rw [hx, ← hNum]
    exact (congrArg (fun μ => ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε μ (tor θ)) (funext hΛ)).trans
      (hN n ε m (fun b : Bool => if b then (0 : ℤ) else (pOf ε : ℤ)) (tor θ) ht0)
  have hV0 : (∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
    exact sub_ne_zero.mpr (fun h => (Finset.mem_Ioi.mp hb).ne (hinj h))
  rw [hVd] at hV0
  have hW0 := left_ne_zero_of_mul hV0
  have hPm0 := right_ne_zero_of_mul (right_ne_zero_of_mul hV0)
  have hh : GlobalTheory.HCChar.wtVal (fun _ => ((n : ℝ) - 1) / 2) θ ≠ 0 := Complex.exp_ne_zero _
  have key := alg (s := (-1) ^ sDeg ε) (p := (-1) ^ (pOf ε * qOf ε)) (neg_one_pow_mul_self _)
    (neg_one_pow_mul_self _) hW0 hPm0 (pow_ne_zero _ (by norm_num)) hx'
  rw [key, hPD, ← hVd, ← hWd]
  unfold GlobalTheory.HCChar.dsChar
  congr 1
  rw [← mul_assoc, mul_div_mul_right _ _ hh]
  try rfl

end GlobalTheory.PsCo.PcEF

end
end

namespace GlobalTheory.PsCo.PcEF
open GlobalTheory.PsCo.PcEG

theorem torusId_full : TorusId := weylFormulaCompactTorusIdentity_of_ingredients vandermonde_splits_compactNoncompact adjointDet_onCompactTorus numShift_holds

end GlobalTheory.PsCo.PcEF
end
