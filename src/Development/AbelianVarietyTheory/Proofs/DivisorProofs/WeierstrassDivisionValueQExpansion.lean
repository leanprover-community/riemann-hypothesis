import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowsSumEqDivisorSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonInteger
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
import BuildAid.ForwardExisting

section
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma summable_weierstrassP_terms (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 := by
  have h := (L.hasSum_weierstrassPExcept 0 z).summable
  refine (h.add (summable_of_ne_finset_zero (s := {0})
    (f := fun l : L.lattice => if (l : ℂ) = 0 then 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 else 0)
    ?_)).congr ?_
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro l
    by_cases hl : (l : ℂ) = 0 <;> simp [hl]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma latticeEquivProd_symm_coe (L : PeriodPair) (p : ℤ × ℤ) :
    (L.latticeEquivProd.symm p : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ := by
  simp [PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    PeriodPair.latticeBasis]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

lemma _root_.GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * τ + m) ^ 2)
      (EisensteinSeries.G2 τ + (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP z) := by
  set L := _root_.GlobalTheory.QFam.tauPair τ with hLdef
  have hω₁ : L.ω₁ = τ := rfl
  have hω₂ : L.ω₂ = 1 := rfl
  set f : ℤ × ℤ → ℂ := fun p => 1 / (z - (p.1 * τ + p.2)) ^ 2 - 1 / ((p.1 : ℂ) * τ + p.2) ^ 2
    with hfdef
  have hg : HasSum (fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2) (L.weierstrassP z) :=
    (summable_weierstrassP_terms L z).hasSum
  have hf : HasSum f (L.weierstrassP z) := by
    have := (L.latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hg
    convert this using 1
    funext p
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, latticeEquivProd_symm_coe, hω₁, hω₂,
      hfdef, mul_one]
  have hrow : HasSum (fun n : ℤ => ∑' m : ℤ, f (n, m)) (L.weierstrassP z) :=
    hf.prod_fiberwise fun n => (hf.summable.prod_factor n).hasSum
  have hG : HasSum (fun n : ℤ => EisensteinSeries.e2Summand n τ) (EisensteinSeries.G2 τ) := by
    rw [← _root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.tsum_e2Summand τ]
    exact (_root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand τ).hasSum
  have hsum := hG.add hrow
  have hF : HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z - (n * τ + m)) ^ 2)
      (EisensteinSeries.G2 τ + L.weierstrassP z) := by
    convert hsum using 1
    funext n
    have ha : Summable fun m : ℤ => 1 / ((n : ℂ) * τ + m) ^ 2 := by
      have := EisensteinSeries.linear_right_summable (τ : ℂ) n (k := 2) le_rfl
      convert this using 1
      funext m
      simp [zpow_ofNat]
    have hba : Summable fun m : ℤ => f (n, m) := hf.summable.prod_factor n
    have he : EisensteinSeries.e2Summand n τ = ∑' m : ℤ, 1 / ((n : ℂ) * τ + m) ^ 2 := by
      unfold EisensteinSeries.e2Summand
      congr 1
      funext m
      simp [EisensteinSeries.eisSummand]
    rw [he]
    have := (ha.hasSum.add hba.hasSum).tsum_eq
    simp only [hfdef, add_sub_cancel] at this
    exact this
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hF
  convert hneg using 1
  funext n
  simp only [Function.comp_apply, Equiv.neg_apply]
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext m
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring_nf

end GlobalTheory.WpFam
end
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.G2_add_weierstrassP_row_sum : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 2) (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP z) := by
  atlas_forward_decl GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpansionB

theorem val_div_ne_int (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by
  intro h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [div_eq_iff hN] at h
  have h' : (j.val : ℤ) = n * (N : ℤ) := by exact_mod_cast h
  apply hj
  have h2 := congrArg (Int.cast : ℤ → ZMod N) h'
  simpa using h2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  classical
  intro N _ x hx
  rw [hasQ_iff]
  intro τ
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 1 τ x _ le_rfl (GlobalTheory.T.G2_add_weierstrassP_row_sum τ (tors N τ x))
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hT' : HasSum (fun k : ℕ => cSum N 1 1 x k *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T := by
    simpa using hT
  set c : ℂ := (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) with hcdef
  have hval : wB N x τ = T + c := by
    rw [wB_eq, hS, div_eq_iff (pow_ne_zero 2 hc), hcdef]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have him : (((x 1).val : ℂ) / N).im = 0 := by
        have : (((x 1).val : ℂ) / N) = ((((x 1).val : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.ofReal_im]
      have hr := (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger _ him (val_div_ne_int N (x 1) h1)).1
      have hch : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((x 1).val : ℂ) / N)) = ch N (x 1) := by
        rw [ch, mul_div_assoc]
      rw [hch] at hr
      rw [if_pos h0, if_pos h0]
      have e2 : (1 + 1 : ℕ) = 2 := rfl
      rw [e2, hr]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
  rw [hval]
  have hs : HasSum (fun k : ℕ => if k = 0 then c else 0) c := hasSum_ite_eq 0 c
  convert hT'.add hs using 2 with k
  by_cases hk : k = 0
  · subst hk
    simp [cB, cSum, hcdef]
  · simp [cB, hk]

end GlobalTheory.WpFam.ExpansionB
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_division_value_q_expansion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  atlas_forward_decl GlobalTheory.WpFam.ExpansionB.main
end
