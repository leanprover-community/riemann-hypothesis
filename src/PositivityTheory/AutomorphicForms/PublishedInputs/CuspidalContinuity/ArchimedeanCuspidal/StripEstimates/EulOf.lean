import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImPosScaledUpperHalfPlane
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootOfUnityCharacterPeriodic
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumConjugation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NeZeroOfRePos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWeightGamma0NeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentsTransferOneOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.B1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeGaussLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnTranslateFd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountEqCardZmod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountOfNotDvdJacobi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareEuler
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyFactorCoeffZeroValuationEqProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumFloorHalf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierIntegrationByParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierContinuationDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOneAddSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCuspZeroFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfIntegralEisensteinContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormZInvLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphyIntegralParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldedIdentityOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSetTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdUniformizerEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormEqPrimesEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HsumSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSymCoeffLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lf3
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorRankThreeUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulOfOfFaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCharacterInv

section
noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped MatrixGroups ModularForm Modular ComplexConjugate Real ArithmeticFunction.Moebius NumberTheorySymbols

namespace Ad3.S

namespace ScalarIntegralEstimates

lemma ee_add (x y : ℂ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

lemma ee_int (k : ℤ) : ee (k : ℂ) = 1 := by
  unfold ee; rw [show 2 * (π : ℂ) * I * (k : ℂ) = k * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma cpow_rmul (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) (y : ℂ) :
    ((r : ℂ) * x) ^ y = (r : ℂ) ^ y * x ^ y := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr' hx), Complex.log_ofReal_mul hr hx,
    Complex.cpow_def_of_ne_zero hr', Complex.cpow_def_of_ne_zero hx, ← Complex.exp_add,
    ← Complex.ofReal_log hr.le]
  ring_nf

lemma inv_cpow_half (X : ℂ) (hX : 0 < X.re) : X⁻¹ ^ (-(1 / 2 : ℂ)) = X ^ (1 / 2 : ℂ) := by
  rw [Complex.inv_cpow X _ (by rw [Ne, Complex.arg_eq_pi_iff]; intro h; linarith [h.1]),
    Complex.cpow_neg, inv_inv]

lemma sq_half (x : ℂ) (hx : x ≠ 0) : x ^ (1 / 2 : ℂ) * x ^ (1 / 2 : ℂ) = x := by
  rw [← Complex.cpow_add _ _ hx]; norm_num

lemma cpow_ne (x y : ℂ) (hx : x ≠ 0) : x ^ y ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hx]; exact Complex.exp_ne_zero _

end ScalarIntegralEstimates

namespace ScalarIntegralEstimates

lemma scal (z : ℂ) (c : ℤ) (d M ν : ℕ) (hz : 0 < z.im) (hd : 0 < d) (hM : 0 < M)
    (hcz : (c : ℂ) * z + d ≠ 0) (τ : ℂ) (hτ : τ = z / (d * ((c : ℂ) * z + d))) :
    (-2 * I * τ) ^ (-(1 / 2 : ℂ)) * ((2 * τ * ((M * d : ℕ) : ℂ)) ^ ν)⁻¹ * ((M * d : ℕ) : ℂ)⁻¹ =
      (d : ℂ) ^ (-(1 / 2 : ℂ)) * (-I * (d * (-1 / z) - c)) ^ (1 / 2 : ℂ) * (-I * (-1 / z)) ^ (-(1 / 2 : ℂ)) *
        ((d * (-1 / z) - c) / (-1 / z)) ^ ν * ((-2 * I * z) ^ (-(1 / 2 : ℂ)) * ((2 * z * M) ^ ν)⁻¹ * (M : ℂ)⁻¹) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hcz' : z * c + d ≠ 0 := by rw [mul_comm]; exact hcz
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hwim : 0 < (-1 / z).im := by
    have : (-1 / z).im = z.im / Complex.normSq z := by simp [Complex.div_im]; ring
    rw [this]; exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have hPre : 0 < (-I * (d * (-1 / z) - c)).re := by
    simp; positivity
  have hP0re : 0 < (-I * (-1 / z)).re := by
    simp; simpa using hwim
  set w := -1 / z with hw
  set P := -I * (d * w - c) with hP
  set P0 := -I * w with hP0
  have hPne : P ≠ 0 := fun h => by rw [h] at hPre; simp at hPre
  have hP0ne : P0 ≠ 0 := fun h => by rw [h] at hP0re; simp at hP0re
  have hwne : w ≠ 0 := by rw [hw]; exact div_ne_zero (by norm_num) hz0
  have hdwc : (d : ℂ) * w - c ≠ 0 := by intro h; apply hPne; rw [hP, h, mul_zero]
  have e1 : -2 * I * τ = (((d / 2 : ℝ) : ℂ) * P)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hτ, hP, hw]; push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have e2 : -2 * I * z = (((1 / 2 : ℝ) : ℂ) * P0)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hP0, hw]; push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have hX1 : 0 < (((d / 2 : ℝ) : ℂ) * P).re := by
    rw [Complex.re_ofReal_mul]; exact mul_pos (by positivity) hPre
  have hX2 : 0 < (((1 / 2 : ℝ) : ℂ) * P0).re := by
    rw [Complex.re_ofReal_mul]; exact mul_pos (by norm_num) hP0re
  rw [e1, e2, inv_cpow_half _ hX1, inv_cpow_half _ hX2, cpow_rmul _ (by positivity) _ hPne,
    cpow_rmul _ (by norm_num) _ hP0ne]
  rw [show ((d / 2 : ℝ) : ℂ) = ((d : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg (by positivity) (by norm_num), Complex.ofReal_natCast]
  have hτne : τ ≠ 0 := by rw [hτ]; exact div_ne_zero hz0 (mul_ne_zero hdC hcz)
  have hK : (2 * z * M : ℂ) = 2 * τ * ((M * d : ℕ) : ℂ) * ((d * w - c) / w) := by
    rw [hτ, hw]; push_cast; field_simp; ring
  rw [hK, mul_pow (2 * τ * ((M * d : ℕ) : ℂ)) ((d * w - c) / w) ν, Complex.cpow_neg, Complex.cpow_neg P0]
  have hs := sq_half (d : ℂ) hdC
  have hsne := cpow_ne (d : ℂ) (1 / 2) hdC
  have hqne := cpow_ne P0 (1 / 2) hP0ne
  have htne := cpow_ne ((1 / 2 : ℝ) : ℂ) (1 / 2) (by norm_num)
  have hKne : (2 * τ * ((M * d : ℕ) : ℂ)) ^ ν ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hτne) (by push_cast; exact mul_ne_zero hMC hdC))
  have hRne : ((d * w - c) / w) ^ ν ≠ 0 := pow_ne_zero _ (div_ne_zero hdwc hwne)
  generalize (d : ℂ) ^ (1 / 2 : ℂ) = s at *
  generalize P0 ^ (1 / 2 : ℂ) = q at *
  generalize (2 * τ * ((M * d : ℕ) : ℂ)) ^ ν = K at *
  generalize ((d * w - c) / w) ^ ν = R at *
  generalize ((1 / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = t at *
  generalize P ^ (1 / 2 : ℂ) = p at *
  push_cast
  field_simp
  linear_combination p * hs

end ScalarIntegralEstimates

open ScalarIntegralEstimates in
theorem third_estimate_of_first_two : T1 → T2 → T3 := by
  intro h1 h2 M d ν _ ψ c' γ z hd hν hc hdd
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdet : γ 0 0 * d - γ 0 1 * (4 * (M : ℤ) ^ 2 * c') = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    rw [← hc, ← hdd]; exact this
  have hdetC : (γ 0 0 : ℂ) * d - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    rw [hc]; exact_mod_cast hdet
  have hzC : (z : ℂ) ≠ 0 := z.ne_zero
  have hzim : 0 < (z : ℂ).im := z.im_pos
  have hcz : (γ 1 0 : ℂ) * z + d ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    rcases h' with h0 | h0
    · rw [h0] at h; simp at h; exact hd.ne' h
    · exact z.im_pos.ne' h0
  set τ : ℂ := (z : ℂ) / (d * ((γ 1 0 : ℂ) * z + d)) with hτ
  have hγz : ((γ • z : ℍ) : ℂ) = (γ 0 1 : ℂ) / d + τ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
    rw [hτ, hdd]; push_cast
    have hcz' : (z : ℂ) * (γ 1 0 : ℂ) + d ≠ 0 := by rw [mul_comm]; exact hcz
    field_simp
    linear_combination (z : ℂ) * hdetC
  have hτim : 0 < τ.im := by
    have := (γ • z).im_pos
    rw [show τ = ((γ • z : ℍ) : ℂ) - (γ 0 1 : ℂ) / d by rw [hγz]; ring]
    simpa using this
  set Q : ℤ → ℂ := fun n => ψ (n : ZMod M) * ee ((γ 0 1 : ℂ) * (n : ℂ) ^ 2 / d) with hQ
  have hQper : ∀ x, Q (x + ((M * d : ℕ) : ℤ)) = Q x := by
    intro x; simp only [hQ]; congr 1
    · push_cast; simp
    · rw [show (γ 0 1 : ℂ) * (((x + ((M * d : ℕ) : ℤ) : ℤ) : ℂ)) ^ 2 / d =
          (γ 0 1 : ℂ) * (x : ℂ) ^ 2 / d + ((γ 0 1 * (2 * x * M + M ^ 2 * d) : ℤ) : ℂ) by
          push_cast; field_simp; ring, ee_add, ee_int, mul_one]
  have hth : th (fun n => ψ (n : ZMod M)) ν (γ • z : ℍ) = th Q ν τ := by
    unfold th; rw [hγz]; congr 1; ext n; simp only [hQ]
    rw [show (n : ℂ) ^ 2 * ((γ 0 1 : ℂ) / d + τ) = (γ 0 1 : ℂ) * (n : ℂ) ^ 2 / d + (n : ℂ) ^ 2 * τ by ring,
      ee_add]
    ring
  rw [hth, h1 Q (M * d) ν τ (by positivity) hν hτim hQper,
    h1 (fun n => ψ (n : ZMod M)) M ν z hMpos hν hzim (by intro x; push_cast; simp)]
  have hin : ∀ n : ℤ, ∑ x ∈ Finset.range (M * d), Q x * ee (n * x / ((M * d : ℕ) : ℂ)) =
      ψ d * GS (γ 0 1) d * ee (c' * (n : ℂ) ^ 2 / d) *
        ∑ x ∈ Finset.range M, ψ (((x : ℕ) : ℤ) : ZMod M) * ee (n * x / M) := by
    intro n; simp only [Int.cast_natCast]
    rw [← h2 M d ψ (γ 0 0) (γ 0 1) c' n hd hdet]
    apply Finset.sum_congr rfl; intro x _; simp [hQ]
  have hcC : ((γ 1 0 : ℤ) : ℂ) = 4 * (M : ℂ) ^ 2 * c' := by rw [hc]; push_cast; ring
  have hcz2 : 4 * (M : ℂ) ^ 2 * c' * z + d ≠ 0 := by rw [← hcC]; exact hcz
  have hex : ∀ n : ℤ, ee (c' * (n : ℂ) ^ 2 / d) * ee (-((n : ℂ) ^ 2 / (4 * ((M * d : ℕ) : ℂ) ^ 2 * τ))) =
      ee (-((n : ℂ) ^ 2 / (4 * (M : ℂ) ^ 2 * z))) := by
    intro n; rw [← ee_add]; congr 1; rw [hτ, hcC]; push_cast; field_simp; ring
  have hsum : ∑' n : ℤ, (∑ x ∈ Finset.range (M * d), Q x * ee (n * x / ((M * d : ℕ) : ℂ))) * (n : ℂ) ^ ν *
      ee (-((n : ℂ) ^ 2 / (4 * ((M * d : ℕ) : ℂ) ^ 2 * τ))) = ψ d * GS (γ 0 1) d *
      ∑' n : ℤ, (∑ x ∈ Finset.range M, ψ (((x : ℕ) : ℤ) : ZMod M) * ee (n * x / M)) * (n : ℂ) ^ ν *
        ee (-((n : ℂ) ^ 2 / (4 * (M : ℂ) ^ 2 * z))) := by
    rw [← tsum_mul_left]; congr 1; ext n; rw [hin n, ← hex n]; ring
  rw [hsum, scal z (γ 1 0) d M ν hzim hd hMpos hcz τ hτ]; ring

end Ad3.S

end
end

section
noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped MatrixGroups ModularForm Modular ComplexConjugate Real ArithmeticFunction.Moebius NumberTheorySymbols

namespace Ad3.S

namespace PLB

lemma hd_add (b c d : ℂ) (hd : d = c - 1) {t : ℝ} (h : b + t ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => (b + t) ^ c) (c * (b + t) ^ d) t := by
  have h1 : HasDerivAt (fun w : ℂ => b + w) 1 (t : ℂ) := (hasDerivAt_id' (x := (t : ℂ))).const_add b
  have h3 := (h1.cpow_const (c := c) h).comp_ofReal
  rw [mul_one, ← hd] at h3
  exact h3

lemma hd_sub (b c d : ℂ) (hd : d = c - 1) {t : ℝ} (h : b - t ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => (b - t) ^ c) (-(c * (b - t) ^ d)) t := by
  have h1 : HasDerivAt (fun w : ℂ => b - w) (-1) (t : ℂ) := (hasDerivAt_id' (x := (t : ℂ))).const_sub b
  have h3 := (h1.cpow_const (c := c) h).comp_ofReal
  rw [mul_neg_one, ← hd] at h3
  exact h3

lemma mvt2 {h h' h'' : ℝ → ℂ} {K : ℝ}
    (d1 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt h (h' t) t)
    (d2 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt h' (h'' t) t)
    (h0 : h' 0 = 0) (hK : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖h'' t‖ ≤ K) : ‖h 1 - h 0‖ ≤ K := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 ⟨le_rfl, zero_le_one⟩)
  have b1 : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖h' t‖ ≤ K := by
    intro t ht
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := h') (f' := h'') (C := K)
      (fun x hx => (d2 x hx).hasDerivWithinAt) (fun x hx => hK x (Set.Ico_subset_Icc_self hx)) t ht
    rw [h0, sub_zero] at this
    nlinarith [ht.1, ht.2]
  exact norm_image_sub_le_of_norm_deriv_le_segment_01' (fun x hx => (d1 x hx).hasDerivWithinAt)
    (fun x hx => b1 x (Set.Ico_subset_Icc_self hx))

lemma norm_re (y : ℝ) (hy : 0 < y) (c : ℂ) : ‖(y : ℂ) ^ c‖ = y ^ c.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hy c

lemma second_difference_cpow_bound (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖(x : ℂ) ^ (-s) - 2 * ((x : ℂ) + 1) ^ (-s) + ((x : ℂ) + 2) ^ (-s)‖ ≤
      ‖s‖ * ‖s + 1‖ * (2 * x ^ (-s.re - 2)) := by
  have mm : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + 1 - t ∈ Complex.slitPlane := by
    intro t ht
    rw [show (x : ℂ) + 1 - t = ((x + 1 - t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.2 (by linarith [ht.2])
  have mp : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + 1 + t ∈ Complex.slitPlane := by
    intro t ht
    rw [show (x : ℂ) + 1 + t = ((x + 1 + t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.2 (by linarith [ht.1])
  have key := mvt2 (h := fun t : ℝ => ((x : ℂ) + 1 - t) ^ (-s) + ((x : ℂ) + 1 + t) ^ (-s))
    (h' := fun t : ℝ => -(-s * ((x : ℂ) + 1 - t) ^ (-s - 1)) + -s * ((x : ℂ) + 1 + t) ^ (-s - 1))
    (h'' := fun t : ℝ => -s * (-s - 1) * (((x : ℂ) + 1 - t) ^ (-s - 2) + ((x : ℂ) + 1 + t) ^ (-s - 2)))
    (K := ‖s‖ * ‖s + 1‖ * (2 * x ^ (-s.re - 2))) ?_ ?_ ?_ ?_
  · have e : ((x:ℂ) + 1 - ((1:ℝ):ℂ)) ^ (-s) + ((x:ℂ) + 1 + ((1:ℝ):ℂ)) ^ (-s) -
        (((x:ℂ) + 1 - ((0:ℝ):ℂ)) ^ (-s) + ((x:ℂ) + 1 + ((0:ℝ):ℂ)) ^ (-s)) =
        (x : ℂ) ^ (-s) - 2 * ((x : ℂ) + 1) ^ (-s) + ((x : ℂ) + 2) ^ (-s) := by
      rw [Complex.ofReal_one, Complex.ofReal_zero, add_sub_cancel_right, sub_zero, add_zero, add_assoc,
        one_add_one_eq_two]
      ring
    rw [← e]
    exact key
  · intro t ht
    refine ((hd_sub _ (-s) (-s - 1) (by ring) (mm t ht)).add (hd_add _ (-s) (-s - 1) (by ring) (mp t ht))).congr_deriv ?_
    ring
  · intro t ht
    refine (((hd_sub _ (-s - 1) (-s - 2) (by ring) (mm t ht)).const_mul (-s)).neg.add
      ((hd_add _ (-s - 1) (-s - 2) (by ring) (mp t ht)).const_mul (-s))).congr_deriv ?_
    ring
  · simp
  · intro t ht
    have e1 : ‖((x : ℂ) + 1 - t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2) := by
      rw [show (x : ℂ) + 1 - t = ((x + 1 - t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.2])]
      have : (-s - 2).re = -s.re - 2 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.2]) (by linarith)
    have e2 : ‖((x : ℂ) + 1 + t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2) := by
      rw [show (x : ℂ) + 1 + t = ((x + 1 + t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.1])]
      have : (-s - 2).re = -s.re - 2 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.1]) (by linarith)
    have e3 : ‖-s - 1‖ = ‖s + 1‖ := by rw [show -s - 1 = -(s + 1) by ring, norm_neg]
    rw [norm_mul, norm_mul, norm_neg, e3]
    gcongr
    calc _ ≤ ‖((x : ℂ) + 1 - t) ^ (-s - 2)‖ + ‖((x : ℂ) + 1 + t) ^ (-s - 2)‖ := norm_add_le _ _
      _ ≤ _ := by linarith

lemma trap_bound (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖(s - 1) / 2 * ((x : ℂ) ^ (-s) + ((x : ℂ) + 1) ^ (-s)) - ((x : ℂ) ^ (1 - s) - ((x : ℂ) + 1) ^ (1 - s))‖ ≤
      1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * x ^ (-s.re - 2)))) := by
  have mp : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + t ∈ Complex.slitPlane := by
    intro t ht
    rw [show (x : ℂ) + t = ((x + t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.2 (by linarith [ht.1])
  have key := mvt2 (h := fun t : ℝ => ((x : ℂ) + t) ^ (1 - s) - (x : ℂ) ^ (1 - s) +
      (t : ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + t) ^ (-s)))
    (h' := fun t : ℝ => 1 / 2 * ((s - 1) * (x : ℂ) ^ (-s) - (s - 1) * ((x : ℂ) + t) ^ (-s)) +
      (t : ℂ) / 2 * ((s - 1) * (-s * ((x : ℂ) + t) ^ (-s - 1))))
    (h'' := fun t : ℝ => (t : ℂ) / 2 * ((s - 1) * (-s * ((-s - 1) * ((x : ℂ) + t) ^ (-s - 2)))))
    (K := 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * x ^ (-s.re - 2))))) ?_ ?_ ?_ ?_
  · have e : ((x : ℂ) + ((1:ℝ):ℂ)) ^ (1 - s) - (x : ℂ) ^ (1 - s) +
        ((1:ℝ):ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + ((1:ℝ):ℂ)) ^ (-s)) -
        (((x : ℂ) + ((0:ℝ):ℂ)) ^ (1 - s) - (x : ℂ) ^ (1 - s) +
        ((0:ℝ):ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + ((0:ℝ):ℂ)) ^ (-s))) =
        (s - 1) / 2 * ((x : ℂ) ^ (-s) + ((x : ℂ) + 1) ^ (-s)) - ((x : ℂ) ^ (1 - s) - ((x : ℂ) + 1) ^ (1 - s)) := by
      rw [Complex.ofReal_one, Complex.ofReal_zero, add_zero]
      ring
    rw [← e]
    exact key
  · intro t ht
    refine (((hd_add _ (1 - s) (-s) (by ring) (mp t ht)).sub_const ((x : ℂ) ^ (1 - s))).add
      (((hasDerivAt_id' (x := t)).ofReal_comp.div_const 2).mul
        (((hd_add _ (-s) (-s - 1) (by ring) (mp t ht)).const_mul (s - 1)).const_add
          ((s - 1) * (x : ℂ) ^ (-s))))).congr_deriv ?_
    push_cast
    ring
  · intro t ht
    refine (((((hd_add _ (-s) (-s - 1) (by ring) (mp t ht)).const_mul (s - 1)).const_sub
      ((s - 1) * (x : ℂ) ^ (-s))).const_mul (1 / 2)).add
      (((hasDerivAt_id' (x := t)).ofReal_comp.div_const 2).mul
        (((hd_add _ (-s - 1) (-s - 2) (by ring) (mp t ht)).const_mul (-s)).const_mul (s - 1)))).congr_deriv ?_
    push_cast
    ring
  · simp
  · intro t ht
    have e1 : ‖((x : ℂ) + t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2) := by
      rw [show (x : ℂ) + t = ((x + t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.1])]
      have : (-s - 2).re = -s.re - 2 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.1]) (by linarith)
    have e3 : ‖-s - 1‖ = ‖s + 1‖ := by rw [show -s - 1 = -(s + 1) by ring, norm_neg]
    have e4 : ‖(t : ℂ) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht.1, Complex.norm_two]
      linarith [ht.2]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, e3]
    gcongr

def v (k : ℕ) (s : ℂ) : ℂ := ((k : ℂ) + 1) ^ (-s)
def W (k : ℕ) (s : ℂ) : ℂ := ((k : ℂ) + 1) ^ (1 - s)
def D (k : ℕ) (s : ℂ) : ℂ := v k s - 2 * v (k + 1) s + v (k + 2) s
def E (k : ℕ) (s : ℂ) : ℂ := (s - 1) / 2 * (v k s + v (k + 1) s) - (W k s - W (k + 1) s)

lemma cast1 (k : ℕ) : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
lemma cast2 (k : ℕ) : (((k + 1 : ℕ) : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) + 1 := by push_cast; ring
lemma cast3 (k : ℕ) : (((k + 2 : ℕ) : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) + 2 := by push_cast; ring

lemma D_bound (k : ℕ) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖D k s‖ ≤ ‖s‖ * ‖s + 1‖ * (2 * ((k : ℝ) + 1) ^ (-s.re - 2)) := by
  have := second_difference_cpow_bound ((k : ℝ) + 1) (by positivity) s hs
  unfold D v
  rw [cast1, cast2, cast3]
  exact this

lemma E_bound (k : ℕ) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖E k s‖ ≤ 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * ((k : ℝ) + 1) ^ (-s.re - 2)))) := by
  have := trap_bound ((k : ℝ) + 1) (by positivity) s hs
  unfold E v W
  rw [cast1, cast2]
  exact this

lemma nv (k : ℕ) (s : ℂ) : ‖v k s‖ = ((k : ℝ) + 1) ^ (-s.re) := by
  unfold v
  rw [cast1, norm_re _ (by positivity)]
  simp

lemma nW (k : ℕ) (s : ℂ) : ‖W k s‖ = ((k : ℝ) + 1) ^ (1 - s.re) := by
  unfold W
  rw [cast1, norm_re _ (by positivity)]
  simp

lemma sumr (p : ℝ) (hp : p < -1) : Summable fun k : ℕ => ((k : ℝ) + 1) ^ p :=
  ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 hp)).congr fun k => by simp

lemma poly2 (s : ℂ) : ‖s‖ * ‖s + 1‖ ≤ (1 + ‖s‖) ^ 3 := by
  have h2 : ‖s + 1‖ ≤ 1 + ‖s‖ := by have := norm_add_le s 1; rw [norm_one] at this; linarith
  have h0 : 0 ≤ ‖s‖ := norm_nonneg _
  nlinarith [mul_le_mul h2 h2 (norm_nonneg _) (by linarith), mul_le_mul_of_nonneg_left h2 h0]

lemma poly3 (s : ℂ) : ‖s - 1‖ * (‖s‖ * ‖s + 1‖) ≤ (1 + ‖s‖) ^ 3 := by
  have h1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by have := norm_sub_le s 1; rw [norm_one] at this; linarith
  have h2 : ‖s + 1‖ ≤ 1 + ‖s‖ := by have := norm_add_le s 1; rw [norm_one] at this; linarith
  have h0 : 0 ≤ ‖s‖ := norm_nonneg _
  calc ‖s - 1‖ * (‖s‖ * ‖s + 1‖) ≤ (1 + ‖s‖) * ((1 + ‖s‖) * (1 + ‖s‖)) := by
        apply mul_le_mul h1 _ (by positivity) (by positivity)
        exact mul_le_mul (by linarith) h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma tele (F : ℕ → ℂ) (hF : Tendsto F atTop (𝓝 0)) (hs : Summable fun n => F n - F (n + 1)) :
    ∑' n, (F n - F (n + 1)) = F 0 := by
  have h := hs.hasSum.tendsto_sum_nat
  simp only [Finset.sum_range_sub'] at h
  have h2 : Tendsto (fun n => F 0 - F n) atTop (𝓝 (F 0 - 0)) := hF.const_sub _
  rw [sub_zero] at h2
  exact tendsto_nhds_unique h h2

lemma abel (A w : ℕ → ℂ) (B : ℝ) (hA0 : A 0 = 0) (hA : ∀ n, ‖A n‖ ≤ B) (hw : Summable fun n => ‖w n‖) :
    ∑' n, (A (n + 1) - A n) * w n = ∑' n, A (n + 1) * (w n - w (n + 1)) := by
  have sm : ∀ (g u : ℕ → ℂ), (∀ n, ‖g n‖ ≤ B) → Summable (fun n => ‖u n‖) → Summable fun n => g n * u n := by
    intro g u hg hu
    refine Summable.of_norm_bounded (hu.mul_left B) (fun n => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hg n) (norm_nonneg _)
  have hw1 : Summable fun n => ‖w (n + 1)‖ := (summable_nat_add_iff 1).2 hw
  have s1 := sm (fun n => A (n + 1)) w (fun n => hA _) hw
  have s2 := sm A w hA hw
  have s3 := sm (fun n => A (n + 1)) (fun n => w (n + 1)) (fun n => hA _) hw1
  have e1 : ∑' n, A n * w n = ∑' n, A (n + 1) * w (n + 1) := by
    rw [s2.tsum_eq_zero_add, hA0, zero_mul, zero_add]
  calc ∑' n, (A (n + 1) - A n) * w n = ∑' n, (A (n + 1) * w n - A n * w n) := by congr 1; ext n; ring
    _ = ∑' n, A (n + 1) * w n - ∑' n, A n * w n := s1.tsum_sub s2
    _ = ∑' n, A (n + 1) * w n - ∑' n, A (n + 1) * w (n + 1) := by rw [e1]
    _ = ∑' n, (A (n + 1) * w n - A (n + 1) * w (n + 1)) := (s1.tsum_sub s3).symm
    _ = _ := by congr 1; ext n; ring

lemma diff_tsum (F : ℕ → ℂ → ℂ) (A : ℝ) (hA : 0 ≤ A) (hF : ∀ k, Differentiable ℂ (F k))
    (hb : ∀ k s, -1 < s.re → ‖F k s‖ ≤ A * (1 + ‖s‖) ^ 3 * ((k : ℝ) + 1) ^ (-s.re - 2)) :
    DifferentiableOn ℂ (fun s => ∑' k, F k s) (HP (-1)) := by
  intro s₀ hs₀
  have hs₀' : -1 < s₀.re := hs₀
  let U : Set ℂ := {s | (s₀.re - 1) / 2 < s.re} ∩ Metric.ball 0 (‖s₀‖ + 1)
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s₀ ∈ U := ⟨by show (s₀.re - 1) / 2 < s₀.re; linarith,
    by rw [Metric.mem_ball, dist_zero_right]; linarith⟩
  have hd : DifferentiableOn ℂ (fun s => ∑' k, F k s) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun k => A * (1 + (‖s₀‖ + 1)) ^ 3 * ((k : ℝ) + 1) ^ (-((s₀.re - 1) / 2) - 2))
      ((sumr _ (by linarith)).mul_left _) (fun k => (hF k).differentiableOn) hU ?_
    intro k s hs
    have h1 : (s₀.re - 1) / 2 < s.re := hs.1
    have h2 : ‖s‖ < ‖s₀‖ + 1 := by
      have := hs.2; rw [Metric.mem_ball, dist_zero_right] at this; exact this
    refine (hb k s (by linarith)).trans ?_
    have h3 : ((k : ℝ) + 1) ^ (-s.re - 2) ≤ ((k : ℝ) + 1) ^ (-((s₀.re - 1) / 2) - 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) (by linarith)
    have h4 : (1 + ‖s‖) ^ 3 ≤ (1 + (‖s₀‖ + 1)) ^ 3 := by gcongr
    gcongr
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

lemma sum_shift (q : ℕ) (f : ℕ → ℂ) (hper : ∀ n, f (n + q) = f n) (n : ℕ) :
    ∑ j ∈ Finset.range q, f (n + j + 1) = ∑ j ∈ Finset.range q, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ih]
    have h1 : ∑ j ∈ Finset.range (q + 1), f (n + j + 1) = ∑ j ∈ Finset.range q, f (n + j + 1) + f (n + q + 1) :=
      Finset.sum_range_succ _ _
    have h2 : ∑ j ∈ Finset.range (q + 1), f (n + j + 1) =
        ∑ j ∈ Finset.range q, f (n + (j + 1) + 1) + f (n + 0 + 1) := Finset.sum_range_succ' _ _
    have h3 : f (n + q + 1) = f (n + 0 + 1) := by
      rw [add_zero, show n + q + 1 = (n + 1) + q by ring, hper]
    have h4 : ∀ j, f (n + 1 + j + 1) = f (n + (j + 1) + 1) := fun j => by congr 1; ring
    simp only [h4]
    linear_combination h1 - h2 + h3

lemma prim (q : ℕ) (hq : 0 < q) (f : ℕ → ℂ) (B : ℝ) (hper : ∀ n, f (n + q) = f n) (hb : ∀ n, ‖f n‖ ≤ B) :
    ∃ (m : ℂ) (P : ℕ → ℂ), ‖m‖ ≤ B ∧ P 0 = 0 ∧ (∀ n, P (n + 1) = P n + (f (n + 1) - m)) ∧
      (∀ n, P (n + q) = P n) ∧ ∀ n, ‖P n‖ ≤ 2 * B * q := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hb 0)
  have hsum : ∀ r : ℕ, ‖∑ j ∈ Finset.range r, f (j + 1)‖ ≤ B * r := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ]; push_cast
      linarith [norm_add_le (∑ j ∈ Finset.range r, f (j + 1)) (f (r + 1)), hb (r + 1)]
  set m : ℂ := (∑ j ∈ Finset.range q, f (j + 1)) / q with hm
  have hmB : ‖m‖ ≤ B := by
    rw [hm, norm_div, Complex.norm_natCast, div_le_iff₀ (by exact_mod_cast hq)]
    exact hsum q
  set P : ℕ → ℂ := fun n => ∑ j ∈ Finset.range n, (f (j + 1) - m) with hPdef
  have hz : ∀ n, ∑ j ∈ Finset.range q, (f (n + j + 1) - m) = 0 := by
    intro n
    rw [Finset.sum_sub_distrib, sum_shift q f hper n, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (q : ℂ) * m = ∑ j ∈ Finset.range q, f (j + 1) := by rw [hm]; field_simp
    rw [this, sub_self]
  have hPq : ∀ n, P (n + q) = P n := by
    intro n
    simp only [hPdef, Finset.sum_range_add]
    rw [add_eq_left]
    simpa only [add_assoc] using hz n
  have hPk : ∀ r k, P (r + q * k) = P r := by
    intro r k
    induction k with
    | zero => simp
    | succ k ih => rw [show r + q * (k + 1) = (r + q * k) + q by ring, hPq, ih]
  have hPs : ∀ n, P (n + 1) = P n + (f (n + 1) - m) := fun n => Finset.sum_range_succ _ _
  have hPr : ∀ r : ℕ, ‖P r‖ ≤ 2 * B * r := by
    intro r
    induction r with
    | zero => simp [hPdef]
    | succ r ih =>
      rw [hPs]; push_cast
      have h1 := norm_add_le (P r) (f (r + 1) - m)
      have h2 := norm_sub_le (f (r + 1)) m
      have h3 := hb (r + 1)
      nlinarith
  refine ⟨m, P, hmB, by simp [hPdef], hPs, hPq, fun n => ?_⟩
  rw [← Nat.mod_add_div n q, hPk]
  have : n % q ≤ q := (Nat.mod_lt n hq).le
  exact (hPr _).trans (by gcongr)

lemma hv_sum (s : ℂ) (hs : 1 < s.re) : Summable fun k => ‖v k s‖ :=
  (sumr (-s.re) (by linarith)).congr (fun k => (nv k s).symm)

lemma zeta_id (s : ℂ) (hs : 1 < s.re) : 1 + (s - 1) / 2 + ∑' k, E k s = (s - 1) * ∑' k, v k s := by
  have hv := hv_sum s hs
  have hv' := hv.of_norm
  have hv1 : Summable fun k => v (k + 1) s := (summable_nat_add_iff 1).2 hv'
  have hE : Summable fun k => E k s := by
    refine Summable.of_norm_bounded
      ((sumr (-s.re - 2) (by linarith)).mul_left (1 / 2 * (‖s - 1‖ * (‖s‖ * ‖s + 1‖)))) (fun k => ?_)
    refine (E_bound k s (by linarith)).trans (le_of_eq ?_)
    ring
  have hvv : Summable fun k => (s - 1) / 2 * (v k s + v (k + 1) s) := (hv'.add hv1).mul_left _
  have hWs : Summable fun k => W k s - W (k + 1) s :=
    (hvv.sub hE).congr (fun k => by unfold E; ring)
  have hWt : Tendsto (fun k => W k s) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [nW]
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : (fun k : ℕ => ((k : ℝ) + 1) ^ (1 - s.re)) =
        (fun x : ℝ => x ^ (-(s.re - 1))) ∘ (fun k : ℕ => (k : ℝ) + 1) := by
      ext k; simp only [Function.comp_apply, neg_sub]
    rw [h2]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h1
  have e1 : ∑' k, (W k s - W (k + 1) s) = 1 := by
    rw [tele (fun k => W k s) hWt hWs]; simp [W]
  have e2 : ∑' k, v k s = 1 + ∑' k, v (k + 1) s := by
    rw [hv'.tsum_eq_zero_add]; simp [v]
  have e3 : ∑' k, E k s = (s - 1) / 2 * (∑' k, v k s + ∑' k, v (k + 1) s) - 1 := by
    simp only [E]
    rw [hvv.tsum_sub hWs, tsum_mul_left, hv'.tsum_add hv1, e1]
  rw [e3, e2]
  ring

lemma per_id (Φ : ℕ → ℂ) (m m₂ : ℂ) (S T : ℕ → ℂ) (B1 B2 : ℝ) (hS0 : S 0 = 0)
    (hS : ∀ n, S (n + 1) = S n + (Φ (n + 1) - m)) (hT0 : T 0 = 0)
    (hT : ∀ n, T (n + 1) = T n + (S (n + 1) - m₂))
    (hSb : ∀ n, ‖S n‖ ≤ B1) (hTb : ∀ n, ‖T n‖ ≤ B2) (s : ℂ) (hs : 1 < s.re) :
    ∑' k, (Φ (k + 1) - m) * v k s = m₂ + ∑' k, T (k + 1) * D k s := by
  have hv := hv_sum s hs
  have hv' := hv.of_norm
  have hv1 : Summable fun k => v (k + 1) s := (summable_nat_add_iff 1).2 hv'
  have hvn1 : Summable fun k => ‖v (k + 1) s‖ := hv1.norm
  have hdv : Summable fun k => ‖v k s - v (k + 1) s‖ :=
    Summable.of_nonneg_of_le (f := fun k => ‖v k s‖ + ‖v (k + 1) s‖) (fun _ => norm_nonneg _)
      (fun k => norm_sub_le (v k s) (v (k + 1) s)) (hv.add hvn1)
  have a1 := abel S (fun k => v k s) B1 hS0 hSb hv
  have a2 := abel T (fun k => v k s - v (k + 1) s) B2 hT0 hTb hdv
  have e1 : ∑' k, (Φ (k + 1) - m) * v k s = ∑' k, (S (k + 1) - S k) * v k s := by
    congr 1; ext k; rw [hS k]; ring
  have sA : Summable fun k => m₂ * (v k s - v (k + 1) s) := (hv'.sub hv1).mul_left _
  have sB : Summable fun k => (T (k + 1) - T k) * (v k s - v (k + 1) s) := by
    refine Summable.of_norm_bounded (hdv.mul_left (2 * B2)) (fun k => ?_)
    rw [norm_mul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    linarith [norm_sub_le (T (k + 1)) (T k), hTb (k + 1), hTb k]
  have e2 : ∑' k, S (k + 1) * (v k s - v (k + 1) s) =
      ∑' k, (m₂ * (v k s - v (k + 1) s) + (T (k + 1) - T k) * (v k s - v (k + 1) s)) := by
    congr 1; ext k; rw [hT k]; ring
  have e3 : ∑' k, (v k s - v (k + 1) s) = 1 := by
    rw [hv'.tsum_sub hv1, hv'.tsum_eq_zero_add]; simp [v]
  rw [e1, a1, e2, sA.tsum_add sB, tsum_mul_left, e3, a2, mul_one]
  congr 1; congr 1; ext k
  simp only [D, show k + 1 + 1 = k + 2 from rfl]
  ring

lemma lser_eq (Φ : ℕ → ℂ) (s : ℂ) (h : Summable fun k : ℕ => Φ (k + 1) * v k s) :
    LSeries Φ s = ∑' k, Φ (k + 1) * v k s := by
  have e : ∀ k : ℕ, LSeries.term Φ s (k + 1) = Φ (k + 1) * v k s := by
    intro k
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), v, Complex.cpow_neg, div_eq_mul_inv]
    push_cast; ring
  have h1 : Summable fun n => LSeries.term Φ s n := by
    rw [← summable_nat_add_iff 1]; simpa only [e] using h
  rw [LSeries, h1.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add, e]

lemma vdiff (k : ℕ) : Differentiable ℂ (fun s => v k s) := by
  unfold v
  exact differentiable_neg.const_cpow (Or.inl (Nat.cast_add_one_ne_zero k))

lemma Wdiff (k : ℕ) : Differentiable ℂ (fun s => W k s) := by
  unfold W
  exact (differentiable_id.const_sub 1).const_cpow (Or.inl (Nat.cast_add_one_ne_zero k))

lemma Ddiff (k : ℕ) : Differentiable ℂ (fun s => D k s) := by
  unfold D
  exact ((vdiff k).sub ((vdiff (k + 1)).const_mul 2)).add (vdiff (k + 2))

lemma Ediff (k : ℕ) : Differentiable ℂ (fun s => E k s) := by
  unfold E
  exact (((differentiable_id.sub_const 1).div_const 2).mul ((vdiff k).add (vdiff (k + 1)))).sub
    ((Wdiff k).sub (Wdiff (k + 1)))

end PLB

theorem lB_of : LB := by
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ))) K0 :=
    ⟨_, (PLB.sumr _ (by norm_num)).hasSum⟩
  have hK0n : 0 ≤ K0 := hK0.nonneg (fun k => by positivity)
  refine ⟨4 + 9 * K0, fun q Φ hq hper hb => ?_⟩
  obtain ⟨m, S, hm, hS0, hS, hSper, hSb⟩ := PLB.prim q hq Φ 1 hper hb
  obtain ⟨m₂, T, hm₂, hT0, hT, -, hTb⟩ := PLB.prim q hq S (2 * 1 * q) hSper hSb
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hTb' : ∀ n, ‖T n‖ ≤ 4 * (q : ℝ) ^ 2 := fun n => (hTb n).trans (le_of_eq (by ring))
  have d1 : DifferentiableOn ℂ (fun s => ∑' k, T (k + 1) * PLB.D k s) (HP (-1)) := by
    refine PLB.diff_tsum _ (8 * (q : ℝ) ^ 2) (by positivity) (fun k => (PLB.Ddiff k).const_mul _)
      (fun k s hs => ?_)
    rw [norm_mul]
    calc ‖T (k + 1)‖ * ‖PLB.D k s‖ ≤ (4 * (q : ℝ) ^ 2) * (‖s‖ * ‖s + 1‖ * (2 * ((k : ℝ) + 1) ^ (-s.re - 2))) :=
          mul_le_mul (hTb' _) (PLB.D_bound k s (by linarith)) (norm_nonneg _) (by positivity)
      _ ≤ (4 * (q : ℝ) ^ 2) * ((1 + ‖s‖) ^ 3 * (2 * ((k : ℝ) + 1) ^ (-s.re - 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (PLB.poly2 s) (by positivity)) (by positivity)
      _ = _ := by ring
  have d2 : DifferentiableOn ℂ (fun s => ∑' k, PLB.E k s) (HP (-1)) := by
    refine PLB.diff_tsum _ (1 / 2) (by norm_num) PLB.Ediff (fun k s hs => ?_)
    calc ‖PLB.E k s‖ ≤ 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * ((k : ℝ) + 1) ^ (-s.re - 2)))) :=
          PLB.E_bound k s (by linarith)
      _ = 1 / 2 * (‖s - 1‖ * (‖s‖ * ‖s + 1‖)) * ((k : ℝ) + 1) ^ (-s.re - 2) := by ring
      _ ≤ 1 / 2 * (1 + ‖s‖) ^ 3 * ((k : ℝ) + 1) ^ (-s.re - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (PLB.poly3 s) (by norm_num)) (by positivity)
  refine ⟨fun s => (s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s) + m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s),
    ?_, ?_, ?_⟩
  · exact ((differentiableOn_id.sub_const 1).mul (d1.const_add m₂)).add
      (((((differentiableOn_id.sub_const 1).div_const 2).const_add 1).add d2).const_mul m)
  · intro s hs
    have hv := PLB.hv_sum s hs
    have hΦv : Summable fun k => Φ (k + 1) * PLB.v k s := by
      refine Summable.of_norm_bounded hv (fun k => ?_)
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hb _)
    have hmv : Summable fun k => (Φ (k + 1) - m) * PLB.v k s := by
      refine Summable.of_norm_bounded (hv.mul_left 2) (fun k => ?_)
      rw [norm_mul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      linarith [norm_sub_le (Φ (k + 1)) m, hb (k + 1)]
    have e : ∑' k, Φ (k + 1) * PLB.v k s = m * ∑' k, PLB.v k s + ∑' k, (Φ (k + 1) - m) * PLB.v k s := by
      rw [← tsum_mul_left, ← (hv.of_norm.mul_left m).tsum_add hmv]
      congr 1; ext k; ring
    dsimp only
    rw [PLB.lser_eq Φ s hΦv, e, PLB.per_id Φ m m₂ S T _ _ hS0 hS hT0 hT hSb hTb s hs, PLB.zeta_id s hs]
    ring
  · intro s hs
    have hR : 1 ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
    have hexp : ∀ k : ℕ, ((k : ℝ) + 1) ^ (-s.re - 2) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := fun k =>
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) (by linarith)
    have hX : ‖∑' k, T (k + 1) * PLB.D k s‖ ≤ 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0 := by
      refine tsum_of_norm_bounded (hK0.mul_left (8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3)) (fun k => ?_)
      rw [norm_mul]
      calc ‖T (k + 1)‖ * ‖PLB.D k s‖ ≤ (4 * (q : ℝ) ^ 2) * (‖s‖ * ‖s + 1‖ * (2 * ((k : ℝ) + 1) ^ (-s.re - 2))) :=
            mul_le_mul (hTb' _) (PLB.D_bound k s (by linarith)) (norm_nonneg _) (by positivity)
        _ ≤ (4 * (q : ℝ) ^ 2) * ((1 + ‖s‖) ^ 3 * (2 * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul (PLB.poly2 s) (by linarith [hexp k]) (by positivity) (by positivity)
        _ = _ := by ring
    have hY : ‖∑' k, PLB.E k s‖ ≤ 1 / 2 * (1 + ‖s‖) ^ 3 * K0 := by
      refine tsum_of_norm_bounded (hK0.mul_left (1 / 2 * (1 + ‖s‖) ^ 3)) (fun k => ?_)
      calc ‖PLB.E k s‖ ≤ 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * ((k : ℝ) + 1) ^ (-s.re - 2)))) :=
            PLB.E_bound k s (by linarith)
        _ = 1 / 2 * (‖s - 1‖ * (‖s‖ * ‖s + 1‖)) * ((k : ℝ) + 1) ^ (-s.re - 2) := by ring
        _ ≤ 1 / 2 * (1 + ‖s‖) ^ 3 * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
            apply mul_le_mul _ (hexp k) (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left (PLB.poly3 s) (by norm_num)
    have h1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by have := norm_sub_le s 1; rw [norm_one] at this; linarith
    have h2 : ‖m₂ + ∑' k, T (k + 1) * PLB.D k s‖ ≤ 2 * q + 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0 := by
      refine (norm_add_le _ _).trans ?_
      linarith [hm₂]
    have h3 : ‖1 + (s - 1) / 2 + ∑' k, PLB.E k s‖ ≤ 1 + (1 + ‖s‖) / 2 + 1 / 2 * (1 + ‖s‖) ^ 3 * K0 := by
      have e : ‖(s - 1) / 2‖ = ‖s - 1‖ / 2 := by rw [norm_div, Complex.norm_two]
      have t1 := norm_add_le (1 + (s - 1) / 2) (∑' k, PLB.E k s)
      have t2 := norm_add_le (1 : ℂ) ((s - 1) / 2)
      rw [norm_one, e] at t2
      linarith
    have f1 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have f2 : 1 + ‖s‖ ≤ (1 + ‖s‖) ^ 4 := le_self_pow₀ hR (by norm_num)
    have f3 : (1 + ‖s‖) ^ 3 ≤ (1 + ‖s‖) ^ 4 := pow_le_pow_right₀ hR (by norm_num)
    have f4 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hQ
    have f5 : (1 : ℝ) ≤ (1 + ‖s‖) ^ 4 := one_le_pow₀ hR
    have g1 : (q : ℝ) * (1 + ‖s‖) ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := mul_le_mul f1 f2 (by positivity) (by positivity)
    have g2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := one_le_mul_of_one_le_of_one_le f4 f5
    have g3 : 1 + ‖s‖ ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := by
      calc 1 + ‖s‖ = 1 * (1 + ‖s‖) := by ring
        _ ≤ _ := mul_le_mul f4 f2 (by positivity) (by positivity)
    have g4 : (1 + ‖s‖) ^ 3 * K0 ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 * K0 := by
      apply mul_le_mul_of_nonneg_right _ hK0n
      calc (1 + ‖s‖) ^ 3 = 1 * (1 + ‖s‖) ^ 3 := by ring
        _ ≤ _ := mul_le_mul f4 f3 (by positivity) (by positivity)
    have g5 : 0 ≤ (1 + ‖s‖) ^ 3 * K0 := by positivity
    show ‖(s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s) + m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s)‖ ≤ _
    calc _ ≤ ‖(s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s)‖ + ‖m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s)‖ :=
          norm_add_le _ _
      _ = ‖s - 1‖ * ‖m₂ + ∑' k, T (k + 1) * PLB.D k s‖ + ‖m‖ * ‖1 + (s - 1) / 2 + ∑' k, PLB.E k s‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (1 + ‖s‖) * (2 * q + 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0) +
          1 * (1 + (1 + ‖s‖) / 2 + 1 / 2 * (1 + ‖s‖) ^ 3 * K0) :=
          add_le_add (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (mul_le_mul hm h3 (norm_nonneg _) zero_le_one)
      _ ≤ (4 + 9 * K0) * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := by nlinarith

end Ad3.S

end
end

section
namespace Ad3.S

theorem t1 : T1 := (@GlobalTheory.CompanionTheory.HalfTheta.t1 : T1)

theorem t2 : T2 := (@GlobalTheory.CompanionTheory.HalfWeight.finite_sum_splitting : T2)

theorem t3 : T3 := (@Ad3.S.third_estimate_of_first_two : T1 → T2 → T3) t1 t2

theorem t4 : T4 := (@GlobalTheory.CompanionTheory.HalfWeight.gauss_sum_conjugation : T4)

theorem t5 : T5 := (@GlobalTheory.CompanionTheory.HalfWeightUnfold.term_of_theta : T3 → T4 → T5) t3 t4

theorem u0 : U0 := (@GlobalTheory.CompanionTheory.ModularTiling.exists_weight_Gamma0 : U0)

theorem u1 : U1 := (@GlobalTheory.CompanionTheory.Unfolding.unfolding_strip : U1)

theorem b1 : B1 := (@GlobalTheory.CompanionTheory.CuspDecay.b1 : B1)

theorem b2 : B2 := (@GlobalTheory.CompanionTheory.ThetaBound.b2 : B2)

theorem u2a : HorizontalIntegralTwisted := (@GlobalTheory.CompanionTheory.HalfIntegralWeight.unfolding_of_bound : B2 → HorizontalIntegralTwisted) b2

theorem u2 : U2 := (@GlobalTheory.CompanionTheory.HalfWt.strip_integral : B1 → B2 → HorizontalIntegralTwisted → U2) b1 b2 u2a

theorem d1 : D1 := (@GlobalTheory.CompanionTheory.CuspHeight.integrableOn_translate_fd : D1)

theorem lB : LB := (@Ad3.S.lB_of : LB)

theorem n1 : N1 := (@GlobalTheory.CompanionTheory.SquareRootCount.rr_eq : N1)

theorem n2 : N2 := (@GlobalTheory.CompanionTheory.SqrtCount.countingSquareRoots : N2)

theorem a2 : A2 := (@GlobalTheory.CompanionTheory.SquareEuler.euler_coeff : N1 → N2 → A2) n1 n2

theorem a1 : A1 := (@GlobalTheory.CompanionTheory.HalfInt.charpoly_factor_coeff_zero_valuation_eq_prod : LB → N2 → A2 → A1) lB n2 a2

theorem a0 : A0 := (@GlobalTheory.CompanionTheory.HalfIntZero.main : LB → N2 → A2 → A0) lB n2 a2

theorem w0 : W0 := (@GlobalTheory.CompanionTheory.HalfWeight.w0 : W0)

theorem w1 : W1 := (@GlobalTheory.CompanionTheory.HalfIntegral.kernel_fourier_integration_by_parts : W0 → W1) w0

theorem w2 : W2 := (@GlobalTheory.CompanionTheory.HalfWeight.kernel_fourier_continuation_decay : W0 → W1 → W2) w0 w1

theorem p1 : P1 := (@GlobalTheory.CompanionTheory.HalfWeightKernel.poisson_kernel : W0 → W2 → P1) w0 w2

theorem p2 : P2 := (@GlobalTheory.CompanionTheory.EisensteinPoissonSummation.eisenstein_cusp_zero_fourier_expansion : P1 → P2) p1

theorem e0 : E0 := (@GlobalTheory.CompanionTheory.HalfInt.half_integral_eisenstein_continuation : A0 → A1 → W0 → W1 → W2 → P2 → E0) a0 a1 w0 w1 w2 p2

theorem pR : PR := (@GlobalTheory.CompanionTheory.HalfIntPR.pr : PR)

theorem g0 : G0 := (@GlobalTheory.CompanionTheory.InvGammaStrip.g0 : G0)

theorem hI : HI := (@GlobalTheory.CompanionTheory.RgAds.holomorphy_integral_param : HI)

theorem s1 : S1 := (@GlobalTheory.CompanionTheory.HalfWeight.unfolded_identity_of : T5 → U1 → U2 → B2 → S1) t5 u1 u2 b2

theorem shim : Shim := (@GlobalTheory.CompanionTheory.ShimStep.shim_of : U0 → B2 → D1 → E0 → PR → G0 → HI → S1 → Shim) u0 b2 d1 e0 pR g0 hI s1

theorem e1 : E1 := (@GlobalTheory.CompanionTheory.HalfIntegral.e1 : E1)

theorem e1b : faceMap_comp_succAbove_castSucc := (@GlobalTheory.CompanionTheory.Rgads.e1b : faceMap_comp_succAbove_castSucc)

theorem e2a : E2a := (@GlobalTheory.CompanionTheory.HeckeEig.e2a : E2a)

theorem e2b : E2b := (@GlobalTheory.CompanionTheory.HalfIntWeight.localSeries : E2b)

theorem e2 : E2 := (@GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients.e2 : faceMap_comp_succAbove_castSucc → E2a → E2b → E2) e1b e2a e2b

theorem e3 : E3 := (@GlobalTheory.CompanionTheory.EulerThree.HalfWt.adjoint_lift_twisted_euler_product : faceMap_comp_succAbove_castSucc → E3) e1b


theorem anOf : AnOf := (@GlobalTheory.CompanionTheory.AdjointLift.anOf : AnOf)

end Ad3.S
end
