module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidalStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTopStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransformStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariantStatement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem lastRow_uGL_mul (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (GroundTheory.Automorphic.FourierWhittaker.uGL X * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, GroundTheory.Automorphic.FourierWhittaker.coe_uGL, Matrix.mul_apply,
    GroundTheory.Automorphic.FourierWhittaker.uMat_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro c _ hc
    rw [if_neg (Ne.symm hc), dite_eq_right (not_lt.2 (Fin.le_last c)), zero_mul]
  · simp

theorem jswWhit_fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) :
    GlobalTheory.JSW.whit (fT φ Φ) g = sqrtC Φ (yInf g) * GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv (yInf g))) := by
  simp only [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [fT_of_lastRow (lastRow_uGL_mul X g), mul_assoc (GroundTheory.Automorphic.FourierWhittaker.uGL X) g]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem indN_eq_re (N : ℕ) (y : Fin (m + 1) → Af E) : indN N y = ((indN N y).re : ℂ) := by
  unfold indN; split_ifs <;> simp

theorem indN_re_nonneg (N : ℕ) (y : Fin (m + 1) → Af E) : 0 ≤ (indN N y).re := by
  unfold indN; split_ifs <;> simp

theorem wt_coe (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    (((wt N x g : ℝ≥0) : ℝ) : ℂ) = indN N (yFin g) * (detPow E (m + 1) x g : ℂ) := by
  have h0 : 0 ≤ detPow E (m + 1) x g := norm_nonneg _
  rw [wt, Real.coe_toNNReal _ (mul_nonneg (indN_re_nonneg N _) h0), Complex.ofReal_mul, ← indN_eq_re]

theorem sqrtC_mul_conj {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (u : Fin (m + 1) → Cinf E) :
    sqrtC Φ u * conj (sqrtC Φ u) = Φ u := by
  rw [sqrtC, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hΦ u).1]
  exact Complex.ext (by simp) (by simp [(hΦ u).2])

theorem psi_lastRow_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) =
      fT φ Φ g * conj (fT φ' Φ g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, fT, fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change φ (g * (infGL E (m + 1)) (secInv (yInf g))) * conj (φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem uInt_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.uInt φ φ' Φ N x g =
      GlobalTheory.JSW.whit (fT φ Φ) g * conj (GlobalTheory.JSW.whit (fT φ' Φ) g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, jswWhit_fT, jswWhit_fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change GlobalTheory.JSW.whit φ (g * (infGL E (m + 1)) (secInv (yInf g))) *
    conj (GlobalTheory.JSW.whit φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem NE_eq_ratMirU_zero : GlobalTheory.CellDec.NE E (m + 1) = ratMirU E (m + 1) 0 := by
  have h : GlobalTheory.SmGL.unipB E (Fin (m + 1)) = mirU E (m + 1) 0 := by
    ext γ
    rw [GlobalTheory.SmGL.mem_unipB, mem_mirU_zero]
  rw [GlobalTheory.CellDec.NE, ratMirU, h]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isMir_of_mem_mirU_zero {γ : GL (Fin (m + 1)) E} (hγ : γ ∈ mirU E (m + 1) 0) : IsMir m γ := by
  intro i k h
  refine hγ i k (Nat.zero_le _) ?_
  rcases h with h | h
  · have := k.2; change (k : ℕ) ≤ i; omega
  · have := k.2; omega

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

theorem enorm_uInt_self {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ = ‖GlobalTheory.JSW.whit (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) := by
  rw [uInt_eq hΦ, enorm_mul, enorm_mul, RCLike.enorm_conj, pow_two]
  congr 1
  have h0 : (((wt N x g : ℝ≥0) : ℝ) : ℂ) = ((wt N x g : ℝ≥0) : ℂ) := rfl
  rw [h0, enorm_eq_nnnorm]
  congr 1
  ext
  simp

end GlobalTheory.ZUnf
