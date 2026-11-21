import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PUnipotentCoordinates
import GroundTheory.PAdicHodge.SlopeCauchyBinet
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGramSumOfMinors
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.POmitStepPolynomial
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PDiagonalQuotient
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereHeightUniform
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalHeightReduction
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernelPairing
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalReduction
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalPairing
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreConstantClosedForm
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreIntegralInvariant
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PCompactPairCurveForm
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PBarCurveForm

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem UnipotentLeadingMinor.proof : UnipotentLeadingMinor.Statement := by
  intro R _ N a l hl
  unfold leadingMinor
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [unipotentMatrix]
  · intro i j hji
    have hji' : Fin.castLE hl j < Fin.castLE hl i := hji
    simp only [Matrix.submatrix_apply, unipotentMatrix, Matrix.of_apply]
    rw [dif_neg (not_lt.mpr hji'.le), if_neg (ne_of_gt hji')]

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Matrix Finset

theorem PluckerFrameChange.proof : PluckerFrameChange.Statement := by
  classical
  intro R _ l N V g I hI
  have hmul : (V * g).submatrix id (I.orderEmbOfFin hI) =
      V * g.submatrix id (I.orderEmbOfFin hI) := by
    ext i j; simp [Matrix.mul_apply]
  have hL : pluckerCoord (V * g) I =
      ∑ s : GroundTheory.PAdicHodge.KSubset N l,
        (V.submatrix id s.emb).det *
          ((g.submatrix id (I.orderEmbOfFin hI)).submatrix s.emb id).det := by
    rw [pluckerCoord, dif_pos hI, hmul, GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  rw [hL, Finset.sum_subtype (Finset.powersetCard l (Finset.univ : Finset (Fin N)))
    (p := fun J : Finset (Fin N) => J.card = l) (fun J => Finset.mem_powersetCard_univ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : s.1.card = l ∧ I.card = l := ⟨s.2, hI⟩
  rw [pluckerCoord, dif_pos s.2, minorOn, dif_pos h2]
  rfl

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate

theorem LineQuotientDeterminant.proof : LineQuotientDeterminant.Statement := by
  intro E _ _ _ S hS e he he0 f
  have hne : (0 : ℝ) < ‖e‖ := norm_pos_iff.mpr he0

  have hdet : (Matrix.gram ℂ ![e, f]).det.re = ‖e‖ ^ 2 * ‖f‖ ^ 2 - ‖⟪e, f⟫_ℂ‖ ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← inner_conj_symm e f, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      mul_comm (conj _), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp [Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact norm_inner_symm f e

  have hee : ⟪e, e⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr he0
  set c : ℂ := ⟪e, f⟫_ℂ / ⟪e, e⟫_ℂ with hc
  set h : E := f - c • e with hh
  have hce : c * ⟪e, e⟫_ℂ = ⟪e, f⟫_ℂ := by
    rw [hc]
    field_simp
  have horth : ⟪e, h⟫_ℂ = 0 := by
    rw [hh, inner_sub_right, inner_smul_right, hce, sub_self]
  have hpyth : ∀ d : ℂ, ‖h + d • e‖ ^ 2 = ‖h‖ ^ 2 + ‖d • e‖ ^ 2 := by
    intro d
    have h0 : ⟪h, d • e⟫_ℂ = 0 := by
      rw [inner_smul_right, inner_eq_zero_symm.mp horth, mul_zero]
    simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) h (d • e) h0
  have hf : f = h + c • e := by rw [hh, sub_add_cancel]
  have hnc : ‖c‖ * ‖e‖ ^ 2 = ‖⟪e, f⟫_ℂ‖ := by
    rw [← hce, norm_mul, inner_self_eq_norm_sq_to_K]
    simp
  have hdet' : (Matrix.gram ℂ ![e, f]).det.re = (‖e‖ * ‖h‖) ^ 2 := by
    have hf2 : ‖f‖ ^ 2 = ‖h‖ ^ 2 + (‖c‖ * ‖e‖) ^ 2 := by
      rw [hf, hpyth c, norm_smul]
    rw [hdet, hf2, ← hnc]
    ring

  have hspan : ∀ s ∈ S, ∃ d : ℂ, d • e = s := by
    intro s hs
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : S)
      (by simpa using he0)).mp hS ⟨s, hs⟩
    exact ⟨d, by simpa using congrArg Subtype.val hd⟩

  have hmk : (Submodule.Quotient.mk h : E ⧸ S) = Submodule.Quotient.mk f := by
    rw [Submodule.Quotient.eq, hh, sub_sub_cancel_left]
    exact S.neg_mem (S.smul_mem c he)
  have hq : ‖(Submodule.Quotient.mk f : E ⧸ S)‖ = ‖h‖ := by
    apply le_antisymm
    · rw [← hmk]
      exact Submodule.Quotient.norm_mk_le S h
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨m, hm, hmε⟩ := Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk f : E ⧸ S) hε
      rw [← hmk, Submodule.Quotient.eq] at hm
      obtain ⟨d, hd⟩ := hspan _ hm
      have hm' : m = h + d • e := by rw [hd, add_sub_cancel]
      have : ‖h‖ ^ 2 ≤ ‖m‖ ^ 2 := by
        rw [hm', hpyth d]
        nlinarith [sq_nonneg ‖d • e‖]
      have : ‖h‖ ≤ ‖m‖ := by
        nlinarith [norm_nonneg h, norm_nonneg m]
      linarith
  rw [hdet', hq, Real.sqrt_sq (by positivity)]

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Submodule

theorem quotient_span_bijective_second_basis {R : Type} [CommRing R] (v : Fin 2 → R) (hv : v 0 = 1) :
    Function.Bijective (fun r : R => r • (span R {v}).mkQ (eps R 1)) := by
  constructor
  · intro r s h
    simp only at h
    rw [← map_smul, ← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq,
      ← sub_smul, mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [eps, hv] at h0 h1
    subst h0
    simp at h1
    exact sub_eq_zero.mp h1.symm
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨x 1 - x 0 * v 1, ?_⟩
    simp only
    rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨-x 0, ?_⟩
    ext k
    fin_cases k <;> simp [eps, hv]

theorem quotient_span_bijective_first_basis {R : Type} [CommRing R] (v : Fin 2 → R) (hv : v 1 = 1) :
    Function.Bijective (fun r : R => r • (span R {v}).mkQ (eps R 0)) := by
  constructor
  · intro r s h
    simp only at h
    rw [← map_smul, ← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq,
      ← sub_smul, mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [eps, hv] at h0 h1
    subst h1
    simp at h0
    exact sub_eq_zero.mp h0.symm
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨x 0 - x 1 * v 0, ?_⟩
    simp only
    rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨-x 1, ?_⟩
    ext k
    fin_cases k <;> simp [eps, hv]

theorem SectionLocalEquation.proof : SectionLocalEquation.Statement := by
  intro R _ a₁ a₂ b₁ b₂
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact quotient_span_bijective_second_basis _ (by simp [eps])
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp [eps]
  · exact quotient_span_bijective_first_basis _ (by simp [eps])
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp [eps]
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨a₁, ?_⟩
    ext k
    fin_cases k <;> simp [eps]

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial IsLocalRing

theorem localization_span_singleton_dvr {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha : a ≠ 0) [hP : (Ideal.span {a}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {a})) ∧
      Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {a})) a) := by
  set L := Localization.AtPrime (Ideal.span {a})
  have : IsDomain L :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (Ideal.span {a}).primeCompl L inferInstance
  have hmax : maximalIdeal L = Ideal.span {algebraMap A L a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {a}) L, Ideal.map_span,
      Set.image_singleton]
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have hne : algebraMap A L a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hnf : ¬ IsField L := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hdvr : IsDiscreteValuationRing L :=
    ((IsDiscreteValuationRing.TFAE L hnf).out 4 0).mp (⟨⟨_, hmax⟩⟩ : (maximalIdeal L).IsPrincipal)
  exact ⟨hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax⟩

theorem DiagonalLocalDVR.proof (h0 : DiagonalQuotient.Statement) : DiagonalLocalDVR.Statement := by
  intro R _ _ _
  have hd : (diagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.1 inferInstance
  have hm : (mixedDiagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.2.2.2 inferInstance
  have h1 : (X 0 - X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(1 : R), 0]) h
    simp at this
  have h2 : (1 - X 0 * X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(0 : R), 0]) h
    simp at this
  exact ⟨⟨hd, @localization_span_singleton_dvr _ _ _ _ _ h1 hd⟩,
    ⟨hm, @localization_span_singleton_dvr _ _ _ _ _ h2 hm⟩⟩

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate Matrix

lemma blochVector_apply (e : EuclideanSpace ℂ (Fin 2)) :
    blochVector e 0 = 2 * ((e 0).re * (e 1).re + (e 0).im * (e 1).im) ∧
    blochVector e 1 = 2 * ((e 0).re * (e 1).im - (e 0).im * (e 1).re) ∧
    blochVector e 2 = (e 0).re ^ 2 + (e 0).im ^ 2 - (e 1).re ^ 2 - (e 1).im ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [blochVector, pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

lemma norm_sq_complex_two_re_im (e : EuclideanSpace ℂ (Fin 2)) :
    ‖e‖ ^ 2 = (e 0).re ^ 2 + (e 0).im ^ 2 + (e 1).re ^ 2 + (e 1).im ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  ring

theorem BlochOverlap.proof : BlochOverlap.Statement := by
  refine ⟨fun e he => ?_, fun e₁ e₂ h₁ h₂ => ?_⟩
  · have hs := norm_sq_complex_two_re_im e
    rw [he] at hs
    obtain ⟨h0, h1, h2⟩ := blochVector_apply e
    have hn : ‖blochVector e‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, h0, h1, h2]
      linear_combination (-(1 : ℝ) - ((e 0).re ^ 2 + (e 0).im ^ 2 + (e 1).re ^ 2 + (e 1).im ^ 2)) * hs
    have h0' : 0 ≤ ‖blochVector e‖ := norm_nonneg _
    nlinarith [hn]
  · have hs₁ := norm_sq_complex_two_re_im e₁
    have hs₂ := norm_sq_complex_two_re_im e₂
    rw [h₁] at hs₁
    rw [h₂] at hs₂
    obtain ⟨a0, a1, a2⟩ := blochVector_apply e₁
    obtain ⟨b0, b1, b2⟩ := blochVector_apply e₂
    rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [RCLike.inner_apply, conj_trivial, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, a0, a1, a2, b0, b1, b2]
    linear_combination (-(1 : ℝ) / 2) * (((e₂ 0).re ^ 2 + (e₂ 0).im ^ 2 + (e₂ 1).re ^ 2 + (e₂ 1).im ^ 2) * hs₁ + hs₂)

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate

noncomputable section

theorem quotient_norm_eq_norm_sub_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : Submodule ℂ E) [U.HasOrthogonalProjection] (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ U)‖ = ‖x - U.starProjection x‖ := by
  have h1 : ‖(Submodule.Quotient.mk x : E ⧸ U)‖ = Metric.infDist x (U : Set E) :=
    QuotientAddGroup.norm_mk (S := U.toAddSubgroup) x
  rw [h1, Metric.infDist_eq_iInf, Submodule.starProjection_minimal]
  simp only [dist_eq_norm]
  rfl

theorem quotient_norm_sq_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e₁ e₂ : E) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) :
    ‖(Submodule.Quotient.mk e₁ : E ⧸ ℂ ∙ e₂)‖ ^ 2 = 1 - ‖⟪e₁, e₂⟫_ℂ‖ ^ 2 := by
  rw [quotient_norm_eq_norm_sub_starProjection, Submodule.starProjection_unit_singleton ℂ h₂,
    @norm_sub_sq ℂ, inner_smul_right, norm_smul, h₁, h₂, mul_one, ← inner_conj_symm e₁ e₂,
    Complex.norm_conj, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  rw [RCLike.re_to_complex, Complex.ofReal_re]
  ring

theorem SectionNormLog.proof (h0 : BlochOverlap.Statement) : SectionNormLog.Statement := by
  intro e₁ e₂ h₁ h₂
  have hsq := quotient_norm_sq_line e₁ e₂ h₁ h₂
  refine ⟨hsq, fun _ => ?_⟩
  rw [h0.2 e₁ e₂ h₁ h₂] at hsq
  unfold kernelL
  set q := ‖(Submodule.Quotient.mk e₁ : EuclideanSpace ℂ (Fin 2) ⧸ ℂ ∙ e₂)‖
  have : (1 - ⟪blochVector e₁, blochVector e₂⟫_ℝ) / 2 = q ^ 2 := by rw [hsq]; ring
  rw [this, Real.log_pow]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

theorem MixedCoefficient.proof : MixedCoefficient.Statement := by
  intro S _ G A₁ A₂ v₁ v₂ h₁ h₂
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add] at hp hq ⊢
    rw [hp, hq]; ring
  | mul_X p i hp =>
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Derivation.leibniz, pderiv_X_self, smul_eq_mul,
        map_add, map_mul, eval_X, Matrix.cons_val_zero, mul_one] at hp ⊢
      have e : pderiv (1 : Fin 2) (X (0 : Fin 2) : MvPolynomial (Fin 2) S) = 0 :=
        pderiv_X_of_ne (by decide)
      rw [e]
      simp only [map_zero, mul_zero, zero_add]
      rw [hp]
      linear_combination (eval ![A₁, A₂] (pderiv 0 p) - v₂ * eval ![A₁, A₂] (pderiv 0 (pderiv 1 p))) * h₁
    · simp only [Fin.mk_one, Fin.isValue, Derivation.leibniz, pderiv_X_self, smul_eq_mul,
        map_add, map_mul, eval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one] at hp ⊢
      have e : pderiv (0 : Fin 2) (X (1 : Fin 2) : MvPolynomial (Fin 2) S) = 0 :=
        pderiv_X_of_ne (by decide)
      rw [e]
      simp only [map_zero, mul_zero, zero_add, add_zero]
      rw [hp]
      linear_combination (eval ![A₁, A₂] (pderiv 1 p) - v₁ * eval ![A₁, A₂] (pderiv 0 (pderiv 1 p))) * h₂

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

lemma SphereMoment.exists_unit (a : E3) :
    ∃ u : E3, ‖u‖ = 1 ∧ ∀ n : E3, ⟪a, n⟫_ℝ = ‖a‖ * ⟪u, n⟫_ℝ := by
  by_cases h : a = 0
  · refine ⟨EuclideanSpace.single 0 1, by simp, fun n => by simp [h]⟩
  · have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr h
    refine ⟨‖a‖⁻¹ • a, ?_, fun n => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna]
    · rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hna, one_mul]

lemma SphereMoment.moment (h0 : SphereHeightUniform.Statement) (a : E3) (k : ℕ) :
    ∫ n, ⟪a, (n : E3)⟫_ℝ ^ k ∂sphereMeasure =
      ‖a‖ ^ k * (2⁻¹ * ((1 - (-1 : ℝ) ^ (k + 1)) / (k + 1))) := by
  obtain ⟨u, hu, ha⟩ := SphereMoment.exists_unit a
  have hc : Continuous fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ :=
    continuous_const.inner continuous_subtype_val
  calc ∫ n, ⟪a, (n : E3)⟫_ℝ ^ k ∂sphereMeasure
      = ∫ n, ‖a‖ ^ k * ⟪u, (n : E3)⟫_ℝ ^ k ∂sphereMeasure := by
        simp_rw [ha, mul_pow]
    _ = ‖a‖ ^ k * ∫ n, ⟪u, (n : E3)⟫_ℝ ^ k ∂sphereMeasure := integral_const_mul _ _
    _ = ‖a‖ ^ k * ∫ t, t ^ k ∂(sphereMeasure.map fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ) := by
        rw [integral_map hc.measurable.aemeasurable
          (continuous_pow k).aestronglyMeasurable]
    _ = ‖a‖ ^ k * (2⁻¹ * ((1 - (-1 : ℝ) ^ (k + 1)) / (k + 1))) := by
        rw [h0 u hu, integral_smul_measure, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
        simp [smul_eq_mul]

theorem SphereMoment.proof (h0 : SphereHeightUniform.Statement) : SphereMoment.Statement := by
  intro a m
  refine ⟨?_, ?_⟩
  · rw [SphereMoment.moment h0, pow_succ, pow_mul]
    have h2 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    norm_num
    field_simp
  · rw [SphereMoment.moment h0, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    norm_num

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

theorem FibrePushforward.proof (h0 : SphereMoment.Statement) : FibrePushforward.Statement := by
  intro k hk a
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have h1 : m + 1 - 1 = m := by omega
  rw [h2, h1, (h0 a m).1, real_inner_self_eq_norm_sq, ← pow_mul]
  have hpos : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Real
open scoped InnerProductSpace

theorem norm_circleMap_sub_ofReal_sq (r φ : ℝ) :
    ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos φ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_re, Complex.exp_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem ZonalKernel.proof : ZonalKernel.Statement := by
  intro c₁ h₁ c₂ h₂ hne
  obtain ⟨h₁l, h₁u⟩ := h₁
  obtain ⟨h₂l, h₂u⟩ := h₂
  have hs₁ : Real.sqrt (1 - c₁ ^ 2) ^ 2 = 1 - c₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs₂ : Real.sqrt (1 - c₂ ^ 2) ^ 2 = 1 - c₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) with hBdef
  set A := 1 - c₁ * c₂ with hAdef
  set D := |c₁ - c₂| with hDdef
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hA : 0 ≤ A := by nlinarith
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hABD : A ^ 2 = B ^ 2 + D ^ 2 := by
    rw [hBdef, mul_pow, hs₁, hs₂, hDdef, sq_abs]; ring
  have hAD : 0 < A + D := by linarith
  set r := B / (A + D) with hrdef
  have hr0 : 0 ≤ r := div_nonneg hB hAD.le
  have hBlt : B < A + D := by nlinarith
  have hr1 : r < 1 := (div_lt_one hAD).mpr hBlt
  have key : ∀ φ : ℝ, kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ =
      (1 / 2) * Real.log ((A + D) / 4) + Real.log ‖circleMap 0 1 φ - (r : ℂ)‖ := by
    intro φ
    have hinner : ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = c₁ * c₂ + B * Real.cos φ := by
      simp [spherePoint, PiLp.inner_apply, Fin.sum_univ_three, hBdef]
      ring
    have hne0 : ‖circleMap 0 1 φ - (r : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h
      have := congrArg norm h
      rw [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
      norm_num at this
      linarith
    have hfac : (1 - (c₁ * c₂ + B * Real.cos φ)) / 2 =
        (A + D) / 4 * ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 := by
      rw [norm_circleMap_sub_ofReal_sq, hrdef]
      field_simp
      linear_combination (2 : ℝ) * hABD
    rw [kernelL, hinner, hfac, Real.log_mul (by positivity) (pow_ne_zero 2 hne0), Real.log_pow]
    push_cast
    ring
  simp only [key]
  have hint : IntervalIntegrable (fun φ : ℝ => Real.log ‖circleMap 0 1 φ - (r : ℂ)‖)
      MeasureTheory.volume 0 (2 * π) := circleIntegrable_log_norm_sub_const (a := (r : ℂ)) (c := 0) 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const]
  have havg := circleAverage_log_norm_sub_const₀ (a := (r : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  rw [circleAverage_def, smul_eq_mul] at havg
  have hpi : (2 * π) ≠ 0 := by positivity
  have hsum : A + D = (1 + max c₁ c₂) * (1 - min c₁ c₂) := by
    rcases le_total c₁ c₂ with h | h
    · rw [max_eq_right h, min_eq_left h, hDdef, abs_of_nonpos (by linarith), hAdef]; ring
    · rw [max_eq_left h, min_eq_right h, hDdef, abs_of_nonneg (by linarith), hAdef]; ring
  rw [zonalKernel, ← hsum, mul_add, havg, smul_eq_mul, sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi]
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

theorem ZonalBilinearFormula.proof (hB : ZonalHeightReduction.Statement)
    (hC : ZonalKernelPairing.Statement) : ZonalBilinearFormula.Statement := by
  refine ⟨fun F H => (hB F H).2.trans (hC F H), ?_⟩
  have h := (hB Polynomial.X Polynomial.X).2.trans (hC Polynomial.X Polynomial.X)
  simp only [Polynomial.eval_X] at h
  rw [h]
  have hm : uniformMean (fun x : ℝ => x) = 0 := by
    simp [uniformMean, integral_id]
  have hg : ∀ c : ℝ, centredPrimitive Polynomial.X c = (c ^ 2 - 1) / 2 := by
    intro c
    simp only [centredPrimitive, Polynomial.eval_X]
    rw [hm]
    simp only [sub_zero, integral_id]
    ring
  have hq : ∀ c : ℝ, centredPrimitive Polynomial.X c * centredPrimitive Polynomial.X c / (1 - c ^ 2)
      = (1 - c ^ 2) / 4 := by
    intro c
    rw [hg]
    rcases eq_or_ne (1 - c ^ 2) 0 with h0 | h0
    · have : c ^ 2 - 1 = 0 := by linarith
      rw [h0, this]; simp
    · field_simp
      ring
  rw [hm]
  simp only [hq]
  simp [intervalIntegral.integral_div, integral_pow]
  norm_num

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped ComplexConjugate

theorem TorusInvariantDiagonal.proof : TorusInvariantDiagonal.Statement := by
  intro ι T V _ _ _ _ _ _ ρ L χ _ _ hχ hρ h _ hinv i j hij x hx y hy
  by_contra hne
  apply hij
  apply hχ
  ext t
  have key := hinv t x y
  rw [hρ i x hx t, hρ j y hy t] at key
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul] at key

  have h1 : conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) = 1 := by
    have : (conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) - 1) * h x y = 0 := by
      linear_combination key
    rcases mul_eq_zero.1 this with h2 | h2
    · linear_combination h2
    · exact absurd h2 hne
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, Circle.coe_eq_one, inv_mul_eq_one] at h1
  exact congrArg (fun z : Circle => (z : ℂ)) h1

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Finset

theorem add_pow_succ_of_sq_eq_zero {S : Type*} [CommRing S] {x y : S} (hx : x ^ 2 = 0)
    (m : ℕ) : (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : S) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    push_cast
    linear_combination (x + y) * ih + ((m : S) + 1) * y ^ m * hx

theorem sum_pow_card_of_sq_eq_zero {S ι : Type*} [CommRing S] [DecidableEq ι] (x : ι → S)
    (hx : ∀ j, x j ^ 2 = 0) (s : Finset ι) :
    (∑ j ∈ s, x j) ^ (s.card + 1) = 0 ∧
      (∑ j ∈ s, x j) ^ s.card = (s.card.factorial : S) * ∏ j ∈ s, x j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [sum_insert ha, prod_insert ha, card_insert_of_notMem ha]
    constructor
    · rw [add_pow_succ_of_sq_eq_zero (hx a) (s.card + 1), pow_succ, h1]
      simp
    · rw [add_pow_succ_of_sq_eq_zero (hx a) s.card, h1, h2, Nat.factorial_succ]
      push_cast
      ring

theorem TopPowerDiagonal.proof : TopPowerDiagonal.Statement := by
  intro S _ D ω lam hω
  have h := (sum_pow_card_of_sq_eq_zero (fun j => lam j * ω j)
    (fun j => by rw [mul_pow, hω j, mul_zero]) (univ : Finset (Fin D))).2
  rw [card_univ, Fintype.card_fin, prod_mul_distrib] at h
  rw [h, mul_assoc]

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

theorem PolarisationDegreeD.proof : PolarisationDegreeD.Statement := by
  intro K _ _ r D φ ψ h P hP
  set χ : MvPolynomial (Fin r) K →ₗ[K] K := φ - ψ with hχdef
  have hχ : ∀ c : Fin r → K, χ ((∑ i, C (c i) * X i) ^ D) = 0 := fun c => by
    simp [hχdef, h c]

  have hmono : ∀ k : Fin r → ℕ, (∏ i, X i ^ k i : MvPolynomial (Fin r) K) =
      monomial (Finsupp.equivFunOnFinite.symm k) 1 := by
    intro k
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp

  have hexp : ∀ c : Fin r → K, (∑ i, C (c i) * X i : MvPolynomial (Fin r) K) ^ D =
      ∑ k ∈ piAntidiag univ D,
        C ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) * ∏ i, X i ^ k i := by
    intro c
    rw [sum_pow_eq_sum_piAntidiag]
    refine sum_congr rfl fun k _ => ?_
    simp only [mul_pow, prod_mul_distrib, map_mul, map_prod, map_pow, map_natCast]
    ring

  set Q : MvPolynomial (Fin r) K := ∑ k ∈ piAntidiag univ D,
      C ((Nat.multinomial univ k : K) * χ (∏ i, X i ^ k i)) * ∏ i, X i ^ k i with hQdef
  have hQ : Q = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_zero, ← hχ c, hexp c, hQdef, map_sum, map_sum]
    refine sum_congr rfl fun k _ => ?_
    have hs : C ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) * ∏ i, X i ^ k i =
        ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) • (∏ i, X i ^ k i : MvPolynomial (Fin r) K) :=
      C_mul'
    rw [hs, map_smul, smul_eq_mul, eval_mul, eval_C]
    simp only [map_prod, map_pow, eval_X]
    ring

  have hzero : ∀ k ∈ piAntidiag univ D, χ (∏ i, X i ^ k i) = 0 := by
    intro k hk
    have hc : coeff (Finsupp.equivFunOnFinite.symm k) Q =
        (Nat.multinomial univ k : K) * χ (∏ i, X i ^ k i) := by
      rw [hQdef, coeff_sum]
      simp_rw [hmono, coeff_C_mul, coeff_monomial, EmbeddingLike.apply_eq_iff_eq]
      simp [hk]
    rw [hQ, coeff_zero] at hc
    have hm : (Nat.multinomial univ k : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.multinomial_pos _ _).ne'
    exact (mul_eq_zero.mp hc.symm).resolve_left hm

  have hP0 : χ P = 0 := by
    rw [as_sum P, map_sum]
    refine sum_eq_zero fun d hd => ?_
    have hdeg : ∑ i, d i = D := by
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hd)
    have hmem : (⇑d : Fin r → ℕ) ∈ piAntidiag univ D := by
      simp [hdeg]
    have hd1 : monomial d (coeff d P) = coeff d P • monomial d (1 : K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hd1, map_smul, smul_eq_mul]
    have := hzero _ hmem
    rw [hmono, Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this, mul_zero]
  have := hP0
  rw [hχdef, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GroundTheory.Heights₂.Heights.FlagBundles
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem UnipotentLeadingMinor.full : UnipotentLeadingMinor.Statement :=
  UnipotentLeadingMinor.proof

theorem PluckerFrameChange.full : PluckerFrameChange.Statement :=
  PluckerFrameChange.proof

theorem GramSumOfMinors.full : GramSumOfMinors.Statement :=
  GramSumOfMinors.proof PluckerFrameChange.full

theorem OmitStepPolynomial.full : OmitStepPolynomial.Statement :=
  OmitStepPolynomial.proof

theorem LineQuotientDeterminant.full : LineQuotientDeterminant.Statement :=
  LineQuotientDeterminant.proof

theorem SectionLocalEquation.full : SectionLocalEquation.Statement :=
  SectionLocalEquation.proof

theorem DiagonalQuotient.full : DiagonalQuotient.Statement :=
  DiagonalQuotient.proof

theorem DiagonalLocalDVR.full : DiagonalLocalDVR.Statement :=
  DiagonalLocalDVR.proof DiagonalQuotient.full

theorem BlochOverlap.full : BlochOverlap.Statement :=
  BlochOverlap.proof

theorem SectionNormLog.full : SectionNormLog.Statement :=
  SectionNormLog.proof BlochOverlap.full

theorem GKernelIdentity.full : GKernelIdentity.Statement :=
  GKernelIdentity.proof

theorem MixedCoefficient.full : MixedCoefficient.Statement :=
  MixedCoefficient.proof

theorem ZonalKernel.full : ZonalKernel.Statement :=
  ZonalKernel.proof

theorem SphereLongitudeCoordinates.full : SphereLongitudeCoordinates.Statement :=
  SphereLongitudeCoordinates.proof

theorem ZonalHeightReduction.full : ZonalHeightReduction.Statement :=
  ZonalHeightReduction.proof SphereLongitudeCoordinates.full ZonalKernel.full

theorem ZonalKernelPairing.full : ZonalKernelPairing.Statement :=
  ZonalKernelPairing.proof

theorem ZonalBilinearFormula.full : ZonalBilinearFormula.Statement :=
  ZonalBilinearFormula.proof ZonalHeightReduction.full ZonalKernelPairing.full

theorem GHatIdentity.full : GHatIdentity.Statement :=
  GHatIdentity.proof GKernelIdentity.full

theorem FibreConstantClosedForm.full : FibreConstantClosedForm.Statement :=
  FibreConstantClosedForm.proof ZonalBilinearFormula.full GHatIdentity.full

theorem fibreConstant_eq (k : ℕ) :
    fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) :=
  FibreConstantClosedForm.full.1 k

theorem FibreIntegralInvariant.full : FibreIntegralInvariant.Statement :=
  FibreIntegralInvariant.proof FibreConstantClosedForm.full

theorem CompactPairCurveForm.full : CompactPairCurveForm.Statement :=
  CompactPairCurveForm.proof

theorem BarCurveForm.full : BarCurveForm.Statement :=
  BarCurveForm.proof

theorem TorusInvariantDiagonal.full : TorusInvariantDiagonal.Statement :=
  TorusInvariantDiagonal.proof

theorem TopPowerDiagonal.full : TopPowerDiagonal.Statement :=
  TopPowerDiagonal.proof

theorem PolarisationDegreeD.full : PolarisationDegreeD.Statement :=
  PolarisationDegreeD.proof

end GroundTheory.Heights₂.Heights.FlagBundles
end
