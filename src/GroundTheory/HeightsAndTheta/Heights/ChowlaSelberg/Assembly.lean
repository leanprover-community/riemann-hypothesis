import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.DedekindZetaEqSumRealEisenstein
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmClassPeriodInvConj
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmClassReducedParamsNonemptyPf
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPhScale
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PKroneckerLimit
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.KroneckerSplitStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PowerIntegralStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.ShiftedSumIntegralStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.CotangentSumStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LogEtaStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.GammaZetaLimitStatement
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PeriodLatticeIdeal
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PMeanOverEmbeddings
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWIdeal
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWUnitOffPrime
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.SuperlatticeRatio
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioInvariant
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LevelOneQExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioInvariant
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PLevelOneQExpansion

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem coe_idealLattice (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice σ I : Set ℂ) = σ '' (I : Set K) := by
  ext z
  exact Iff.rfl

theorem exists_im_ne_zero [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K)
    (σ : K →+* ℂ) : ∃ x : K, (σ x).im ≠ 0 := by
  by_contra h
  push Not at h
  have hreal : (InfinitePlace.mk σ).IsReal := by
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (h x)
  have h1 : 0 < InfinitePlace.nrRealPlaces K := by
    classical
    exact Fintype.card_pos_iff.mpr ⟨⟨_, hreal⟩⟩
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  have h3 : InfinitePlace.nrComplexPlaces K = 0 := by omega
  have h4 := sign_discr K
  rw [h3, pow_zero, S.discr_eq] at h4
  have hd := S.prime.pos
  have : (-(S.d : ℤ)).sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
  rw [this] at h4
  exact absurd h4 (by decide)

theorem latticeArea_periodPair (L : PeriodPair) :
    latticeArea L.lattice = |L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re| := by
  have hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
    rw [← Complex.toBasis_orthonormalBasisOneI,
      MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _)]
    rw [MeasureTheory.measureReal_def, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.volume_parallelepiped]
    simp
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.basisOneI, hvol, mul_one,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]
  congr 1
  ring

theorem epsteinSum_eq_realEisenstein {Λ : Submodule ℤ ℂ} {τ : ℍ} {c : ℂ} (hc : c ≠ 0)
    (h : (fun z => c * z) '' (Λ : Set ℂ) = Theta.latticeOf (τ : ℂ)) (s : ℝ) :
    epsteinSum Λ s = Theta.realEisenstein τ s := by
  have hind : LinearIndependent ℝ ![c⁻¹ * (τ : ℂ), c⁻¹] := by
    refine LinearIndependent.pair_iff.2 fun a b hab => ?_
    refine LinearIndependent.pair_iff.1 (latticeOfTau τ).indep a b ?_
    have e : a • (latticeOfTau τ).ω₁ + b • (latticeOfTau τ).ω₂ =
        c * (a • (c⁻¹ * (τ : ℂ)) + b • c⁻¹) := by
      simp only [latticeOfTau, Complex.real_smul]
      field_simp
    rw [e, hab, mul_zero]
  let P : PeriodPair := ⟨c⁻¹ * (τ : ℂ), c⁻¹, hind⟩
  have hmem : ∀ z : ℂ, z ∈ Λ ↔ c * z ∈ Theta.latticeOf (τ : ℂ) := by
    intro z
    rw [← h]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨y, hy, e⟩
      rwa [← mul_left_cancel₀ hc e]
  have hP : P.lattice = Λ := by
    ext z
    rw [PeriodPair.mem_lattice, hmem, Theta.latticeOf, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨n, m, ?_⟩
      simp only [P, zsmul_eq_mul]
      field_simp
      ring
    · rintro ⟨a, b, e⟩
      refine ⟨b, a, mul_left_cancel₀ hc ?_⟩
      rw [← e]
      simp only [P, zsmul_eq_mul]
      field_simp
      ring
  subst hP
  have harea : latticeArea P.lattice = ‖c⁻¹‖ ^ 2 * τ.im := by
    rw [latticeArea_periodPair]
    have e : P.ω₁.re * P.ω₂.im - P.ω₁.im * P.ω₂.re = -(Complex.normSq c⁻¹ * τ.im) := by
      simp only [P, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, UpperHalfPlane.coe_im]
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) τ.im_pos.le),
      Complex.normSq_eq_norm_sq]
  unfold epsteinSum Theta.realEisenstein
  rw [harea, ← P.latticeEquivProd.symm.toEquiv.tsum_eq]
  refine tsum_congr fun p => ?_
  have hcoe : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) =
      c⁻¹ * ((p.1 : ℂ) * τ + p.2) := by
    rw [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply]
    simp only [P]
    ring
  by_cases hp : p = 0
  · subst hp
    simp
  · have hne : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) ≠ 0 := by
      rw [ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.coe_toEquiv,
        LinearEquiv.map_eq_zero_iff]
      exact hp
    have hz : (p.1 : ℂ) * τ + p.2 ≠ 0 := by
      intro h0
      apply hne
      rw [hcoe, h0, mul_zero]
    rw [if_neg hne, if_neg hp, hcoe, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      Real.mul_rpow (by positivity) τ.im_pos.le, ← Real.rpow_natCast_mul (norm_nonneg _)]
    have ht : 0 < ‖c⁻¹‖ ^ ((2 : ℕ) * s) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hc)) _
    push_cast at ht ⊢
    rw [mul_div_mul_left _ _ ht.ne']

theorem realEisenstein_negConj (τ : ℍ) (s : ℝ) :
    Theta.realEisenstein (Theta.negConj τ) s = Theta.realEisenstein τ s := by
  unfold Theta.realEisenstein
  rw [← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq]
  refine tsum_congr fun p => ?_
  have hneg : ((Theta.negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl
  have him : (Theta.negConj τ).im = τ.im := by
    show ((Theta.negConj τ : ℍ) : ℂ).im = (τ : ℂ).im
    rw [hneg]
    simp
  by_cases hp : p = 0
  · subst hp
    have h00 : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) (0 : ℤ × ℤ) = 0 := by
      ext <;> simp
    rw [if_pos h00, if_pos rfl]
  · have hp' : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p ≠ 0 := by
      intro h0
      apply hp
      simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map,
        Prod.mk_eq_zero, id, neg_eq_zero] at h0
      exact Prod.ext h0.1 h0.2
    rw [if_neg hp', if_neg hp, him]
    congr 2
    have e : (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).1 : ℂ) * (Theta.negConj τ : ℂ) +
        (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).2 : ℂ) =
          -(starRingEnd ℂ) ((p.1 : ℂ) * τ + p.2) := by
      simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map, id, hneg,
        map_add, map_mul, map_intCast, Int.cast_neg]
      ring
    rw [e, norm_neg, Complex.norm_conj]

theorem partialZeta_eq_toReal (A : ClassGroup (𝓞 K)) (s : ℝ) :
    partialZeta A s = (∑' t : (ClassGroup.mk0 ⁻¹' {A} : Set (Ideal (𝓞 K))⁰),
      ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s))).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  unfold partialZeta
  refine tsum_congr fun t => ?_
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.rpow_neg (Nat.cast_nonneg _)]

theorem ClassEpstein.proof [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K) :
    ClassEpstein.Statement S := by
  intro σ C 𝔟 hC s hs
  subst hC
  have hK : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have hσ := exists_im_ne_zero S σ
  obtain ⟨τ, c, hc, himg⟩ := Theta.exists_isLatticeParam_fractionalIdeal hK σ hσ 𝔟
  obtain ⟨w, hw, hinv⟩ := Theta.ClassPeriodInv.exists_inv_eq_conj hK σ hσ 𝔟
  obtain ⟨c', hc', himg'⟩ : Theta.IsLatticeParam
      (σ '' (((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K))
      (Theta.negConj τ) := by
    rw [hinv]
    exact Theta.ClassPeriodInv.isLatticeParam_conj ⟨c, hc, himg⟩ hw
  have key := Theta.projectiveLineClassData.class_sum hK σ hσ 𝔟⁻¹ (Theta.negConj τ) c' hc' himg' hs
  have hE : epsteinSum (idealLattice σ 𝔟) s = Theta.realEisenstein τ s :=
    epsteinSum_eq_realEisenstein hc (by rw [coe_idealLattice]; exact himg) s
  have hD : Real.sqrt |(discr K : ℝ)| = Real.sqrt S.d := by
    rw [S.discr_eq]
    push_cast
    rw [abs_neg, Nat.abs_cast]
  rw [realEisenstein_negConj, hD] at key
  have hw0 : (Units.torsionOrder K : ENNReal) ≠ 0 := by
    exact_mod_cast Units.torsionOrder_ne_zero K
  have hsum := (ENNReal.eq_div_iff hw0 (ENNReal.natCast_ne_top _)).mpr key
  have hcl : ClassGroup.mk K 𝔟 = (ClassGroup.mk K 𝔟⁻¹)⁻¹ := by rw [map_inv, inv_inv]
  rw [hcl, partialZeta_eq_toReal]
  erw [hsum]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (Theta.realEisenstein_nonneg _ _)), hE]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem ZetaFactor.proof (S : PrimeDiscriminant K) : ZetaFactor.Statement S := by
  intro s hs
  have hs0 : (0 : ℝ) < s := by linarith
  refine ⟨Quadratic.dedekindZeta_eq_mul K (by simpa using hs), ?_⟩

  let f : (Ideal (𝓞 K))⁰ → ℝ := fun I ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)
  have hf : ∀ I, 0 ≤ f I := fun I ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  let g : ClassGroup (𝓞 K) → ENNReal := fun C ↦
    ∑' I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰), ENNReal.ofReal (f I)
  have htot : ENNReal.ofReal (dedekindZetaReal K s) = ∑ C, g C :=
    (GroundTheory.Heights₂.Theta.projectiveLineClassData.ofReal_dedekindZetaReal K hs).trans
      (GroundTheory.Heights₂.Theta.projectiveLineClassData.tsum_ideal_eq_sum_class K hs0)
  have hg : ∀ C, g C ≠ ⊤ := fun C ↦ by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := dedekindZetaReal K s)) ?_
    rw [htot]
    exact Finset.single_le_sum (f := g) (fun _ _ ↦ zero_le) (Finset.mem_univ C)

  have hpz : ∀ C, partialZeta C s =
      ∑' I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰), f I := fun C ↦ by
    refine tsum_congr fun I ↦ ?_
    exact (Real.rpow_neg (Nat.cast_nonneg _) s).symm
  have hsum : ∀ C, Summable fun I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰) ↦ f I :=
    fun C ↦ by simpa [ENNReal.toReal_ofReal (hf _)] using ENNReal.summable_toReal (hg C)
  have hofr : ∀ C, ENNReal.ofReal (partialZeta C s) = g C := fun C ↦ by
    rw [hpz]
    exact ENNReal.ofReal_tsum_of_nonneg (f := fun I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰) ↦ f I)
      (fun I ↦ hf I) (hsum C)
  have hnn : ∀ C, 0 ≤ partialZeta C s := fun C ↦ by
    rw [hpz]
    exact tsum_nonneg fun I ↦ hf I
  have hreal : ∑ C : ClassGroup (𝓞 K), partialZeta C s = dedekindZetaReal K s := by
    have hζ : 0 ≤ dedekindZetaReal K s := tsum_nonneg fun n ↦ dedekindZetaTerm_nonneg K s n
    refine (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun C _ ↦ hnn C) hζ).1 ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun C _ ↦ hnn C), htot]
    exact Finset.sum_congr rfl (fun C _ ↦ hofr C)
  rw [dedekindZeta_ofReal K hs0.ne', ← hreal]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic
open scoped Real ModularForm UpperHalfPlane

theorem DeltaEta.proof : DeltaEta.Statement := by
  intro τ
  rw [latticeDiscr_lattice, discr_latticeOfTau]
  simp only [ModularForm.discriminant]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic MeasureTheory ZSpan
open scoped Real ModularForm UpperHalfPlane

noncomputable section

theorem latticeArea_latticeOfTau (τ : ℍ) : latticeArea (latticeOfTau τ).lattice = τ.im := by
  have hvol : volume.real (fundamentalDomain Complex.basisOneI) = 1 := by
    rw [← Complex.toBasis_orthonormalBasisOneI,
      measureReal_congr (fundamentalDomain_ae_parallelepiped _ volume)]
    rw [measureReal_def, OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
    simp
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ (latticeOfTau τ).latticeBasis
    Complex.basisOneI, hvol, mul_one, Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr, abs_of_pos τ.im_pos]

theorem PhTau.proof (hΔ : DeltaEta.Statement) : PhTau.Statement := by
  intro τ
  have hy : 0 < τ.im := τ.im_pos
  have hη : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero (z := (τ : ℂ)) τ.im_pos
  have hn : 0 < ‖η (τ : ℂ)‖ := norm_pos_iff.2 hη
  have h1 : ‖((2 * π : ℝ) : ℂ) ^ 12 * η (τ : ℂ) ^ 24‖ = ((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring
  have h6 : (1 / 6 : ℝ) * Real.log (((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6) =
      Real.log ((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) := by
    rw [Real.log_pow]; push_cast; ring
  unfold logPeriod
  rw [latticeArea_latticeOfTau, hΔ τ, h1, h6, ← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem mem_conjLattice_iff (Λ : Submodule ℤ ℂ) (z : ℂ) : z ∈ conjLattice Λ ↔ conj z ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨conj z, h, by simp⟩

theorem eisensteinSum_conjLattice (Λ : Submodule ℤ ℂ) (n : ℕ) :
    eisensteinSum (conjLattice Λ) n = conj (eisensteinSum Λ n) := by
  unfold eisensteinSum
  let e : Λ ≃ conjLattice Λ :=
    (Submodule.equivMapOfInjective _ (star_injective (R := ℂ)) Λ).toEquiv
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext l
  change ((conj (l : ℂ)) ^ n)⁻¹ = conj (((l : ℂ) ^ n)⁻¹)
  simp [map_inv₀, map_pow]

theorem latticeDiscr_conjLattice (Λ : Submodule ℤ ℂ) :
    latticeDiscr (conjLattice Λ) = conj (latticeDiscr Λ) := by
  simp [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_conjLattice, map_sub, map_mul, map_pow, map_ofNat]

theorem conjLattice_eq_comap (Λ : Submodule ℤ ℂ) :
    conjLattice Λ =
      ZLattice.comap ℝ Λ Complex.conjLIE.toLinearEquiv.toLinearMap := by
  ext z
  rw [mem_conjLattice_iff]
  exact Iff.rfl

theorem latticeArea_conjLattice (L : PeriodPair) :
    latticeArea (conjLattice L.lattice) = latticeArea L.lattice := by
  unfold latticeArea
  rw [conjLattice_eq_comap]
  exact ZLattice.covolume_comap L.lattice volume volume
    (e := Complex.conjLIE.toContinuousLinearEquiv) Complex.conjLIE.measurePreserving

theorem PhConj.proof : PhConj.Statement := by
  intro L
  unfold logPeriod
  rw [latticeArea_conjLattice, latticeDiscr_conjLattice, Complex.norm_conj]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

lemma kroneckerTerm_eq (τ : ℍ) {s : ℝ} (hs : 0 < s) (p : ℤ × ℤ) :
    (if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)) =
      τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s) := by
  split_ifs with h
  · subst h
    simp [Real.zero_rpow (mul_pos two_pos hs).ne']
  · rfl

lemma summable_kroneckerTerm (τ : ℍ) {s : ℝ} (hs : 1 < s) :
    Summable fun p : ℤ × ℤ ↦ τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s) := by
  have hk : 2 < 2 * s := by linarith
  have hy : 0 ≤ τ.im ^ s := Real.rpow_nonneg τ.im_pos.le _
  have h1 := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
    (τ.im ^ s * EisensteinSeries.r τ ^ (-(2 * s)))
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h1
  refine Summable.of_nonneg_of_le
    (fun p ↦ div_nonneg hy (Real.rpow_nonneg (norm_nonneg _) _)) (fun p ↦ ?_) h1
  have hb := EisensteinSeries.summand_bound τ (by linarith : (0 : ℝ) ≤ 2 * s)
    ((finTwoArrowEquiv ℤ).symm p)
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_apply] at hb ⊢
  rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left hb hy

lemma kroneckerTerm_eq_rpow (τ : ℍ) (s : ℝ) (m n : ℤ) :
    τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) =
      τ.im ^ s * (((n : ℝ) + m * τ.re) ^ 2 + (m * τ.im) ^ 2) ^ (-s) := by
  have h : ‖(m : ℂ) * τ + n‖ ^ 2 = ((n : ℝ) + m * τ.re) ^ 2 + (m * τ.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two, h, Real.rpow_neg (by positivity),
    div_eq_mul_inv]

lemma kroneckerTerm_neg (τ : ℍ) (s : ℝ) (m n : ℤ) :
    τ.im ^ s / ‖((-m : ℤ) : ℂ) * τ + ((-n : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) := by
  rw [show ((-m : ℤ) : ℂ) * τ + ((-n : ℤ) : ℂ) = -((m : ℂ) * τ + n) by push_cast; ring, norm_neg]

lemma tsum_int_split {f : ℤ → ℝ} (h : Summable f) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f (n + 1) + f 0 + ∑' n : ℕ, f (-(n + 1)) :=
  tsum_of_add_one_of_neg_add_one
    (h.comp_injective (show Function.Injective fun n : ℕ ↦ (n : ℤ) + 1 from
      fun a b h ↦ by simpa using h))
    (h.comp_injective (show Function.Injective fun n : ℕ ↦ -((n : ℤ) + 1) from
      fun a b h ↦ by simpa using h))

lemma kroneckerRow_zero (τ : ℍ) {s : ℝ} (hs : 0 < s)
    (h : Summable fun n : ℤ ↦ τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s)) :
    ∑' n : ℤ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      2 * τ.im ^ s * ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s)) := by
  rw [tsum_int_split h]
  have e1 : ∀ n : ℕ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s * (1 / ((n + 1 : ℝ) ^ (2 * s))) := by
    intro n
    have : ‖((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ)‖ = (n : ℝ) + 1 := by
      rw [show ((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [this, mul_one_div]
  have e2 : ∀ n : ℕ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + ((-((n : ℤ) + 1) : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s * (1 / ((n + 1 : ℝ) ^ (2 * s))) := by
    intro n
    rw [← e1 n]
    simpa using kroneckerTerm_neg τ s 0 ((n : ℤ) + 1)
  have e0 : τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ)‖ ^ (2 * s) = 0 := by
    simp [Real.zero_rpow (mul_pos two_pos hs).ne']
  simp only [e1, e2, e0, add_zero, tsum_mul_left]
  ring

lemma kroneckerRow_neg (τ : ℍ) (s : ℝ) (m : ℤ) :
    ∑' n : ℤ, τ.im ^ s / ‖((-m : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      ∑' n : ℤ, τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) := by
  rw [← tsum_comp_neg]
  exact tsum_congr fun n ↦ kroneckerTerm_neg τ s m n

theorem KroneckerSplit.proof : KroneckerSplit.Statement := by
  intro τ s hs
  have hs0 : 0 < s := by linarith
  have hsum := summable_kroneckerTerm τ hs
  have hcol : Summable fun m : ℤ ↦ ∑' n : ℤ, τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) :=
    hsum.prod
  rw [kroneckerSum, tsum_congr (kroneckerTerm_eq τ hs0), hsum.tsum_prod, tsum_int_split hcol]
  have hrow0 : Summable fun n : ℤ ↦ τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) :=
    hsum.prod_factor 0
  simp only [kroneckerRow_neg, kroneckerRow_zero τ hs0 hrow0]
  have e : ∀ m : ℕ, ∑' n : ℤ, τ.im ^ s / ‖(((m : ℤ) + 1 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      τ.im ^ s * ∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s) := by
    intro m
    rw [← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [kroneckerTerm_eq_rpow]
    push_cast
    rfl
  simp only [e]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory Set Real

noncomputable section

theorem PowerIntegral.integral_rpow_mul_exp_neg_mul {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-(c * u)) = c ^ (-s) * Gamma s := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s - 1) (b := c) one_pos
    (by linarith) hc
  have e1 : (-(s - 1 + 1) / 1 : ℝ) = -s := by ring
  have e2 : ((s - 1 + 1) / 1 : ℝ) = s := by ring
  rw [e1, e2, one_div_one, mul_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  simp only [rpow_one, neg_mul]

theorem PowerIntegral.integrand_split (a s u t : ℝ) :
    u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) =
      (u ^ (s - 1) * exp (-(a ^ 2 * u))) * exp (-u * t ^ 2) := by
  rw [mul_assoc, ← exp_add]
  ring_nf

theorem PowerIntegral.proof : PowerIntegral.Statement := by
  intro a s ha hs
  have hs0 : 0 < s := by linarith
  have hΓ : Gamma s ≠ 0 := (Gamma_pos_of_pos hs0).ne'
  have h1 : ∀ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s) =
      (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) := by
    intro t
    rw [PowerIntegral.integral_rpow_mul_exp_neg_mul (by positivity) hs0,
      mul_comm ((t ^ 2 + a ^ 2) ^ (-s)), ← mul_assoc, inv_mul_cancel₀ hΓ, one_mul]
  have h2 : ∀ u ∈ Ioi (0 : ℝ), ∫ t : ℝ, u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) =
      √π * (u ^ (s - 3 / 2) * exp (-(a ^ 2 * u))) := by
    intro u hu
    have hu : 0 < u := hu
    simp_rw [PowerIntegral.integrand_split a s u]
    rw [integral_const_mul, integral_gaussian, sqrt_div pi_pos.le]
    have e : u ^ (s - 3 / 2) = u ^ (s - 1) / √u := by
      rw [sqrt_eq_rpow, ← rpow_sub hu]
      congr 1
      ring
    have hsu : 0 < √u := sqrt_pos.mpr hu
    rw [e]
    field_simp
  have hmeas : Measurable
      (Function.uncurry fun t u : ℝ => u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u))) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable
      (Function.uncurry fun t u : ℝ => u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu : 0 < u := hu
      simp only [Function.uncurry_apply_pair]
      simp_rw [PowerIntegral.integrand_split a s u]
      exact (integrable_exp_neg_mul_sq hu).const_mul _
    · have hq : (-1 : ℝ) < s - 3 / 2 := by linarith
      have hI := (integrableOn_rpow_mul_exp_neg_mul_rpow hq one_pos (pow_pos ha 2)).const_mul √π
      refine IntegrableOn.congr_fun hI (fun u hu => ?_) measurableSet_Ioi
      have hu : 0 < u := hu
      simp only [Function.uncurry_apply_pair]
      simp only [rpow_one, neg_mul]
      rw [← h2 u hu]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      exact (norm_of_nonneg (mul_nonneg (rpow_nonneg hu.le _) (exp_pos _).le)).symm
  have hpow : (a ^ 2) ^ (-(s - 1 / 2)) = a ^ (1 - 2 * s) := by
    rw [← rpow_natCast, ← rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have hs' : 0 < s - 1 / 2 := by linarith
  calc ∫ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s)
      = ∫ t : ℝ, (Gamma s)⁻¹ *
          ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) :=
        integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ t : ℝ,
          u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) := by
        rw [integral_const_mul, integral_integral_swap hint]
    _ = (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), √π * (u ^ (s - 3 / 2) * exp (-(a ^ 2 * u))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi h2]
    _ = (Gamma s)⁻¹ * (√π * ((a ^ 2) ^ (-(s - 1 / 2)) * Gamma (s - 1 / 2))) := by
        rw [integral_const_mul, show s - 3 / 2 = (s - 1 / 2) - 1 by ring,
          PowerIntegral.integral_rpow_mul_exp_neg_mul (pow_pos ha 2) hs']
    _ = √π * Gamma (s - 1 / 2) / Gamma s * a ^ (1 - 2 * s) := by
        rw [hpow]
        field_simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory Set Filter

noncomputable section

namespace ShiftedSumIntegral

theorem half_line {G : ℝ → ℝ} (anti : AntitoneOn G (Ici 0)) (hint : Integrable G)
    (nonneg : ∀ x, 0 ≤ G x) {w : ℝ} (hw : 0 ≤ w) :
    Summable (fun k : ℕ ↦ G (k + w)) ∧ ∫ x in Ioi w, G x ≤ ∑' k : ℕ, G (k + w) ∧
      ∑' k : ℕ, G (k + w) ≤ G w + ∫ x in Ioi w, G x := by
  have hshift : ∫ x in Ioi 0, G (x + w) = ∫ x in Ioi w, G x := by
    have A : MeasurableEmbedding fun x : ℝ ↦ x + w :=
      (Homeomorph.addRight w).isClosedEmbedding.measurableEmbedding
    have := A.setIntegral_map (μ := volume) G (Ioi w)
    rw [map_add_right_eq_self] at this
    rw [this]
    simp
  have anti' : AntitoneOn (fun x ↦ G (x + w)) (Ici 0) := fun x hx y hy hxy ↦
    anti (mem_Ici.2 (by linarith [mem_Ici.1 hx])) (mem_Ici.2 (by linarith [mem_Ici.1 hy]))
      (by linarith)
  have int' : IntegrableOn (fun x ↦ G (x + w)) (Ioi 0) := (hint.comp_add_right w).integrableOn
  have sm := anti'.summable_of_integrableOn_Ioi_zero int' (fun x _ ↦ nonneg _)
  refine ⟨sm, ?_, ?_⟩
  · rw [← hshift]
    exact anti'.integral_le_tsum sm (fun x _ ↦ nonneg _)
  · rw [← hshift]
    simpa using anti'.tsum_le_integral int' (fun x _ ↦ nonneg _)

theorem proof : ShiftedSumIntegral.Statement := by
  intro a u s ha hs
  set G : ℝ → ℝ := fun x ↦ (x ^ 2 + a ^ 2) ^ (-s) with hGdef
  show Summable (fun n : ℤ ↦ G (n + u)) ∧ |∑' n : ℤ, G (n + u) - ∫ t, G t| ≤ a ^ (-2 * s)
  have hpos : ∀ x, 0 < x ^ 2 + a ^ 2 := fun x ↦ by positivity
  have nonneg : ∀ x, 0 ≤ G x := fun x ↦ Real.rpow_nonneg (hpos x).le _
  have cont : Continuous G :=
    (by fun_prop : Continuous fun x : ℝ ↦ x ^ 2 + a ^ 2).rpow_const fun x ↦ Or.inl (hpos x).ne'
  have anti : AntitoneOn G (Ici 0) := fun x hx y hy hxy ↦
    Real.rpow_le_rpow_of_nonpos (hpos x) (by nlinarith [mem_Ici.1 hx]) (by linarith)
  have even : ∀ x, G (-x) = G x := fun x ↦ by simp only [hGdef, neg_sq]
  have hG0 : G 0 = a ^ (-2 * s) := by
    show ((0 : ℝ) ^ 2 + a ^ 2) ^ (-s) = a ^ (-2 * s)
    rw [show (0 : ℝ) ^ 2 + a ^ 2 = a ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
      ← Real.rpow_mul ha.le]
    ring_nf
  have hint : Integrable G := by
    have hm : 0 < min 1 (a ^ 2) := lt_min one_pos (by positivity)
    refine ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)).const_mul (min 1 (a ^ 2) ^ (-s))).mono' cont.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (nonneg t), Real.norm_eq_abs, sq_abs,
      show -(2 * s) / 2 = -s by ring, ← Real.mul_rpow hm.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith [min_le_left 1 (a ^ 2), min_le_right 1 (a ^ 2),
        mul_le_mul_of_nonneg_right (min_le_left 1 (a ^ 2)) (sq_nonneg t)]) (by linarith)
  have hJ : ∫ t, G t = 2 * ∫ x in Ioi 0, G x := by
    rw [← integral_comp_abs (f := G)]
    congr 1
    ext x
    simp only [hGdef, sq_abs]
  have hseg : ∀ y, 0 ≤ y → y * G y ≤ ∫ x in (0 : ℝ)..y, G x ∧ ∫ x in (0 : ℝ)..y, G x ≤ y * G 0 := by
    intro y hy
    constructor
    · have := intervalIntegral.integral_mono_on hy (intervalIntegrable_const (μ := volume))
        (cont.intervalIntegrable 0 y) (fun x hx ↦ anti (mem_Ici.2 hx.1) (mem_Ici.2 hy) hx.2)
      simpa using this
    · have := intervalIntegral.integral_mono_on hy (cont.intervalIntegrable 0 y)
        (intervalIntegrable_const (μ := volume)) (fun x hx ↦ anti (mem_Ici.2 le_rfl) (mem_Ici.2 hx.1) hx.1)
      simpa using this
  have htail : ∀ y, 0 ≤ y → ∫ x in Ioi y, G x = (∫ x in Ioi 0, G x) - ∫ x in (0 : ℝ)..y, G x :=
    fun y hy ↦ by
      have e : (∫ x in Ioi 0, G x) - (∫ x in Ioi y, G x) = ∫ x in (0 : ℝ)..y, G x :=
        intervalIntegral.integral_Ioi_sub_Ioi hint.integrableOn hy
      linarith

  have core : ∀ w : ℝ, 0 ≤ w → w < 1 →
      Summable (fun m : ℤ ↦ G (m + w)) ∧ |∑' m : ℤ, G (m + w) - ∫ t, G t| ≤ G 0 := by
    intro w hw0 hw1
    obtain ⟨sP, lP, uP⟩ := half_line anti hint nonneg hw0
    obtain ⟨sQ, lQ, uQ⟩ := half_line anti hint nonneg (by linarith : 0 ≤ 1 - w)
    have hneg : ∀ n : ℕ, G (((-((n : ℤ) + 1) : ℤ) : ℝ) + w) = G (n + (1 - w)) := fun n ↦ by
      rw [← even]; congr 1; push_cast; ring
    have sQ' : Summable (fun n : ℕ ↦ G (((-((n : ℤ) + 1) : ℤ) : ℝ) + w)) := by
      convert sQ using 1; funext n; exact hneg n
    have hT : ∑' m : ℤ, G (m + w) = ∑' k : ℕ, G (k + w) + ∑' k : ℕ, G (k + (1 - w)) := by
      rw [tsum_of_nat_of_neg_add_one (f := fun m : ℤ ↦ G (m + w)) (by exact_mod_cast sP) sQ']
      push_cast
      congr 1
      exact tsum_congr fun n ↦ by rw [← hneg n]; push_cast; ring_nf
    refine ⟨Summable.of_nat_of_neg_add_one (by exact_mod_cast sP) sQ', ?_⟩
    obtain ⟨lw, uw⟩ := hseg w hw0
    obtain ⟨lv, uv⟩ := hseg (1 - w) (by linarith)
    rw [htail w hw0] at lP uP
    rw [htail (1 - w) (by linarith)] at lQ uQ
    have gw : G w ≤ G 0 := anti (mem_Ici.2 le_rfl) (mem_Ici.2 hw0) hw0
    have gv : G (1 - w) ≤ G 0 := anti (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith)) (by linarith)
    have h1 : G w * (1 - w) ≤ G 0 * (1 - w) := mul_le_mul_of_nonneg_right gw (by linarith)
    have h2 : G (1 - w) * w ≤ G 0 * w := mul_le_mul_of_nonneg_right gv hw0
    rw [hT, hJ, abs_le]
    constructor
    · linarith
    · linarith
  have key : ∀ n : ℤ, G (n + u) =
      (fun m : ℤ ↦ G (m + Int.fract u)) (Equiv.addRight ⌊u⌋ n) := fun n ↦ by
    simp only [Equiv.coe_addRight, Int.cast_add]
    rw [add_assoc, Int.floor_add_fract]
  obtain ⟨hs', hb⟩ := core (Int.fract u) (Int.fract_nonneg u) (Int.fract_lt_one u)
  rw [← hG0]
  refine ⟨?_, ?_⟩
  · rw [show (fun n : ℤ ↦ G (n + u)) = _ from funext key]
    exact (Equiv.addRight ⌊u⌋).summable_iff.2 hs'
  · rw [tsum_congr key, (Equiv.addRight ⌊u⌋).tsum_eq (fun m : ℤ ↦ G (m + Int.fract u))]
    exact hb

end ShiftedSumIntegral

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Complex ComplexConjugate
open scoped Real

theorem CotangentSum.pair_identity (w w' N : ℂ) (h1 : w + N ≠ 0) (h2 : w - N ≠ 0)
    (h3 : w' + N ≠ 0) (h4 : w' - N ≠ 0) (h5 : w - w' ≠ 0) :
    ((w + N) * (w' + N))⁻¹ + ((w - N) * (w' - N))⁻¹ =
      (w - w')⁻¹ * ((1 / (w' - N) + 1 / (w' + N)) - (1 / (w - N) + 1 / (w + N))) := by
  field_simp
  ring

theorem CotangentSum.proof : CotangentSum.Statement := by
  intro a u ha
  have hne : ∀ x : ℂ, x.im ≠ 0 → x ≠ 0 := fun x hx h => hx (by simp [h])
  have hmem : ∀ x : ℂ, x.im ≠ 0 → x ∈ Complex.integerComplement := by
    rintro x hx ⟨n, hn⟩
    apply hx
    rw [← hn]
    simp
  have ha0 : (a : ℝ) ≠ 0 := ha.ne'
  set w : ℂ := (u : ℂ) + (a : ℂ) * I with hw
  set w' : ℂ := (u : ℂ) - (a : ℂ) * I with hw'
  have hwim : w.im = a := by simp [hw]
  have hw'im : w'.im = -a := by simp [hw']
  have hconj : conj w = w' := by
    rw [hw, hw', map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
    ring
  have hdiff : w - w' = 2 * (a : ℂ) * I := by rw [hw, hw']; ring
  have hdiff0 : w - w' ≠ 0 := by
    rw [hdiff]; exact mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr ha0)) I_ne_zero

  let F : ℤ → ℂ := fun n => ((w + n) * (w' + n))⁻¹
  have hF : ∀ n : ℤ, ((((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) : ℝ) = F n := by
    intro n
    have e : (w + n) * (w' + n) = ((n : ℂ) + u) ^ 2 + (a : ℂ) ^ 2 := by
      rw [hw, hw']
      linear_combination (-(a : ℂ) ^ 2) * I_sq
    simp only [F, e, Real.rpow_neg_one]
    push_cast
    rfl
  have hsum : Summable F := by
    have h := (EisensteinSeries.linear_inv_isBigO_right 1 w').mul
      (EisensteinSeries.linear_inv_isBigO_right 1 w)
    refine EisensteinSeries.summable_inv_of_isBigO_rpow_inv (f := fun n : ℤ => (w + n) * (w' + n))
      (a := 2) (by norm_num) ?_
    simpa [pow_two, mul_inv] using! h

  have h1 := tsum_nat_add_neg hsum
  have h2 := (hsum.nat_add_neg).tsum_eq_zero_add
  have hterm : ∀ n : ℕ, F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ)) =
      (w - w')⁻¹ * (cotTerm w' n - cotTerm w n) := by
    intro n
    have hN : ∀ x : ℂ, x.im ≠ 0 → x + ((n : ℂ) + 1) ≠ 0 ∧ x - ((n : ℂ) + 1) ≠ 0 := by
      intro x hx
      refine ⟨hne _ ?_, hne _ ?_⟩ <;> simpa using hx
    have := CotangentSum.pair_identity w w' ((n : ℂ) + 1)
      (hN w (by rw [hwim]; exact ha0)).1 (hN w (by rw [hwim]; exact ha0)).2
      (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).1
      (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).2 hdiff0
    simp only [F, cotTerm]
    push_cast
    simp only [← sub_eq_add_neg]
    rw [← this]
  have hw_mem : w ∈ Complex.integerComplement := hmem w (by rw [hwim]; exact ha0)
  have hw'_mem : w' ∈ Complex.integerComplement :=
    hmem w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)
  have h3 : ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ))) =
      (w - w')⁻¹ * ((π * cot (π * w') - 1 / w') - (π * cot (π * w) - 1 / w)) := by
    rw [tsum_congr hterm, tsum_mul_left,
      Summable.tsum_sub (summable_cotTerm hw'_mem) (summable_cotTerm hw_mem),
      cot_series_rep' hw'_mem, cot_series_rep' hw_mem]
  have hF0 : F 0 = (w - w')⁻¹ * (1 / w' - 1 / w) := by
    simp only [F, Int.cast_zero, add_zero]
    have := hne w (by rw [hwim]; exact ha0)
    have := hne w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)
    field_simp
  have hS : ∑' n : ℤ, F n = (w - w')⁻¹ * (π * cot (π * w') - π * cot (π * w)) := by
    have h2' : ∑' n : ℕ, (F n + F (-n)) =
        (F 0 + F 0) + ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ))) := by
      rw [h2]; simp
    rw [h2', h3] at h1
    rw [hF0] at h1
    linear_combination -h1

  have hwH : 0 < w.im := by rw [hwim]; exact ha
  have hq := pi_mul_cot_pi_q_exp ⟨w, hwH⟩
  simp only at hq
  set q : ℂ := Complex.exp (2 * π * I * w) with hqdef
  have hqn : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w, hwH⟩
  have hgeo : ∑' n : ℕ, q ^ n = 1 + ∑' k : ℕ, q ^ (k + 1) := by
    rw [(summable_geometric_of_norm_lt_one hqn).tsum_eq_zero_add]; simp
  set T : ℂ := ∑' k : ℕ, q ^ (k + 1) with hT
  have hcot' : π * cot (π * w') = conj (π * cot (π * w)) := by
    rw [map_mul, conj_ofReal, ← cot_conj, map_mul, conj_ofReal, hconj]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, tsum_congr hF, hS, hcot', hq, hgeo]
  have hTc : T + conj T = 2 * (T.re : ℂ) := by rw [Complex.add_conj]; push_cast; ring
  simp only [map_sub, map_mul, map_add, conj_ofReal, conj_I, map_one, map_ofNat]
  rw [hdiff]
  have hI : I ≠ 0 := I_ne_zero
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha0
  push_cast
  field_simp
  linear_combination 2 * hTc
end ChowlaSelberg
end Heights
end Heights₂
end GroundTheory
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology Complex
open scoped Real UpperHalfPlane ModularForm

noncomputable section

theorem LogEta.proof : LogEta.Statement := by
  intro τ
  set q : ℂ := Complex.exp (2 * π * Complex.I * (τ : ℂ)) with hq
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hpow : ∀ k : ℕ, ‖q ^ (k + 1)‖ < 1 := fun k ↦ by
    rw [norm_pow]; exact pow_lt_one₀ hr0 hq1 (Nat.succ_ne_zero k)

  let F : ℕ × ℕ → ℂ := fun p ↦ ((1 / (p.1 + 1 : ℝ) : ℝ) : ℂ) * q ^ ((p.1 + 1) * (p.2 + 1))
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ ↦ ‖q‖ ^ p.1 * ‖q‖ ^ p.2)
      (Summable.mul_of_nonneg (summable_geometric_of_lt_one hr0 hq1)
        (summable_geometric_of_lt_one hr0 hq1) (fun _ ↦ pow_nonneg hr0 _)
        (fun _ ↦ pow_nonneg hr0 _)) ?_
    rintro ⟨m, k⟩
    simp only [F, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [← pow_add]
    have h1 : |1 / ((m : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      exact div_le_one_of_le₀ (by linarith [m.cast_nonneg (α := ℝ)]) (by positivity)
    have h2 : ‖q‖ ^ ((m + 1) * (k + 1)) ≤ ‖q‖ ^ (m + k) :=
      pow_le_pow_of_le_one hr0 hq1.le (by nlinarith)
    calc _ ≤ 1 * ‖q‖ ^ (m + k) := mul_le_mul h1 h2 (pow_nonneg hr0 _) zero_le_one
      _ = _ := one_mul _
  set T := ∑' p, F p

  have hA : HasSum (fun m : ℕ ↦ ∑' k : ℕ, F (m, k)) T :=
    hFs.hasSum.prod_fiberwise fun m ↦ (hFs.prod_factor m).hasSum

  have hcol : ∀ k : ℕ, HasSum (fun m : ℕ ↦ F (m, k)) (-Complex.log (1 - q ^ (k + 1))) := by
    intro k
    convert hasSum_taylorSeries_neg_log' (hpow k) using 1
    ext m
    simp only [F]
    rw [← pow_mul, mul_comm (k + 1)]
    push_cast
    ring
  have hB : HasSum (fun k : ℕ ↦ -Complex.log (1 - q ^ (k + 1))) T := by
    have hsw : HasSum (F ∘ Prod.swap) T :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hFs.hasSum
    exact hsw.prod_fiberwise fun k ↦ hcol k

  have hne : ∀ k : ℕ, 1 - q ^ (k + 1) ≠ 0 := fun k ↦
    sub_ne_zero.mpr (ne_of_apply_ne norm (by rw [norm_one]; exact (hpow k).ne)).symm
  have hlog : HasSum (fun k : ℕ ↦ Real.log ‖1 - q ^ (k + 1)‖) (-T.re) := by
    have := (Complex.hasSum_re hB).neg
    simpa only [neg_re, Complex.log_re, neg_neg] using this
  have hprod : HasProd (fun k : ℕ ↦ ‖1 - q ^ (k + 1)‖) (Real.exp (-T.re)) := by
    convert hlog.rexp using 1
    ext k
    simp only [Function.comp_apply]
    rw [Real.exp_log (norm_pos_iff.mpr (hne k))]
  have hnorm : ‖∏' k : ℕ, (1 - q ^ (k + 1))‖ = Real.exp (-T.re) :=
    (ModularForm.multipliable_one_sub_pow hq1).hasProd.norm.unique hprod
  have heta : ‖η (τ : ℂ)‖ = Real.exp (-2 * π * (τ : ℂ).im / 24) * Real.exp (-T.re) := by
    rw [ModularForm.eta, norm_mul, Function.Periodic.norm_qParam, ← hnorm]
    congr 2
    refine tprod_congr fun n ↦ ?_
    rw [ModularForm.eta_q_eq_pow]
  have hlogeta : Real.log ‖η (τ : ℂ)‖ = -2 * π * τ.im / 24 - T.re := by
    rw [heta, ← Real.exp_add, Real.log_exp, UpperHalfPlane.coe_im]
    ring
  rw [hlogeta]
  convert Complex.hasSum_re hA using 1
  · ext m
    simp only [F]
    rw [tsum_mul_left, re_ofReal_mul]
  · ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real

noncomputable section

theorem tendsto_tsum_one_div_rpow_sub_one_div :
    Tendsto (fun w : ℝ ↦ (∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ w)) - 1 / (w - 1)) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
  have h := (Complex.continuous_re.tendsto _).comp
    ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : (1 : ℝ) < w := hw
  simp only [Function.comp_apply]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hw')]
  have : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (w : ℂ)) = ((∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ w) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1 with n
    rw [Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring
  rw [this]
  have h1 : ((1 : ℂ) / ((w : ℂ) - 1)) = (((1 : ℝ) / (w - 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_sub, Complex.ofReal_re]

theorem GammaZetaLimit.proof : GammaZetaLimit.Statement := by
  intro y hy
  set F : ℝ → ℝ := fun s ↦ √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * y ^ (1 - s) with hF
  have hs2 : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have h12 : Real.Gamma (1 - 1 / 2) = √π := by norm_num [Real.Gamma_one_half_eq]

  have hG12 : HasDerivAt (fun s : ℝ ↦ Real.Gamma (s - 1 / 2))
      (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2)) 1 := by
    have h : HasDerivAt Real.Gamma (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2))
        ((1 : ℝ) - 1 / 2) := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      exact Real.hasDerivAt_Gamma_one_half
    exact h.comp_sub_const 1 (1 / 2)
  have hY : HasDerivAt (fun s : ℝ ↦ y ^ (1 - s)) (-Real.log y) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 1).const_rpow hy
  have hΓ1 : Real.Gamma 1 ≠ 0 := by simp
  have hFd : HasDerivAt F (-2 * π * Real.log 2 - π * Real.log y) 1 := by
    have h := ((hG12.div Real.hasDerivAt_Gamma_one hΓ1).const_mul √π).mul hY
    have e1 : ((fun t : ℝ ↦ √π * ((fun s : ℝ ↦ Real.Gamma (s - 1 / 2)) / Real.Gamma) t) *
        fun s : ℝ ↦ y ^ (1 - s)) = F := by
      funext s
      simp only [hF, Pi.mul_apply, Pi.div_apply]
      ring
    rw [e1] at h
    refine h.congr_deriv ?_
    simp only [h12, Real.Gamma_one, Pi.div_apply, one_pow, div_one, mul_one, sub_self,
      Real.rpow_zero]
    linear_combination (-(2 * Real.log 2 + Real.log y)) * hs2
  have hF1 : F 1 = π := by
    simp only [hF, h12, Real.Gamma_one, sub_self, Real.rpow_zero, div_one, mul_one]
    exact hs2

  have hslope : Tendsto (fun s ↦ (F s - π) / (s - 1)) (𝓝[>] 1)
      (𝓝 (-2 * π * Real.log 2 - π * Real.log y)) := by
    have := (hasDerivAt_iff_tendsto_slope.mp hFd).mono_left
      (nhdsWithin_mono _ (fun x (hx : (1 : ℝ) < x) ↦ hx.ne'))
    refine this.congr' (Eventually.of_forall fun s ↦ ?_)
    rw [slope_def_field, hF1]
  have hFc : Tendsto F (𝓝[>] 1) (𝓝 π) :=
    hF1 ▸ hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝 1) (𝓝 (2 * 1 - 1)) :=
        ((continuous_const.mul continuous_id).sub continuous_const).tendsto 1
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : (1 : ℝ) < s)
      show (1 : ℝ) < 2 * s - 1
      linarith
  have hZ := tendsto_tsum_one_div_rpow_sub_one_div.comp hmap
  have hlim := hslope.add ((hFc.const_mul 2).mul hZ)
  have hval : -2 * π * Real.log 2 - π * Real.log y + 2 * π * Real.eulerMascheroniConstant =
      2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : (1 : ℝ) < s)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  have key : ∀ A Z : ℝ, (A - π) / (s - 1) + 2 * A * (Z - 1 / (2 * s - 1 - 1)) =
      2 * A * Z - π / (s - 1) := by
    intro A Z
    rw [show 2 * s - 1 - 1 = 2 * (s - 1) by ring]
    field_simp
    ring
  simp only [Function.comp_apply]
  rw [key]
  simp only [hF]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem ClassMeanOverEmbeddings.proof (S : PrimeDiscriminant K) (F : CMFamily K)
    (hMean : MeanOverEmbeddings.Statement S F) (hScale : PhScale.Statement)
    (hConj : PhConj.Statement) : ClassMeanOverEmbeddings.Statement S F := by
  intro σ
  have := S.isTotallyComplex
  have hK := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

  have hhom : ∀ (τ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : Submodule ℤ ℂ) (c : ℂ),
      c ≠ 0 → (Λ : Set ℂ) = (c * ·) '' idealLattice τ J →
        logPeriod Λ = logPeriod (idealLattice τ J) := by
    intro τ J Λ c hc h
    have e : Λ = scaleLattice c (idealPeriodPair τ hK J).lattice := by
      apply SetLike.coe_injective
      rw [h, scaleLattice, Submodule.map_coe, lattice_idealPeriodPair]
      rfl
    rw [e, hScale _ c hc, lattice_idealPeriodPair]

  have hcls : ∀ (τ : K →+* ℂ) (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
      logPeriod (idealLattice τ 𝔟) = classLogPeriod τ (ClassGroup.mk K 𝔟) := by
    intro τ 𝔟
    have hJ : ClassGroup.mk K 𝔟 =
        ClassGroup.mk K (FractionalIdeal.mk0 K (classRep (ClassGroup.mk K 𝔟))) := by
      rw [ClassGroup.mk_mk0, mk0_classGroupRep]
    obtain ⟨c, hc, h⟩ := (classGroup_mk_eq_iff τ hK _ _).1 hJ
    rw [classLogPeriod, classLattice, ← FractionalIdeal.coe_mk0, hhom τ 𝔟 _ c hc h]

  have hconj : ∀ τ : K →+* ℂ, classMean τ = classMean σ := by
    intro τ
    rcases S.eq_or_eq_conjugate σ τ with rfl | rfl
    · rfl
    · unfold classMean
      congr 1
      refine Finset.sum_congr rfl fun C _ ↦ ?_
      rw [classLogPeriod, classLogPeriod, classLattice, classLattice, idealLattice_conjugate,
        ← FractionalIdeal.coe_mk0, ← lattice_idealPeriodPair σ hK, hConj]

  have hs : ∀ s : F.k →+* ℂ, (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K),
      logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
        F.periodLattice s) = classMean σ := by
    intro s
    obtain ⟨I, c, hc, h⟩ := F.exists_periodLattice_eq S s
    have e : ∀ C : ClassGroup (𝓞 K),
        logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
          F.periodLattice s) = classLogPeriod (F.restrict s) (C * ClassGroup.mk K I) := by
      intro C
      have h' := idealLattice_mul_homothetic (F.restrict s) (I : FractionalIdeal (𝓞 K)⁰ K)
        (↑(FractionalIdeal.mk0 K (classRep C))) h
      rw [← Units.val_mul] at h'
      rw [hhom _ _ _ c hc h', hcls, map_mul, ClassGroup.mk_mk0, mk0_classGroupRep]
    rw [Finset.sum_congr rfl fun C _ ↦ e C,
      Fintype.sum_equiv (Equiv.mulRight (ClassGroup.mk K I))
        (fun C ↦ classLogPeriod (F.restrict s) (C * ClassGroup.mk K I)) (classLogPeriod (F.restrict s))
        (fun C ↦ rfl)]
    exact hconj _
  have hN : (Fintype.card (F.k →+* ℂ) : ℝ) ≠ 0 := by
    have : Nonempty (F.k →+* ℂ) := ⟨(IsAlgClosed.lift : F.k →ₐ[ℚ] ℂ).toRingHom⟩
    exact_mod_cast Fintype.card_ne_zero
  have hh : (classNumber K : ℝ) ≠ 0 := by exact_mod_cast classNumber_ne_zero K

  calc embMean F.k (fun s ↦ logPeriod (F.periodLattice s))
      = (classNumber K : ℝ)⁻¹ * ∑ _C : ClassGroup (𝓞 K),
          embMean F.k (fun s ↦ logPeriod (F.periodLattice s)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact (inv_mul_cancel_left₀ hh _).symm
    _ = (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K), embMean F.k (fun s ↦
          logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
            F.periodLattice s)) := by
        congr 1
        exact Finset.sum_congr rfl fun C _ ↦ (hMean _).symm
    _ = embMean F.k (fun s ↦ (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K),
          logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
            F.periodLattice s)) := by
        simp only [embMean, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = classMean σ := by
        simp only [hs, embMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

namespace WCocycle

theorem eisensteinSum_scaleLattice {c : ℂ} (hc : c ≠ 0) (N : Submodule ℤ ℂ) (n : ℕ) :
    eisensteinSum (scaleLattice c N) n = (c ^ n)⁻¹ * eisensteinSum N n := by
  have hinj : Function.Injective (LinearMap.mulLeft ℤ c) := fun x y h ↦
    mul_left_cancel₀ hc (by simpa using h)
  let e := Submodule.equivMapOfInjective (LinearMap.mulLeft ℤ c) hinj N
  rw [eisensteinSum, eisensteinSum, ← tsum_mul_left, scaleLattice, ← e.tsum_eq]
  congr 1
  ext x
  show ((c * (x : ℂ)) ^ n)⁻¹ = _
  rw [mul_pow, mul_inv]

theorem latticeDiscr_scaleLattice {c : ℂ} (hc : c ≠ 0) (N : Submodule ℤ ℂ) :
    latticeDiscr (scaleLattice c N) = (c ^ 12)⁻¹ * latticeDiscr N := by
  simp only [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_scaleLattice hc]
  field_simp

theorem mul_scaleLattice (c : ℂ) (M N : Submodule ℤ ℂ) :
    M * scaleLattice c N = scaleLattice c (M * N) := by
  apply le_antisymm
  · refine Submodule.mul_le.2 fun m hm n hn ↦ ?_
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
    refine Submodule.mem_map.2 ⟨m * y, Submodule.mul_mem_mul hm hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    ring
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun m hm y hy ↦ ?_)
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply,
      show c * (m * y) = m * (c * y) by ring]
    exact Submodule.mul_mem_mul hm (Submodule.mem_map.2 ⟨y, hy, rfl⟩)

theorem latticeDiscr_idealLattice_mul_ne_zero (S : PrimeDiscriminant K) (σ : K →+* ℂ)
    (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    latticeDiscr (idealLattice σ ↑𝔟 * L.lattice) ≠ 0 := by
  have := S.isTotallyComplex
  have hK := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨I, c, hc, hLI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have hLc : L.lattice = scaleLattice c (idealLattice σ ↑I) := by
    apply SetLike.coe_injective
    rw [hLI, scaleLattice, Submodule.map_coe]
    rfl
  rw [hLc, mul_scaleLattice, latticeDiscr_scaleLattice hc, ← idealLattice_mul, ← Units.val_mul,
    ← lattice_idealPeriodPair σ hK, latticeDiscr_lattice]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc)) (discr_ne_zero _)

theorem full (S : PrimeDiscriminant K) : WCocycle.Statement S := by
  intro σ L hL 𝔞 𝔭
  have hΛ : idealLattice σ ↑(𝔞 * 𝔭)⁻¹ * L.lattice =
      idealLattice σ ↑𝔭⁻¹ * (idealLattice σ ↑𝔞⁻¹ * L.lattice) := by
    rw [mul_inv, Units.val_mul, idealLattice_mul, mul_comm (idealLattice σ ↑𝔞⁻¹), mul_assoc]
  have h0 : latticeDiscr L.lattice ≠ 0 := by
    rw [latticeDiscr_lattice]; exact discr_ne_zero L
  have h1 := latticeDiscr_idealLattice_mul_ne_zero S σ L hL 𝔞⁻¹
  simp only [discrRatio, hΛ]
  field_simp

end WCocycle

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

theorem DeltaRatioIntegral.proof (hA : SuperlatticeRatio.Statement)
    (hI : HeckeRatioInvariant.Statement) (hE : HeckeRatioExpansion.Statement)
    (hQ : LevelOneQExpansion.Statement) : DeltaRatioIntegral.Statement := by
  intro L L' p hp hle hidx
  obtain ⟨τ, hj, hmem⟩ := hA L L' p hp hle hidx
  set M := heckeRatios ⟨p, hp.pos⟩ τ with hM
  set R := Algebra.adjoin ℤ {(weierstrassCurve L).j}
  have hes : ∀ k, M.esymm k ∈ R := by
    intro k
    obtain ⟨hd, hx⟩ := hE p hp k
    obtain ⟨Q, hQk⟩ := hQ _ hd (fun γ τ' ↦ congrArg (fun m : Multiset ℂ ↦ m.esymm k) (hI p hp γ τ')) hx
    rw [hM, hQk τ, ← hj]
    exact Polynomial.aeval_mem_adjoin_singleton ℤ _
  set P : ℂ[X] := (M.map fun t ↦ X - C t).prod with hP
  have hmon : P.Monic := monic_multiset_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C t
  have hlift : P ∈ lifts (algebraMap R ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card M
    · rw [hP, Multiset.prod_X_sub_C_coeff M hn]
      have hmem' : (-1 : ℂ) ^ (Multiset.card M - n) * M.esymm (Multiset.card M - n) ∈ R :=
        R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _) (hes _)
      exact ⟨⟨_, hmem'⟩, rfl⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hP, natDegree_multiset_prod_X_sub_C_eq_card]
      omega
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨q, hqm, ?_⟩
  rw [eval₂_eq_eval_map, hq, hP, eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.map_map]
  exact Multiset.mem_map.2 ⟨_, hmem, by simp⟩

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic

noncomputable section

namespace SuperlatticeRatio

theorem eq_of_le_of_relIndex {A B C : Submodule ℤ ℂ} {p : ℕ} (hp : p.Prime) (hAB : A ≤ B)
    (hBC : B ≤ C) (hidx : A.toAddSubgroup.relIndex C.toAddSubgroup = p) (hne : ¬ B ≤ A) :
    B = C := by
  have h := AddSubgroup.relIndex_mul_relIndex (H := A.toAddSubgroup) (K := B.toAddSubgroup)
    (L := C.toAddSubgroup) (fun _ hx ↦ hAB hx) (fun _ hx ↦ hBC hx)
  rw [hidx] at h
  rcases Nat.prime_mul_iff.1 (h ▸ hp) with ⟨-, h1⟩ | ⟨-, h1⟩
  · have h2 := AddSubgroup.relIndex_eq_one.1 h1
    exact le_antisymm hBC (fun x hx ↦ h2 hx)
  · have h2 := AddSubgroup.relIndex_eq_one.1 h1
    exact absurd (fun x hx ↦ h2 hx) hne

theorem mem_span_pair_iff {α β x : ℂ} :
    x ∈ Submodule.span ℤ ({α, β} : Set ℂ) ↔ ∃ m n : ℤ, (m : ℂ) * α + n * β = x := by
  simp [Submodule.mem_span_pair, zsmul_eq_mul]

theorem latticeDiscr_scale_latticeOfTau {c : ℂ} (hc : c ≠ 0) (σ : ℍ) :
    latticeDiscr (scaleLattice c (latticeOfTau σ).lattice) =
      (c ^ 12)⁻¹ * ((2 * Real.pi) ^ 12 * discriminant σ) := by
  rw [PhScale.latticeDiscr_scaleLattice _ hc, latticeDiscr_lattice, discr_latticeOfTau]

theorem proof : SuperlatticeRatio.Statement := by
  intro L L' p hp hle hidx
  obtain ⟨τ, c, hc, hL⟩ := ClassMean.exists_eq_scaleLattice L
  have hLs : L.lattice = Submodule.span ℤ {c * τ, c} := by
    rw [hL, ClassMean.scaleLattice_latticeOfTau]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hτ : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hcτ : c * τ ∈ L'.lattice := hle (hLs ▸ Submodule.subset_span (by simp))
  have hc' : c ∈ L'.lattice := hle (hLs ▸ Submodule.subset_span (by simp))

  refine ⟨τ, ?_, ?_⟩
  · rw [← weierstrassCurve_latticeOfTau_j, eq_comm, weierstrassCurve_j_eq_iff]
    refine ⟨c, hc, ?_⟩
    rw [hL, scaleLattice, Submodule.map_coe]
    rfl

  have hne : ¬ L'.lattice ≤ L.lattice := fun h ↦
    hp.one_lt.ne' (hidx ▸ AddSubgroup.relIndex_eq_one.2 (fun x hx ↦ h hx))
  obtain ⟨v, hvL', hvL⟩ := SetLike.not_le_iff_exists.1 hne
  have hpv : (p : ℂ) * v ∈ L.lattice := by
    have := AddSubgroup.nsmul_relIndex_mem L.lattice.toAddSubgroup
      (K := L'.lattice.toAddSubgroup) (g := v) hvL'
    rw [hidx, nsmul_eq_mul] at this
    exact this
  rw [hLs, mem_span_pair_iff] at hpv
  obtain ⟨m, n, hmn⟩ := hpv
  have hLdiscr : latticeDiscr L.lattice = (c ^ 12)⁻¹ * ((2 * Real.pi) ^ 12 * discriminant τ) := by
    rw [hL, latticeDiscr_scale_latticeOfTau hc]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hz : ∀ (z : ℤ) {x : ℂ}, x ∈ L'.lattice → (z : ℂ) * x ∈ L'.lattice := fun z x hx ↦ by
    rw [← zsmul_eq_mul]; exact zsmul_mem hx z
  by_cases hm : (p : ℤ) ∣ m
  ·
    obtain ⟨k, rfl⟩ := hm
    have hn : ¬ (p : ℤ) ∣ n := by
      rintro ⟨l, rfl⟩
      apply hvL
      rw [hLs, mem_span_pair_iff]
      refine ⟨k, l, mul_left_cancel₀ hp0 ?_⟩
      rw [← hmn]; push_cast; ring
    obtain ⟨u, w, huw⟩ := (hpZ.coprime_iff_not_dvd.2 hn).symm
    set σ := mulPoint ⟨p, hp.pos⟩ τ
    have hσ : (σ : ℂ) = p * τ := coe_mulPoint _ _
    have hcp : c / p ≠ 0 := div_ne_zero hc hp0
    have hM : scaleLattice (c / p) (latticeOfTau σ).lattice = Submodule.span ℤ {c * τ, c / p} := by
      rw [ClassMean.scaleLattice_latticeOfTau, hσ, show c / p * (p * τ) = c * τ by field_simp]
    have heq : scaleLattice (c / p) (latticeOfTau σ).lattice = L'.lattice := by
      refine eq_of_le_of_relIndex hp ?_ ?_ hidx ?_
      · rw [hLs, hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, mem_span_pair_iff]
        · exact ⟨1, 0, by simp⟩
        · have key2 : (p : ℂ) * (c / p) = c := by field_simp
          exact ⟨0, p, by push_cast; linear_combination key2⟩
      · rw [hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩
        · exact hcτ
        · have e : c / p = (u : ℂ) * v + ((-(u * k) : ℤ) : ℂ) * (c * τ) + (w : ℂ) * c := by
            have hmn' : (p : ℂ) * v = p * k * (c * τ) + n * c := by rw [← hmn]; push_cast; ring
            have huw' : (u : ℂ) * n + w * p = 1 := by exact_mod_cast huw
            push_cast
            rw [div_eq_iff hp0]
            linear_combination (-(u : ℂ)) * hmn' - c * huw'
          rw [SetLike.mem_coe, e]
          exact add_mem (add_mem (hz u hvL') (hz _ hcτ)) (hz w hc')
      · intro h
        have : c / p ∈ L.lattice := h (hM ▸ Submodule.subset_span (by simp))
        rw [hLs, mem_span_pair_iff] at this
        obtain ⟨m', n', e⟩ := this
        have e2 : c * ((m' : ℂ) * τ + n' - 1 / p) = 0 := by linear_combination e
        have e' : (m' : ℂ) * τ + n' = 1 / p := sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hc)
        have him : (m' : ℝ) * (τ : ℂ).im = 0 := by
          have := congrArg Complex.im e'
          simpa using this
        have hm0 : m' = 0 := by
          rcases mul_eq_zero.1 him with h0 | h0
          · exact_mod_cast h0
          · exact absurd h0 hτ
        subst hm0
        have hre : (n' : ℂ) * p = 1 := by
          have e3 : (n' : ℂ) = 1 / p := by simpa using e'
          rw [e3]; field_simp
        have : (p * n' : ℤ) = 1 := by rw [mul_comm]; exact_mod_cast hre
        exact hpZ.not_dvd_one ⟨n', this.symm⟩
    refine Multiset.mem_cons.2 (Or.inl ?_)
    rw [← heq, latticeDiscr_scale_latticeOfTau hcp, hLdiscr]
    have hΔ := discriminant_ne_zero τ
    simp only [PNat.mk_coe]
    field_simp
    rfl
  ·
    obtain ⟨u, w, huw⟩ := (hpZ.coprime_iff_not_dvd.2 hm).symm
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
    set r := u * n % p with hr
    set q := u * n / p
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hpz.ne'
    have hrp : r < p := Int.emod_lt_of_pos _ hpz
    have hrq : r + q * p = u * n := Int.emod_add_ediv_mul _ _
    set a := r.toNat
    have ha : (a : ℤ) = r := Int.toNat_of_nonneg hr0
    have hap : a < p := by omega
    have haC : (a : ℂ) = r := by exact_mod_cast ha
    set σ := divPoint ⟨p, hp.pos⟩ a τ
    have hσ : (σ : ℂ) = (a + τ) / p := coe_divPoint _ _ _
    have hM : scaleLattice c (latticeOfTau σ).lattice =
        Submodule.span ℤ {c * ((a + τ) / p), c} := by
      rw [ClassMean.scaleLattice_latticeOfTau, hσ]
    have heq : scaleLattice c (latticeOfTau σ).lattice = L'.lattice := by
      refine eq_of_le_of_relIndex hp ?_ ?_ hidx ?_
      · rw [hLs, hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, mem_span_pair_iff]
        · have key : (p : ℂ) * (c * ((a + τ) / p)) = c * (a + τ) := by field_simp
          exact ⟨p, -(a : ℤ), by push_cast; linear_combination key⟩
        · exact ⟨0, 1, by simp⟩
      · rw [hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩
        · have e : c * ((a + τ) / p) = (u : ℂ) * v + (w : ℂ) * (c * τ) + ((-q : ℤ) : ℂ) * c := by
            have hmn' : (p : ℂ) * v = m * (c * τ) + n * c := hmn.symm
            have huw' : (u : ℂ) * m + w * p = 1 := by exact_mod_cast huw
            have hrq' : (r : ℂ) + q * p = u * n := by exact_mod_cast hrq
            have haC' : (a : ℂ) - r = 0 := by rw [haC]; ring
            push_cast
            rw [mul_div_assoc', div_eq_iff hp0]
            linear_combination (-(u : ℂ)) * hmn' - c * τ * huw' + c * hrq' + c * haC'
          rw [SetLike.mem_coe, e]
          exact add_mem (add_mem (hz u hvL') (hz w hcτ)) (hz _ hc')
        · exact hc'
      · intro h
        have : c * ((a + τ) / p) ∈ L.lattice := h (hM ▸ Submodule.subset_span (by simp))
        rw [hLs, mem_span_pair_iff] at this
        obtain ⟨m', n', e⟩ := this
        have hdiv : c * ((a + τ) / p) * p = c * (a + τ) := by field_simp
        have e2 : c * ((a + τ) - p * (m' * τ + n')) = 0 := by
          linear_combination (-(p : ℂ)) * e - hdiv
        have e' : (a : ℂ) + τ - p * (m' * τ + n') = 0 := (mul_eq_zero.1 e2).resolve_left hc
        have him : τ.im * (1 - p * m') = 0 := by
          have := congrArg Complex.im e'
          simp at this
          linear_combination this
        have h1 : ((p * m' : ℤ) : ℝ) = 1 := by
          push_cast
          linarith [(mul_eq_zero.1 him).resolve_left τ.im_pos.ne']
        have h1' : (p * m' : ℤ) = 1 := by exact_mod_cast h1
        exact hpZ.not_dvd_one ⟨m', h1'.symm⟩
    refine Multiset.mem_cons_of_mem (Multiset.mem_map.2 ⟨a, Multiset.mem_range.2 hap, ?_⟩)
    rw [← heq, latticeDiscr_scale_latticeOfTau hc, hLdiscr]
    have hΔ := discriminant_ne_zero τ
    field_simp
    rfl

end SuperlatticeRatio

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian

theorem KroneckerLimit.full : KroneckerLimit.Statement :=
  KroneckerLimit.proof KroneckerSplit.proof PowerIntegral.proof ShiftedSumIntegral.proof
    CotangentSum.proof LogEta.proof GammaZetaLimit.proof

theorem PhTau.full : PhTau.Statement :=
  PhTau.proof DeltaEta.proof

theorem ClassMean.full {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
    (S : PrimeDiscriminant K) : ClassMean.Statement S :=
  ClassMean.proof S KroneckerLimit.full (ClassEpstein.proof S) (ZetaFactor.proof S) PhTau.full
    PhScale.proof

section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end
