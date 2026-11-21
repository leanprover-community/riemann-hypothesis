import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEvaluationSelfLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerL2Constant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterTrivialOnSmallIdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLevelConductorCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterTrivialImpliesIntegralTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.ScaleBound

theorem exists_l2_const (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hPair : IsPair B M χX χW om r s r' s') (M₁ : Model σ X W) (hM₁ : M₁.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n d) (hE : IsEv B M M₁ 1 1 ∅ e)
    (μ : @Measure (Fin n × Fin d → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl F, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  refine GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure ?_ (fun v => ?_) μ hμ
  · letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact GlobalTheory.T.schrodinger_intertwiner_l2_constant F (Fin n × Fin d) ψ hψ ei A hA
  · have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ :=
      GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA

variable {F : Type} [Field F] [NumberField F]

theorem tAd_eq_infScale (s : ℝ) : tAd F s = GlobalTheory.TorusTheta.infScale F s := by
  unfold tAd GlobalTheory.TorusTheta.infScale realAd
  refine Prod.ext ?_ ?_
  · show (1 : InfiniteAdeleRing F) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (s - 1)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ s)
    rw [map_sub, map_sub, map_one, map_one, add_sub_cancel]
  · show (1 : FiniteAdeleRing (𝓞 F) F) + 0 = 1
    exact add_zero 1

variable (F) in

def scaleHom : ℝ →* AF F where
  toFun := GlobalTheory.TorusTheta.infScale F
  map_one' := by
    unfold GlobalTheory.TorusTheta.infScale
    rw [map_one, map_one]
    rfl
  map_mul' u v := by
    unfold GlobalTheory.TorusTheta.infScale
    rw [map_mul, map_mul]
    exact Prod.ext rfl (one_mul (1 : FiniteAdeleRing (𝓞 F) F)).symm

theorem blkScale_eq {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (t : Fin q → ℝ)
    (z : κ → AF F) :
    blkScale blk t z = fun j => GlobalTheory.TorusTheta.infScale F (∏ i, if j ∈ blk i then t i else 1) * z j := by
  funext j
  unfold blkScale
  congr 1
  show _ = scaleHom F _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact tAd_eq_infScale _
  · exact (map_one _).symm

theorem prod_scale_pow {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (t : Fin q → ℝ)
    (ht : ∀ i, 0 < t i) (f : ℕ) :
    ∏ j, (∏ i, if j ∈ blk i then t i else 1) ^ f = (∏ i, t i ^ (((f * (blk i).card : ℕ) : ℝ) / 2)) ^ 2 := by
  rw [Finset.prod_pow, Finset.prod_comm, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← Real.rpow_natCast (t i ^ _) 2,
    ← Real.rpow_mul (ht i).le, Nat.cast_ofNat, div_mul_cancel₀ _ two_ne_zero, Real.rpow_natCast, mul_comm, pow_mul]

theorem norm_scalar_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J) (c : ℂ), (∀ i, 0 < t i) → IsTorusU x y t a →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z)) →
      ‖c‖ ≤ ∏ i, t i ^ ex i := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y _ M₁ blk e hM₁ _ hE
  refine ⟨fun i => (((Module.finrank ℚ F * (blk i).card : ℕ) : ℝ) / 2), fun t a c ht _ hc => ?_⟩
  have hS := IsUWeilPair.isUSplitting hP.weil
  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE
  have heΦ := hE.maps Φ hΦ
  have hcont : Continuous (e Φ) := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA (F := F) heΦ
  have hI0 : ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ ≠ 0 := by
    intro h
    have hm : AEMeasurable (fun z => ‖e Φ z‖ₑ ^ 2) μ := (hcont.measurable.enorm.pow_const 2).aemeasurable
    rw [lintegral_eq_zero_iff' hm] at h
    have h' : e Φ =ᵐ[μ] 0 := h.mono fun z hz => by simpa using hz
    exact h0 ((hcont.ae_eq_iff_eq μ continuous_const).1 h')
  have hIt : ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h2 := (GlobalTheory.WeilM.schA_memLp_two F _ μ hμ _ heΦ).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h2
    simpa using h2.ne
  obtain ⟨l, hl⟩ := exists_l2_const F E σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE μ hμ
  have hU : ∫⁻ z, ‖e (om (a, 1) Φ) z‖ₑ ^ 2 ∂μ = ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ := by
    rw [hl _ (hS.pres (a, 1) Φ hΦ), hl Φ hΦ, hS.unit μ hμ (a, 1) Φ hΦ]
  set u : Fin n × Fin d → ℝ := fun j => ∏ i, if j ∈ blk i then t i else 1 with hu
  have hupos : ∀ j, 0 < u j := fun j => Finset.prod_pos fun i _ => by
    split_ifs
    · exact ht i
    · exact one_pos
  have hsc := GlobalTheory.T.lintegral_infinite_scaling F (Fin n × Fin d) u hupos μ hμ (fun z => ‖e Φ z‖ₑ ^ 2)
  simp only [hc Φ hΦ, enorm_mul, mul_pow, blkScale_eq] at hU
  rw [lintegral_const_mul' _ _ (by simp), hsc] at hU
  set P := ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) with hPdef
  have hPpos : 0 < ∏ j, u j ^ Module.finrank ℚ F := Finset.prod_pos fun j _ => pow_pos (hupos j) _
  have hP0 : P ≠ 0 := by rw [hPdef]; exact (ENNReal.ofReal_pos.2 hPpos).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk : ‖c‖ₑ ^ 2 * P⁻¹ = 1 := by
    rw [← mul_assoc] at hU
    exact (ENNReal.mul_eq_right hI0 hIt).1 hU
  have hk' : ‖c‖ₑ ^ 2 = P := by
    have := congrArg (· * P) hk
    simpa [mul_assoc, ENNReal.inv_mul_cancel hP0 hPt] using this
  have hk'' : ENNReal.ofReal (‖c‖ ^ 2) = ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) := by
    rw [← hPdef, ← hk', ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hsq := (ENNReal.ofReal_eq_ofReal_iff (by positivity) hPpos.le).1 hk''
  rw [hu, prod_scale_pow blk t ht] at hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ht i).le _) two_ne_zero).1 hsq).le

end GlobalTheory.ThKTorus.ScaleBound

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_frame_blocks_evaluation : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J) (c : ℂ), (∀ i, 0 < t i) → IsTorusU x y t a →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z)) →
      ‖c‖ ≤ ∏ i, t i ^ ex i := by
  atlas_forward_decl GlobalTheory.ThKTorus.ScaleBound.norm_scalar_le
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section
namespace GlobalTheory.ThKTorus.Scale
variable {F : Type} [Field F] [NumberField F]

theorem realAd_add (u v : ℝ) : realAd F u + realAd F v = realAd F (u + v) := by
  simp only [realAd, map_add]
  rfl

theorem realAd_mul (u v : ℝ) : realAd F u * realAd F v = realAd F (u * v) := by
  simp only [realAd, map_mul]
  exact Prod.ext rfl (mul_zero _)

theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem tAd_mul (u v : ℝ) : tAd F u * tAd F v = tAd F (u * v) := by
  simp only [tAd]
  have : realAd F (u * v - 1) = realAd F (u - 1) + realAd F (v - 1) + realAd F (u - 1) * realAd F (v - 1) := by
    rw [realAd_mul, realAd_add, realAd_add]; congr 1; ring
  rw [this]; ring

theorem tAd_one : tAd F 1 = 1 := by
  simp [tAd, realAd_zero]

theorem tAd_inv_mul {s : ℝ} (hs : s ≠ 0) : tAd F s⁻¹ * tAd F s = 1 := by
  rw [tAd_mul, inv_mul_cancel₀ hs, tAd_one]

section GlobalTheory
variable {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ)

theorem prod_inv_mul (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (j : κ) :
    (∏ i, if j ∈ blk i then tAd F (t i)⁻¹ else 1) * (∏ i, if j ∈ blk i then tAd F (t i) else 1) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · exact tAd_inv_mul (ht i)
  · exact one_mul 1

theorem blkScale_inv_blkScale (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (z : κ → AF F) :
    blkScale blk (fun i => (t i)⁻¹) (blkScale blk t z) = z := by
  funext j
  simp only [blkScale]
  rw [← mul_assoc, prod_inv_mul blk t ht j, one_mul]

theorem blkScale_add (s : Fin q → ℝ) (z w : κ → AF F) :
    blkScale blk s (z + w) = blkScale blk s z + blkScale blk s w := by
  funext j
  simp only [blkScale, Pi.add_apply, mul_add]

theorem dot_blkScale (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (x y : κ → AF F) :
    blkScale blk (fun i => (t i)⁻¹) x ⬝ᵥ blkScale blk t y = x ⬝ᵥ y := by
  simp only [dotProduct, blkScale]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, prod_inv_mul blk t ht j, one_mul]

theorem schr_blkScale (ψ : AddChar (AF F) ℂ) (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (p r : κ → AF F)
    (g : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (blkScale blk (fun i => (t i)⁻¹) p, blkScale blk t r) g (blkScale blk (fun i => (t i)⁻¹) x) =
      schr ψ (p, r) (fun z => g (blkScale blk (fun i => (t i)⁻¹) z)) x := by
  simp only [schr, dot_blkScale blk t ht, blkScale_add]

end GlobalTheory

section Main
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem co_mat_mul {σ : E →ₐ[F] E} {n d q : ℕ} {J : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    {x y : Fin q → Fin n → E} {co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW)) (Fin n × Fin d)}
    {blk : Fin q → Finset (Fin n × Fin d)} (hco : IsFrameCo σ J JW x y co blk) {t : Fin q → ℝ} {a : UA σ J}
    (ht : ∀ i, 0 < t i) (hta : IsTorusU x y t a) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    co.e (mat a * w) = (blkScale blk (fun i => (t i)⁻¹) (co.e w).1, blkScale blk t (co.e w).2) := by
  have hw : w = co.e.symm ((co.e w).1, 0) + co.e.symm (0, (co.e w).2) := by
    rw [← map_add]; simp
  conv_lhs => rw [hw]
  rw [Matrix.mul_add, map_add, ((hco.2 t a ht hta) _).1, ((hco.2 t a ht hta) _).2]
  simp

def twist {n d : ℕ} {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} (e : Fn F n d →ₗ[ℂ] Fn F n d) (om : Rep σ X W)
    (a : UA σ X.J) {q : ℕ} (blk : Fin q → Finset (Fin n × Fin d)) (t : Fin q → ℝ) : Fn F n d →ₗ[ℂ] Fn F n d :=
  LinearMap.funLeft ℂ ℂ (blkScale blk (fun i => (t i)⁻¹)) ∘ₗ e ∘ₗ om (a, 1)

theorem incM_one (n : ℕ) : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [incM]

theorem twist_heis {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hpair : IsPair B M χX χW om r s r' s') {q : ℕ}
    {x y : Fin q → Fin n → E} {M₁ : Model σ X W} {blk : Fin q → Finset (Fin n × Fin d)} {e : Fn F n d →ₗ[ℂ] Fn F n d}
    (hco : IsFrameCo σ X.J W.J x y M₁.co blk) (hev : IsEv B M M₁ 1 1 ∅ e) {t : Fin q → ℝ} {a : UA σ X.J}
    (ht : ∀ i, 0 < t i) (hta : IsTorusU x y t a) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    ∀ Ψ ∈ schA F (Fin n × Fin d), twist e om a blk t (M.co.rho B.ψ w Ψ) = M₁.co.rho B.ψ w (twist e om a blk t Ψ) := by
  intro Ψ hΨ
  have hs := hpair.weil.isUSplitting
  have hΨ' : om (a, 1) Ψ ∈ schA F (Fin n × Fin d) := hs.pres (a, 1) Ψ hΨ
  have h1 : om (a, 1) (M.co.rho B.ψ w Ψ) = M.co.rho B.ψ (mat a * w) (om (a, 1) Ψ) := by
    rw [hs.impl (a, 1) w Ψ hΨ]
    congr 2
    simp [actAB, mat]
  have h2 : e (M.co.rho B.ψ (mat a * w) (om (a, 1) Ψ)) = M₁.co.rho B.ψ (mat a * w) (e (om (a, 1) Ψ)) := by
    simpa [incM_one] using hev.Heisenberg₂ (mat a * w) _ hΨ'
  funext z
  have hne : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  simp only [twist, LinearMap.comp_apply, LinearMap.funLeft_apply]
  rw [h1, h2]
  simp only [Darboux.rho, co_mat_mul hco ht hta w]
  exact schr_blkScale blk B.ψ t hne _ _ _ z

end Main

theorem norm_eval_torus_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J), (∀ i, 0 < t i) → IsTorusU x y t a →
      ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F),
        ‖e (om (a * κ, h) (pureA F f φ)) z‖ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair q x y hxy M₁ blk e hM₁ hco hev φ hφ
  obtain ⟨ex, hex⟩ := GlobalTheory.T.pair_frame_blocks_evaluation hK F E σ B n d X W M χX χW om r s r' s' hpair q x y hxy M₁ blk e hM₁ hco hev
  refine ⟨ex, fun t a ht hta f κ h z => ?_⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_evaluation_self_linear hK F E σ B n d X W M χX χW om r s r' s' hpair M₁ e hM₁ hev (twist e om a blk t)
    (fun w => twist_heis hpair hco hev ht hta w)
  have hne : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  have key : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z) := by
    intro Ψ hΨ z
    have := congrFun (hc Ψ hΨ) (blkScale blk t z)
    simpa [twist, blkScale_inv_blkScale blk t hne] using this
  have hc' := hex t a c ht hta key
  have hs := hpair.weil.isUSplitting
  have hΨ0 : om (κ, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) :=
    hs.pres (κ, h) _ (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
  rw [show ((a * κ, h) : UA σ X.J × UA σ W.J) = (a, 1) * (κ, h) by simp, map_mul, Module.End.mul_apply,
    key _ hΨ0, norm_mul]
  exact mul_le_mul_of_nonneg_right hc' (norm_nonneg _)

end GlobalTheory.ThKTorus.Scale
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_frame_block_eigen_relation : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J), (∀ i, 0 < t i) → IsTorusU x y t a →
      ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F),
        ‖e (om (a * κ, h) (pureA F f φ)) z‖ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := by
  atlas_forward_decl GlobalTheory.ThKTorus.Scale.norm_eval_torus_le
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_character_trivial_implies_integral_trace : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) x * t) = 1) → ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  first | exact @GlobalTheory.TraceIntStd.trace_int_of_isStd | exact GlobalTheory.TraceIntStd.trace_int_of_isStd | (intros; apply GlobalTheory.TraceIntStd.trace_int_of_isStd <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_dual_lattice_bounded_denominator : ∀ {F : Type} [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ ξ : F, (∀ o : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * o) = z) → ∃ o : 𝓞 F, (D : F) * ξ = o := by
  first | exact @GlobalTheory.exists_den_traceDual_ringOfIntegers | exact GlobalTheory.exists_den_traceDual_ringOfIntegers | (intros; apply GlobalTheory.exists_den_traceDual_ringOfIntegers <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_abs_matrix_product_le_heights : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  first | exact @GlobalTheory.absFin_mul_mul_transpose_le | exact GlobalTheory.absFin_mul_mul_transpose_le | (intros; apply GlobalTheory.absFin_mul_mul_transpose_le <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_form_bounded_by_local_constants : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
  first | exact @GlobalTheory.LinFormBound.main | exact GlobalTheory.LinFormBound.main | (intros; apply GlobalTheory.LinFormBound.main <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entries_bounded_almost_everywhere : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))) ≤ K v := by
  first | exact @GlobalTheory.FixedBound.exists_entry_absFin_bound | exact GlobalTheory.FixedBound.exists_entry_absFin_bound | (intros; apply GlobalTheory.FixedBound.exists_entry_absFin_bound <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom

theorem std_char_denom : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ D : ℕ, 0 < D ∧
    ∀ ξ : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) ξ * t) = 1) →
      ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _ ψ hψ
  obtain ⟨D, hD, h⟩ := GlobalTheory.T.trace_dual_lattice_bounded_denominator (F := F)
  refine ⟨D, hD, fun ξ hξ => h ξ fun o => GlobalTheory.T.standard_character_trivial_implies_integral_trace ψ hψ _ fun t ht0 ht1 => ?_⟩
  have e : algebraMap F (AF F) (ξ * o) * t = algebraMap F (AF F) ξ * (algebraMap F (AF F) o * t) := by
    rw [map_mul, mul_assoc]
  rw [e]
  refine hξ _ ?_ fun v => ?_
  · rw [show (algebraMap F (AF F) (o : F) * t).1 = (algebraMap F (AF F) (o : F)).1 * t.1 from rfl, ht0, mul_zero]
  · rw [map_mul, AlgHom.commutes, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ht1 v)
    refine Valued.toNormedField.norm_le_one_iff.2 ?_
    first
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact v.valuation_le_one o)
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact v.valuation_le_one o)
      | (exact (HeightOneSpectrum.coe_mem_adicCompletionIntegers v o))

open Formalism.UG in

theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 := by
  intro F E _ _ _ _ _ n d e
  classical
  set Y : Fin n × Fin d → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) :=
    fun j => e.symm (0, fun k => if j = k then 1 else 0) with hY
  let f1 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.fst (AF F) _ _).comp e.toLinearMap)
  let f2 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.snd (AF F) _ _).comp e.toLinearMap)
  choose K1 hK1f hK11 hK1 using fun i => GlobalTheory.T.linear_form_bounded_by_local_constants (f1 i)
  choose K2 hK2f hK21 hK2 using fun i => GlobalTheory.T.linear_form_bounded_by_local_constants (f2 i)
  choose KY hKYf hKY1 hKY using fun j => GlobalTheory.T.matrix_entries_bounded_almost_everywhere (Y j)
  have prod_one : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ v, 1 ≤ ∏ i, K i v := fun K hK v => Finset.one_le_prod' fun i _ => hK i v
  have prod_fin : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i, (Function.mulSupport (K i)).Finite) →
      (Function.mulSupport fun v => ∏ i, K i v).Finite := fun K hK =>
    ((Finset.univ : Finset (Fin n × Fin d)).finite_toSet.biUnion fun i _ => hK i).subset
      (Finset.mulSupport_prod _ _)
  have single_le : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ i v, K i v ≤ ∏ i, K i v := fun K hK i v => Finset.single_le_prod' (fun j _ => hK j v) (Finset.mem_univ i)
  set Ka : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v with hKa
  have hKa1 : ∀ v, 1 ≤ Ka v := fun v => one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (prod_one K1 hK11 v) (prod_one K2 hK21 v)) (prod_one KY hKY1 v)
  have hKaf : (Function.mulSupport Ka).Finite :=
    ((((prod_fin K1 hK1f).union (prod_fin K2 hK2f)).subset (Function.mulSupport_mul _ _)).union
      (prod_fin KY hKYf)).subset (Function.mulSupport_mul _ _)
  have hle1 : ∀ i j v, K1 i v * KY j v ≤ Ka v := fun i j v =>
    calc K1 i v * KY j v ≤ (∏ i, K1 i v) * ∏ j, KY j v := mul_le_mul' (single_le K1 hK11 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K1 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        rw [mul_right_comm]
        exact le_mul_of_one_le_right' (prod_one K2 hK21 v)
  have hle2 : ∀ i j v, K2 i v * KY j v ≤ Ka v := fun i j v =>
    calc K2 i v * KY j v ≤ (∏ i, K2 i v) * ∏ j, KY j v := mul_le_mul' (single_le K2 hK21 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K2 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        exact mul_le_mul_left (le_mul_of_one_le_left' (prod_one K1 hK11 v)) _
  refine ⟨((∏ᶠ v, Ka v : ℝ≥0) : ℝ), fun g h => ?_⟩
  set B : HeightOneSpectrum (𝓞 F) → ℝ≥0 :=
    fun v => Ka v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) with hB
  have hB1 : ∀ v, 1 ≤ B v := fun v =>
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hKa1 v) (one_le_htOf _ _)) (one_le_htOf _ _)
  have hgf := finite_mulSupport_htFin F g
  have hhf := finite_mulSupport_htFin F h
  have hBf : (Function.mulSupport B).Finite :=
    (((hKaf.union hgf).subset (Function.mulSupport_mul _ _)).union hhf).subset (Function.mulSupport_mul _ _)
  obtain ⟨N, hN, hNle, hNint⟩ := GlobalTheory.SmoothForms.denom_global B hB1 hBf
  have hfin : ∀ {m : ℕ} (k : GL (Fin m) (AF F ⊗[F] E)), ∏ᶠ v, htFin F v (bc (compFin F E v) k) ≤ heightGL F k :=
    fun k => by
      unfold heightGL
      exact le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)
  refine ⟨N, hN, ?_, ?_⟩
  · have e1 : ∏ᶠ v, B v = (∏ᶠ v, Ka v) * (∏ᶠ v, htFin F v (bc (compFin F E v) g)) *
        ∏ᶠ v, htFin F v (bc (compFin F E v) h) := by
      rw [hB, finprod_mul_distrib ((hKaf.union hgf).subset (Function.mulSupport_mul _ _)) hhf,
        finprod_mul_distrib hKaf hgf]
    have : (N : ℝ≥0) ≤ (∏ᶠ v, Ka v) * (heightGL F g * heightGL F h) := by
      refine hNle.trans ?_
      rw [e1, mul_assoc]
      exact mul_le_mul_right (mul_le_mul' (hfin g) (hfin h)) _
    exact_mod_cast this
  intro M y hy
  set L : (Fin n × Fin d → AF F) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    e.toLinearMap ∘ₗ sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) ∘ₗ
      e.symm.toLinearMap ∘ₗ LinearMap.inr (AF F) _ _ with hL
  have hLy : e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) =
      ∑ j, y j • L (fun k => if j = k then 1 else 0) := LinearMap.pi_apply_eq_sum_univ L y
  have hsz : ∀ j v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v
      (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j) p.1 p.2))) ≤
      htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h) := fun j v =>
    Finset.sup_le fun p _ => (GlobalTheory.T.finite_abs_matrix_product_le_heights g (Y j) h v p.1 p.2).trans
      (mul_le_mul_left (mul_le_mul_right (hKY j v) _) _)
  have hcomp : ∀ t : Fin n × Fin d → AF F, (∀ j v, ‖evFin F v (t j)‖₊ ≤ B v) →
      (∑ j, y j * t j).1 = 0 ∧ ∀ v, ‖evFin F v (∑ j, y j * t j)‖ ≤ ‖(M : Fv F v)‖ := by
    intro t ht
    refine ⟨?_, fun v => ?_⟩
    · change fstA F (∑ j, y j * t j) = 0
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul]
      change (y j).1 * _ = 0
      rw [hy.1 j, zero_mul]
    · rw [map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
      rw [map_mul, norm_mul]
      have h1 := hy.2 v j
      have h2 := hNint v (evFin F v (t j)) (ht j v)
      rw [Nat.cast_mul, norm_mul] at h1
      rw [norm_mul] at h2
      calc ‖evFin F v (y j)‖ * ‖evFin F v (t j)‖ ≤ ‖(M : Fv F v)‖ * ‖(N : Fv F v)‖ * ‖evFin F v (t j)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ * (‖(N : Fv F v)‖ * ‖evFin F v (t j)‖) := mul_assoc _ _ _
        _ ≤ ‖(M : Fv F v)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ := mul_one _
  have htB : ∀ (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) (K : HeightOneSpectrum (𝓞 F) → ℝ≥0),
      (∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) →
      (∀ j v, K v * KY j v ≤ Ka v) → ∀ j v,
      ‖evFin F v (f (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j)))‖₊ ≤ B v := by
    intro f K hf hK j v
    refine (hf _ v).trans ?_
    refine (mul_le_mul_right (hsz j v) _).trans ?_
    calc K v * (htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h)) =
        K v * KY j v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) := by ring
      _ ≤ B v := mul_le_mul_left (mul_le_mul_left (hK j v) _) _
  refine ⟨⟨fun i => ?_, fun v i => ?_⟩, ⟨fun i => ?_, fun v i => ?_⟩⟩
  all_goals rw [hLy]
  all_goals simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).2 v
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).2 v

end GlobalTheory.ThetaDenom

end
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
open GlobalTheory.ThetaDenom

namespace GlobalTheory.ThKTorusBound

open scoped Classical

theorem exists_clm_eval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F),
      ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), e (om (κ, h) (pureA F f φ)) z = T f := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev φ hφ κ h z
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hPair.weil
  have hl : (LinearMap.proj z : Fn F n d →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin n × Fin d) := GlobalTheory.RealLift.eval_mem_adm z
  have hl2 := GlobalTheory.DoublingEv.IsTame.comp_adm
    (GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hPair.good hM₁ hev) hl
  have hl3 := hS.adm (κ, h) _ hl2
  obtain ⟨T, hT⟩ := hl3 φ hφ
  exact ⟨T, fun f => by simpa using (hT f)⟩

theorem exists_transfer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∃ (om₁ : Rep σ X W) (e₀ : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), IsPair B M₁ χX χW om₁ r s r' s' ∧ IsEv B M M₁ 1 1 ∅ e₀ ∧
      ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = c • om₁ x (e₀ Φ) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev
  obtain ⟨a, ha, hco⟩ := GlobalTheory.goodModel_coords_rat_symplectic F E σ B.ψ n d X W M M₁ hP.good hM₁
  obtain ⟨e₀, -, -, he₀, hbij, -⟩ := GlobalTheory.RatWeilOp.exists_intertwiner hK.base F E σ B n d X W M M₁ r s r' s'
    hP.base hP.herm hP.skew hP.good hM₁ a ha hco
  obtain ⟨om₁, hW, hint⟩ := GlobalTheory.T.weil_eigen_bijective_schwartz F E σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e₀ he₀ hbij
  have h1n : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by simp [incM]
  have h1d : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_evaluation_self_linear hK F E σ B n d X W M χX χW om r s r' s' hP M₁ e₀ hM₁ he₀ e (fun z Φ hΦ => by
    have := hev.Heisenberg₂ z Φ hΦ
    rwa [h1n, h1d, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this)
  refine ⟨om₁, e₀, c, ⟨hP.base, hP.herm, hP.skew, hM₁, hP.hX, hP.hW, hP.resX, hP.resW, hW⟩, he₀, fun x Φ hΦ => ?_⟩
  rw [hc _ (hP.weil.isUSplitting.pres x Φ hΦ), hint x Φ hΦ]

theorem adelic_char_denom {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∃ D : ℕ, 0 < D ∧ ∀ x : AF F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (x * t) = 1) →
      ∀ v : Pl F, evFin F v ((D : AF F) * x) ∈ v.adicCompletionIntegers F := by
  obtain ⟨D, hD, hcond⟩ := std_char_denom ψ hψ
  obtain ⟨m, hm, htriv⟩ := GlobalTheory.PsiTriv.exists_nat_trivial ψ hψ.1
  refine ⟨D, hD, fun x hx v => ?_⟩
  obtain ⟨ξ, a, ha, hxa⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F m hm).1 x.2
  set A : AF F := ((0 : InfiniteAdeleRing F), a) with hA
  have hAv : ∀ v : Pl F, evFin F v A ∈ v.adicCompletionIntegers F := fun v => ha v
  have hev : ∀ v : Pl F, evFin F v x = algebraMap F (Fv F v) ξ + (m : Fv F v) * evFin F v A := fun v => by
    have e1 : evFin F v x = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x.2 := rfl
    have e2 : evFin F v A = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a := rfl
    rw [e1, e2, hxa, map_add, map_nsmul, AlgHom.commutes, nsmul_eq_mul]
  have hsplit : ∀ t : AF F, t.1 = 0 → x * t = algebraMap F (AF F) ξ * t + (m : AF F) * A * t := fun t ht => by
    refine Prod.ext ?_ ?_
    · change x.1 * t.1 = (algebraMap F (AF F) ξ).1 * t.1 + ((m : AF F) * A).1 * t.1
      rw [ht, mul_zero, mul_zero, mul_zero, add_zero]
    · change x.2 * t.2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ * t.2 + (m : FiniteAdeleRing (𝓞 F) F) * a * t.2
      rw [hxa, nsmul_eq_mul, add_mul]
  obtain ⟨o, ho⟩ := hcond ξ fun t ht0 ht1 => by
    have h1 := hx t ht0 ht1
    have h2 : ψ ((m : AF F) * A * t) = 1 := by
      refine htriv _ ?_ fun v => ?_
      · change ((m : AF F) * A).1 * t.1 = 0
        rw [ht0, mul_zero]
      · rw [map_mul, map_mul, map_natCast, norm_mul, norm_mul, mul_assoc]
        exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀
          (Valued.toNormedField.norm_le_one_iff.2 (hAv v)) (norm_nonneg _) (ht1 v))
    rwa [hsplit t ht0, AddChar.map_add_eq_mul, h2, mul_one] at h1
  have ho' : (D : Fv F v) * algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F := by
    rw [← map_natCast (algebraMap F (Fv F v)) D, ← map_mul, ho]
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v o
  rw [map_mul, map_natCast, hev, mul_add]
  exact add_mem ho' (mul_mem (natCast_mem _ D) (mul_mem (natCast_mem _ m) (hAv v)))

theorem tame_fixed {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)} (hT : GlobalTheory.DoublingEv.IsTame F T)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ (f : SInf F κ) (a b : κ → AF F), IsMulInt F m₀ a → IsMulInt F m₀ b →
      schr ψ (a, b) (T (pureA F f g)) = T (pureA F f g) := by
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  obtain ⟨m₃, hm₃, h3⟩ := GlobalTheory.PsiTriv.exists_nat_trivial ψ hψ
  choose m₁ hm₁ h1 using fun j => GlobalTheory.SBTransl.transInv (g' j) (hg' j)
  choose M hM h2 using fun j => GlobalTheory.SuppDen.support_bounded_denominators (g' j) (hg' j)
  refine ⟨∏ j, 2 * m₁ j * M j * m₃, Finset.prod_pos fun j _ => by have := hm₁ j; have := hM j; positivity,
    fun f a b ha hb => ?_⟩
  have hj : ∀ j, schr ψ (a, b) (pureA F (P j f) (g' j)) = pureA F (P j f) (g' j) := fun j => by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at ha hb
    exact GlobalTheory.PureFix.pureA_fixed ψ (g' j) (m₁ j) (M j) m₃ (hm₁ j) (hM j) hm₃ (h1 j) (h2 j) h3 _ a b ha.mono hb.mono
  rw [hP]
  funext z
  have hz := fun j => congrFun (hj j) z
  simp only [schr, Finset.sum_apply, Finset.mul_sum] at hz ⊢
  exact Finset.sum_congr rfl fun j _ => hz j

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {Cc : Set (UA σ J)} (hCc : IsCompact Cc) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ κ ∈ Cc, (ht κ : ℝ) ≤ H := by
  have hc : Continuous fun κ : UA σ J => (ht κ : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨H, hH⟩ := hCc.bddAbove_image hc.continuousOn
  exact ⟨max H 0, le_max_right _ _, fun κ hκ => (hH ⟨κ, hκ, rfl⟩).trans (le_max_left _ _)⟩

theorem support_unif : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ (C : ℝ) (k : ℕ), ∀ (κ : UA σ X.J) (h : UA σ W.J), κ ∈ Cc →
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧ ∀ (f : SInf F (Fin n × Fin d)) (z : Fin n × Fin d → AF F),
        e (om (κ, h) (pureA F f φ)) z ≠ 0 → ∀ j (v : Pl F), evFin F v ((m : AF F) * z j) ∈ v.adicCompletionIntegers F := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev Cc hCc φ hφ
  obtain ⟨om₁, e₀, c, hP₁, he₀, hint⟩ := exists_transfer hK F E σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev
  have hsp := hP₁.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨m₀, hm₀, hinv⟩ := tame_fixed B.ψ hstd.1
    (GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e₀ hP.good hM₁ he₀) φ hφ
  obtain ⟨D, hD, hcond⟩ := adelic_char_denom B.ψ hstd
  obtain ⟨C, hC⟩ := transport_denom M₁.co.e
  obtain ⟨H, hH0, hH⟩ := ht_bdd hCc
  refine ⟨D * m₀ * (max C 0 * H), 1, fun g h hg => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨D * (m₀ * N), Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((D * (m₀ * N) : ℕ) : ℝ) = D * m₀ * N := by push_cast; ring
    rw [this, mul_assoc (D * m₀ : ℝ)]
    refine mul_le_mul_of_nonneg_left (hNle.trans ?_) (by positivity)
    rw [mul_assoc]
    exact mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_right (hH g hg) (NNReal.coe_nonneg _))
      (by positivity) (le_max_right _ _)
  intro f z hz j v
  have hΦ₀ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hΦ : e₀ (pureA F f φ) ∈ schA F (Fin n × Fin d) := he₀.maps _ hΦ₀
  have hz' : om₁ (g, h) (e₀ (pureA F f φ)) z ≠ 0 := by
    intro h0
    apply hz
    rw [hint _ _ hΦ₀, Pi.smul_apply, h0, smul_zero]
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y →
      schr B.ψ (0, y) (om₁ (g, h) (e₀ (pureA F f φ))) = om₁ (g, h) (e₀ (pureA F f φ)) := by
    clear hz hz' hcond hNle hC
    intro y hy
    set w' := M₁.co.e.symm (0, y) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M₁.co.rho B.ψ w (e₀ (pureA F f φ)) = e₀ (pureA F f φ) := hinv f _ _ h1 h2
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w _ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  have key := hcond (((m₀ * N : ℕ) : AF F) * z j) (fun t ht0 ht1 => by
    have e1 := congrFun (hfix _ (isMulInt_single (m₀ * N) j t ht0 ht1)) z
    simp only [schr, dotProduct_single, zero_dotProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero] at e1
    have e2 := (mul_eq_right₀ hz').1 e1
    rw [← e2]
    congr 1
    ring) v
  rwa [← mul_assoc, ← Nat.cast_mul] at key

theorem size_le {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : κ → AF F, 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) ≤
      A * (1 + ‖fun i => evI F (z i)‖) := by
  refine ⟨1 + Fintype.card κ * Fintype.card (InfinitePlace F), by positivity, fun z => ?_⟩
  have h1 : ∀ j (w : InfinitePlace F), mixedEmbedding.normAtPlace w (evI F (z j)) ≤ ‖fun i => evI F (z i)‖ := fun j w => by
    refine le_trans ?_ (norm_le_pi_norm (fun i => evI F (z i)) j)
    by_cases hw : w.IsReal
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  have h2 : ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) ≤
      Fintype.card κ * Fintype.card (InfinitePlace F) * ‖fun i => evI F (z i)‖ := by
    refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ => h1 j w).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have h3 : (0 : ℝ) ≤ Fintype.card κ * Fintype.card (InfinitePlace F) := by positivity
  nlinarith [norm_nonneg fun i => evI F (z i)]

theorem decay_one : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∀ (N : ℕ) (f : SInf F (Fin n × Fin d)), ∃ (k : ℕ) (C : ℝ), ∀ (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F), κ ∈ Cc →
      ‖e (om (κ, h) (pureA F f φ)) z‖ * (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N ≤
        C * (ht h : ℝ) ^ k := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev Cc hCc φ hφ N f
  obtain ⟨om₁, e₀, c, hP₁, he₀, hint⟩ := exists_transfer hK F E σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev
  have hΦ₀ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨C, k, hC⟩ := GlobalTheory.ArchDecay.om_bound_arch F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ _ (he₀.maps _ hΦ₀) N
  obtain ⟨H, hH0, hH⟩ := ht_bdd hCc
  obtain ⟨A, hA0, hA⟩ := size_le (F := F) (κ := Fin n × Fin d)
  refine ⟨k, ‖c‖ * A ^ N * (max C 0 * H ^ k), fun κ h z hκ => ?_⟩
  have hS0 : (0 : ℝ) ≤ 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) :=
    add_nonneg zero_le_one
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg w _)
  have h1 := pow_le_pow_left₀ hS0 (hA z) N
  have h2 : C * ((ht κ : ℝ) * ht h) ^ k ≤ max C 0 * H ^ k * (ht h : ℝ) ^ k := by
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (hH κ hκ) (NNReal.coe_nonneg _)) k) (by positivity) (le_max_right _ _)
  rw [hint _ _ hΦ₀, Pi.smul_apply, smul_eq_mul, norm_mul]
  calc ‖c‖ * ‖om₁ (κ, h) (e₀ (pureA F f φ)) z‖ *
        (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N
      ≤ ‖c‖ * ‖om₁ (κ, h) (e₀ (pureA F f φ)) z‖ * (A * (1 + ‖fun i => evI F (z i)‖)) ^ N :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖c‖ * A ^ N * (‖om₁ (κ, h) (e₀ (pureA F f φ)) z‖ * (1 + ‖fun i => evI F (z i)‖) ^ N) := by
        rw [mul_pow]; ring
    _ ≤ ‖c‖ * A ^ N * (max C 0 * H ^ k * (ht h : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left ((hC κ h z).trans h2) (by positivity)
    _ = _ := by ring

theorem family_bound (F : Type) [Field F] [NumberField F] (κ ι : Type) [Fintype κ] (T : ι → SInf F κ →L[ℂ] ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hT : ∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖T i f‖ ≤ C * w i ^ N) :
    ∃ (N : ℕ) (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ i f, ‖T i f‖ ≤ C * semK κ k f * w i ^ N := by
  obtain ⟨N, C, s, hs⟩ := GlobalTheory.schwartz_family_uniform_bound (κ → mixedEmbedding.mixedSpace F) ι T w hw hT
  set k := s.sup (fun x : ℕ × ℕ => max x.1 x.2)
  have hsub : s ⊆ Finset.Iic (k, k) := fun x hx => Finset.mem_Iic.2
    ⟨le_trans (le_max_left _ _) (Finset.le_sup (f := fun x : ℕ × ℕ => max x.1 x.2) hx),
     le_trans (le_max_right _ _) (Finset.le_sup (f := fun x : ℕ × ℕ => max x.1 x.2) hx)⟩
  refine ⟨N, max C 0, k, le_max_right _ _, fun i f => (hs i f).trans ?_⟩
  have h3 : (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f ≤ semK κ k f :=
    Seminorm.le_def.mp (Finset.sup_mono hsub) f
  exact mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) h3 (apply_nonneg _ _) (le_max_right _ _))
    (pow_nonneg (hw i) _)

theorem major_bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J), κ ∈ Cc →
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧ ∀ z : Fin n × Fin d → AF F,
        ‖e (om (κ, h) (pureA F f φ)) z‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N)⁻¹ ∧
        (e (om (κ, h) (pureA F f φ)) z ≠ 0 → ∀ j (v : Pl F), evFin F v ((m : AF F) * z j) ∈ v.adicCompletionIntegers F) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev Cc hCc φ hφ N
  obtain ⟨C₁, k₁, hsupp⟩ := support_unif hKP F E σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev Cc hCc φ hφ
  have hdec := decay_one hKP F E σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev Cc hCc φ hφ N
  choose T hT using exists_clm_eval F E σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev φ hφ
  set S : (Fin n × Fin d → AF F) → ℝ := fun z =>
    1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) with hSdef
  have hS1 : ∀ z, 1 ≤ S z := fun z => le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg w _)
  have hSp : ∀ z, 0 < S z ^ N := fun z => pow_pos (lt_of_lt_of_le one_pos (hS1 _)) _
  have hht : ∀ h : UA σ W.J, (1 : ℝ) ≤ (ht h : ℝ) := fun h => by
    have := GlobalTheory.AdelicU.one_le_heightGL F h.1
    exact_mod_cast this
  let ι := {p : UA σ X.J × UA σ W.J × (Fin n × Fin d → AF F) // p.1 ∈ Cc}
  let T' : ι → SInf F (Fin n × Fin d) →L[ℂ] ℂ := fun i => ((S i.1.2.2 ^ N : ℝ) : ℂ) • T i.1.1 i.1.2.1 i.1.2.2
  have hT' : ∀ i f, ‖T' i f‖ = ‖e (om (i.1.1, i.1.2.1) (pureA F f φ)) i.1.2.2‖ * S i.1.2.2 ^ N := fun i f => by
    simp only [T', ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hSp _), hT]
    ring
  obtain ⟨k₂, C₃, k₃, hC₃, hBS⟩ := family_bound F (Fin n × Fin d) ι T' (fun i => (ht i.1.2.1 : ℝ))
    (fun i => NNReal.coe_nonneg _) fun f => by
      obtain ⟨k, C, hC⟩ := hdec f
      exact ⟨k, C, fun i => by rw [hT']; exact hC i.1.1 i.1.2.1 i.1.2.2 i.2⟩
  set K := max k₁ (max k₂ k₃)
  refine ⟨max C₁ 0 + C₃, K, fun f κ h hκ => ?_⟩
  obtain ⟨m, hm1, hmC, hmz⟩ := hsupp κ h hκ
  have hhtK : ∀ k, k ≤ K → (ht h : ℝ) ^ k ≤ (ht h : ℝ) ^ K := fun k hk => pow_le_pow_right₀ (hht h) hk
  have hsemK : semK (Fin n × Fin d) k₃ f ≤ semK (Fin n × Fin d) K f := by
    have hsub : Finset.Iic (k₃, k₃) ⊆ Finset.Iic (K, K) := fun x hx => by
      simp only [Finset.mem_Iic] at hx ⊢
      exact le_trans hx (by simp [K, Prod.le_def])
    exact Seminorm.le_def.mp (Finset.sup_mono hsub) f
  have hsem0 : 0 ≤ semK (Fin n × Fin d) k₃ f := apply_nonneg _ _
  have hpos : ∀ k, 0 ≤ (ht h : ℝ) ^ k := fun k => pow_nonneg (NNReal.coe_nonneg _) _
  have hC0 : 0 ≤ max C₁ 0 + C₃ := add_nonneg (le_max_right _ _) hC₃
  refine ⟨m, hm1, ?_, fun z => ⟨?_, fun hz j v => hmz f z hz j v⟩⟩
  · calc (m : ℝ) ≤ C₁ * (ht h : ℝ) ^ k₁ := hmC
      _ ≤ max C₁ 0 * (ht h : ℝ) ^ k₁ := mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos _)
      _ ≤ (max C₁ 0 + C₃) * (ht h : ℝ) ^ K :=
          mul_le_mul (le_add_of_nonneg_right hC₃) (hhtK _ (le_max_left _ _)) (hpos _) hC0
  · have h1 := hBS ⟨(κ, h, z), hκ⟩ f
    rw [hT'] at h1
    refine (le_mul_inv_iff₀ (hSp z)).2 (le_trans h1 ?_)
    refine mul_le_mul ?_ (hhtK _ (le_trans (le_max_left _ _) (le_max_right _ _))) (hpos _)
      (mul_nonneg hC0 (apply_nonneg _ _))
    exact mul_le_mul (le_add_of_nonneg_left (le_max_right _ _)) hsemK hsem0 hC0

end GlobalTheory.ThKTorusBound
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_compact_set_bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J), κ ∈ Cc →
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧ ∀ z : Fin n × Fin d → AF F,
        ‖e (om (κ, h) (pureA F f φ)) z‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N)⁻¹ ∧
        (e (om (κ, h) (pureA F f φ)) z ≠ 0 → ∀ j (v : Pl F), evFin F v ((m : AF F) * z j) ∈ v.adicCompletionIntegers F) := by
  atlas_forward_decl GlobalTheory.ThKTorusBound.major_bound
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.MajCompare

theorem evI_add' (F : Type) [Field F] [NumberField F] (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul' (F : Type) [Field F] [NumberField F] (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_one' (F : Type) [Field F] [NumberField F] : evI F (1 : AF F) = 1 :=
  map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_prod' (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (f : ι → AF F) :
    evI F (∏ i ∈ s, f i) = ∏ i ∈ s, evI F (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evI_one']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, evI_mul', ih]

theorem evI_tAd (F : Type) [Field F] [NumberField F] (s : ℝ) :
    evI F (tAd F s) = algebraMap ℝ (mixedEmbedding.mixedSpace F) s := by
  have h : evI F (realAd F (s - 1)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (s - 1) := by
    simp [evI, realAd]
  rw [tAd, evI_add', evI_one', h, map_sub, map_one]; ring

theorem evI_algMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

theorem evI_blkScale (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ}
    (blk : Fin q → Finset κ) (t : Fin q → ℝ) (ξ : κ → F) (j : κ) :
    evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) =
      (∏ i, if j ∈ blk i then t i else 1) • mixedEmbedding F (ξ j) := by
  simp only [blkScale]
  rw [evI_mul', evI_prod', evI_algMap, Algebra.smul_def, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rw [evI_tAd]
  · rw [evI_one', map_one]

end GlobalTheory.ThKTorus.MajCompare

namespace GlobalTheory.ThKTorus.MajCompare

theorem weight_le_majorant : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) → ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ ξ : κ → F,
      ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) ^ ((q + 1) * N))⁻¹ ≤
        C * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
          (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹ := by
  intro F _ _ κ _ _ q blk hdis c hc N
  set m : ℝ := min c 1 with hm_def
  have hm0 : 0 < m := lt_min hc one_pos
  refine ⟨(m ^ N)⁻¹, inv_nonneg.2 (pow_nonneg hm0.le N), ?_⟩
  intro t ht ξ
  set r : κ → ℝ := fun j => ∏ i, if j ∈ blk i then t i else 1 with hr_def
  set a : κ → ℝ := fun j => ∑ w : InfinitePlace F, w (ξ j) with ha_def
  have ha0 : ∀ j, 0 ≤ a j := fun j => Finset.sum_nonneg fun w _ => apply_nonneg w _
  have hrt : ∀ i, ∀ j ∈ blk i, r j = t i := by
    intro i j hj
    simp only [hr_def]
    rw [Finset.prod_eq_single i]
    · rw [if_pos hj]
    · intro i' _ hi'
      rw [if_neg]
      exact fun hj' => Finset.disjoint_left.1 (hdis i' i hi') hj' hj
    · intro h; exact absurd (Finset.mem_univ i) h
  have hrm : ∀ j, m ≤ r j := by
    intro j
    by_cases h : ∃ i, j ∈ blk i
    · obtain ⟨i, hi⟩ := h
      rw [hrt i j hi]; exact (min_le_left c 1).trans (ht i)
    · push_neg at h
      have : r j = 1 := by
        simp only [hr_def]
        exact Finset.prod_eq_one fun i _ => if_neg (h i)
      rw [this]; exact min_le_right c 1
  have hr0 : ∀ j, 0 < r j := fun j => hm0.trans_le (hrm j)
  have hS : (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w
      (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) = 1 + ∑ j, r j * a j := by
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evI_blkScale, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedEmbedding.normAtPlace_smul, mixedEmbedding.normAtPlace_apply, abs_of_pos (hr0 j)]
  rw [hS]
  set S : ℝ := 1 + ∑ j, r j * a j with hS_def
  have hS1 : 1 ≤ S := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hr0 j).le (ha0 j))
  have hS0 : 0 < S := one_pos.trans_le hS1
  have hA : ∀ i, 1 + t i * ∑ j ∈ blk i, a j ≤ S := by
    intro i
    rw [hS_def, Finset.mul_sum]
    refine add_le_add le_rfl ?_
    calc ∑ j ∈ blk i, t i * a j = ∑ j ∈ blk i, r j * a j :=
          Finset.sum_congr rfl fun j hj => by rw [hrt i j hj]
      _ ≤ ∑ j, r j * a j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j _ _ => mul_nonneg (hr0 j).le (ha0 j)
  have hA0 : ∀ i, 0 ≤ 1 + t i * ∑ j ∈ blk i, a j := fun i =>
    add_nonneg zero_le_one (mul_nonneg (hc.le.trans (ht i)) (Finset.sum_nonneg fun j _ => ha0 j))
  have hB : m * (1 + ∑ j, a j) ≤ S := by
    rw [mul_add, mul_one, Finset.mul_sum, hS_def]
    exact add_le_add (min_le_right c 1) (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hrm j) (ha0 j))
  have hB0 : 0 < 1 + ∑ j, a j := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => ha0 j)
  have hP0 : 0 < (∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N := by
    refine mul_pos (Finset.prod_pos fun i _ => pow_pos ?_ N) (pow_pos hB0 N)
    exact one_pos.trans_le (le_add_of_nonneg_right (mul_nonneg (hc.le.trans (ht i))
      (Finset.sum_nonneg fun j _ => ha0 j)))
  have key : m ^ N * ((∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N) ≤ S ^ ((q + 1) * N) := by
    have h1 : ∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N ≤ S ^ (q * N) := by
      calc ∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N ≤ ∏ _i : Fin q, S ^ N :=
            Finset.prod_le_prod (fun i _ => pow_nonneg (hA0 i) N) fun i _ => pow_le_pow_left₀ (hA0 i) (hA i) N
        _ = S ^ (q * N) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    have h2 : (m * (1 + ∑ j, a j)) ^ N ≤ S ^ N := pow_le_pow_left₀ (mul_nonneg hm0.le hB0.le) hB N
    calc m ^ N * ((∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N)
        = (∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (m * (1 + ∑ j, a j)) ^ N := by rw [mul_pow]; ring
      _ ≤ S ^ (q * N) * S ^ N := mul_le_mul h1 h2 (pow_nonneg (mul_nonneg hm0.le hB0.le) N) (pow_nonneg hS0.le _)
      _ = S ^ ((q + 1) * N) := by rw [← pow_add]; ring_nf
  rw [← mul_inv]
  exact inv_anti₀ (mul_pos (pow_pos hm0 N) hP0) key

end GlobalTheory.ThKTorus.MajCompare
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_scaled_norm_decay : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) → ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ ξ : κ → F,
      ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) ^ ((q + 1) * N))⁻¹ ≤
        C * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
          (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹ := by
  atlas_forward_decl GlobalTheory.ThKTorus.MajCompare.weight_le_majorant
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_scaled_integral_of_local : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ)
    (t : Fin q → ℝ) (m : ℕ) (ξ : κ → F) (j : κ),
    (∀ v : Pl F, evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) ∈ v.adicCompletionIntegers F) →
    IsIntegral ℤ ((m : F) * ξ j) := by
  first | exact @GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem | exact GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem | (intros; apply GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem <;> assumption)
end

section
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem frameMajorant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ A : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc → ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧
        ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N m t ξ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y hxy M₁ blk e hG hco hev Cc hCc c hc φ hφ
  obtain ⟨ex, hex⟩ := GlobalTheory.T.pair_frame_block_eigen_relation hKP F E σ B n d X W M χX χW om r s r' s' hP q x y hxy M₁ blk e hG hco hev φ hφ
  obtain ⟨A, hAex⟩ : ∃ A : ℕ, ∀ i, ex i ≤ A := by
    obtain ⟨A, hA⟩ := exists_nat_ge (∑ i, |ex i|)
    exact ⟨A, fun i => (le_abs_self _).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (ex j)) (Finset.mem_univ i)).trans hA)⟩
  refine ⟨A, fun N => ?_⟩
  obtain ⟨Cb, k, hb⟩ := GlobalTheory.T.evaluation_compact_set_bound hKP F E σ B n d X W M χX χW om r s r' s' hP M₁ e hG hev Cc hCc φ hφ ((q + 1) * N)
  obtain ⟨Cm, hCm0, hCm⟩ := GlobalTheory.T.block_scaled_norm_decay F blk hco.1 c hc N
  set Ct : ℝ := ∏ i, c ^ (ex i - A) with hCt
  have hCt0 : 0 ≤ Ct := Finset.prod_nonneg fun i _ => Real.rpow_nonneg hc.le _
  refine ⟨Cb * max 1 (Ct * Cm), k, ?_⟩
  intro f t a κ h htc ha hκ
  have ht0 : ∀ i, 0 < t i := fun i => hc.trans_le (htc i)
  obtain ⟨m, hm1, hmC, hz⟩ := hb f κ h hκ
  have hhk : 0 ≤ (ht h : ℝ) ^ k := pow_nonneg (NNReal.coe_nonneg _) _
  have hCb : 0 < Cb := by
    by_contra hneg
    push_neg at hneg
    have h2 : Cb * (ht h : ℝ) ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hhk
    have h3 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hmax : 1 ≤ max 1 (Ct * Cm) := le_max_left _ _
  refine ⟨m, hm1, hmC.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCb.le hmax) hhk), fun ξ => ?_⟩
  set z : Fin n × Fin d → AF F := fun j => algebraMap F (AF F) (ξ j) with hzdef
  have h1 := hex t a ht0 ha f κ h z
  have hp : 0 ≤ semK (Fin n × Fin d) k f := apply_nonneg _ _
  by_cases hI : ∀ j, IsIntegral ℤ ((m : F) * ξ j)
  · rw [majI, if_pos hI]
    obtain ⟨hbd, -⟩ := hz (blkScale blk t z)
    have hc' := hCm t htc ξ
    have hprod : (∏ i, t i ^ ex i) ≤ Ct * (∏ i, t i) ^ A := by
      rw [hCt, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (ht0 i).le _) (fun i _ => ?_)
      have e1 : t i ^ ex i = t i ^ (ex i - A) * t i ^ (A : ℝ) := by
        rw [← Real.rpow_add (ht0 i)]; ring_nf
      rw [e1, Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hc (htc i) (by linarith [hAex i])) (pow_nonneg (ht0 i).le _)
    have hW := majW_nonneg blk A N t ξ (fun i => (ht0 i).le)
    have hT : 0 ≤ (∏ i, t i) ^ A := pow_nonneg (Finset.prod_nonneg fun i _ => (ht0 i).le) _
    calc _ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := h1
      _ ≤ (Ct * (∏ i, t i) ^ A) * (Cb * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k *
            ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t z j))) ^ ((q + 1) * N))⁻¹) :=
          mul_le_mul hprod hbd (norm_nonneg _) (mul_nonneg hCt0 hT)
      _ ≤ (Ct * (∏ i, t i) ^ A) * (Cb * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k *
            (Cm * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
              (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc' ?_) (mul_nonneg hCt0 hT)
          exact mul_nonneg (mul_nonneg hCb.le hp) hhk
      _ = Cb * (Ct * Cm) * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majW blk A N t ξ := by
          unfold majW; ring
      _ ≤ Cb * max 1 (Ct * Cm) * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majW blk A N t ξ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hCb.le) hp) hhk) hW
  · have h0 : e (om (κ, h) (pureA F f φ)) (blkScale blk t z) = 0 := by
      by_contra hne
      exact hI fun j => GlobalTheory.T.block_scaled_integral_of_local F blk t m ξ j fun v => (hz _).2 hne j v
    rw [majI, if_neg hI, mul_zero]
    rw [h0, norm_zero, mul_zero] at h1
    exact h1

end GlobalTheory.ThKTorus
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_weil_action_pure_tensor_le_majorant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ A : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc → ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧
        ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N m t ξ := by
  atlas_forward_decl GlobalTheory.ThKTorus.frameMajorant
end
