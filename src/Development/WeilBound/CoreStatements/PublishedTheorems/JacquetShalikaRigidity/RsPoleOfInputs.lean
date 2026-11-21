import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.QuadraticTransferReal
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.BaseRankDimension
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CornerEmbeddingGL
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnBlockEquiv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UnipotentMeasureProperties
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UnipotentBlockMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralVecSmul
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.MeasureInverseInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableInnerIBlkU
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.FundamentalDomainCentre
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.VolumeShellOf
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TableDegreeThreeBase
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PrimePairSetFirst
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PrimePairSetSecond
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CubicPeriodConstant
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.WeightCoefficients
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.HeightParamNonneg
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CuspDecayShortRow
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.DeterminantHeight
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SeparatedThetaSum
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ThetaDecayingFunction
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.EuclideanHeightMul
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.RowsCompactSum
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ExponentialDecomposition
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TorusPowerExponential
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogNormEstimates
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.HeightBoundSetup
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogBallEstimates
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SquareIntegralBound
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LocalAlgebraPowers
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PsiDeterminantFlag
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SmoothVectorHyp
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.WeightInverseContinuity
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphericalIntegralStep
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.BlockInfGL
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UpperBlockProducts
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.BlockMirrorMap
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TransformEmbeddingBlocks
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.NormAverageBound
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.HeightDropSingle
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LastRowIntegral
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UnipotentZeroOfLevel
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelLessSecondOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportEtaOf
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PoissonCutoffAlgebra
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelEqualityFirstOf
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelEqualitySecondOf
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CuspOrthogonalityOf
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferFirst

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem swap3 {μ ν ρ : Measure G} [SFinite μ] [SFinite ν] [SFinite ρ] (K : G → G → G → ℝ≥0∞)
    (hK : Measurable fun p : G × G × G => K p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, K r h g ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, K r h g ∂μ ∂ν ∂ρ := by
  have hF : Measurable (Function.uncurry fun g r => ∫⁻ h, K r h g ∂ν) := by
    have : Measurable fun q : (G × G) × G => K q.1.2 q.2 q.1.1 :=
      hK.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hK' : Measurable (Function.uncurry fun g h => K r h g) :=
    hK.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  exact lintegral_lintegral_swap hK'.aemeasurable

theorem main (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H) (hβ : IsWt ν β)
    (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1) (Φ : G → ℝ≥0∞)
    (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm : Measurable β := hβ.1
  have hH' : ∀ᵐ h ∂ν, h⁻¹ ∈ H := by
    have hH2 := hH
    rw [← hinv] at hH2
    exact ae_of_ae_map measurable_inv.aemeasurable hH2
  have hinvβ : ∀ g, ∫⁻ h, β (h⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h : G => β (h * g) := by fun_prop
    rw [show (∫⁻ h, β (h⁻¹ * g) ∂ν) = ∫⁻ h, β (h * g) ∂(Measure.map (fun h => h⁻¹) ν) from
      (lintegral_map hm measurable_inv).symm, hinv]
    exact hβ.2 g
  calc ∫⁻ g, Φ g ∂μ.withDensity β
      = ∫⁻ g, β g * Φ g ∂μ := lintegral_withDensity_eq_lintegral_mul _ hβm hΦ
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hm1 : ∀ r, Measurable fun h => β₁ (r⁻¹ * h * g) := fun r => by fun_prop
        have hm2 : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        calc β g * Φ g = β g * Φ g * ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ := by rw [h1 g, mul_one]
          _ = _ := by
            rw [← lintegral_const_mul _ hm2]
            refine lintegral_congr fun r => ?_
            rw [lintegral_const_mul _ (hm1 r)]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 (fun r h g => β g * Φ g * β₁ (r⁻¹ * h * g))
          (show Measurable fun p : G × G × G => β p.2.2 * Φ p.2.2 * β₁ (p.1⁻¹ * p.2.1 * p.2.2) by fun_prop)
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae (hH'.mono fun h hh => ?_)
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => β x * Φ x * β₁ (r⁻¹ * h * x)) h⁻¹).symm.trans
          (lintegral_congr fun g => ?_)
        show β (h⁻¹ * g) * Φ (h⁻¹ * g) * β₁ (r⁻¹ * h * (h⁻¹ * g)) = _
        rw [hΦH _ hh, mul_assoc r⁻¹ h, mul_inv_cancel_left]
    _ = ∫⁻ r, ∫⁻ g, ∫⁻ h, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂ν ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        exact lintegral_lintegral_swap
          (show Measurable fun p : G × G => β (p.1⁻¹ * p.2) * Φ p.2 * β₁ (r⁻¹ * p.2) by fun_prop).aemeasurable
    _ = ∫⁻ r, ∫⁻ g, Φ g * β₁ (r⁻¹ * g) ∂μ ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun g => ?_
        simp_rw [mul_assoc]
        rw [lintegral_mul_const _ (show Measurable fun h : G => β (h⁻¹ * g) by fun_prop), hinvβ g, one_mul]
    _ = ∫⁻ r, ∫⁻ g, Φ (r * g) * β₁ g ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * β₁ (r⁻¹ * x)) r).symm.trans
          (lintegral_congr fun g => ?_)
        show Φ (r * g) * β₁ (r⁻¹ * (r * g)) = _
        rw [inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) * β₁ g ∂ρ ∂μ :=
        lintegral_lintegral_swap
          (show Measurable fun p : G × G => Φ (p.1 * p.2) * β₁ p.2 by fun_prop).aemeasurable
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
        have hm : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
          have : Measurable fun p : G × G => Φ (p.2 * p.1) := by fun_prop
          exact this.lintegral_prod_right'
        rw [lintegral_withDensity_eq_lintegral_mul _ hβ₁ hm]
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (show Measurable fun r : G => Φ (r * g) by fun_prop)]
        exact mul_comm _ _

end QuadraticTransferFirst

theorem isUnit_last_join : Q1 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH
  exact QuadraticTransferFirst.main μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace VectorMeasureTranspose

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def trM (g : GA E k) : GA E k :=
  ⟨(g.val)ᵀ, (g⁻¹.val)ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem det_trM (g : GA E k) : GeneralLinearGroup.det (trM g) = GeneralLinearGroup.det g := by
  exact Units.ext (Matrix.det_transpose g.val)

theorem Dt_trM (g : GA E k) : Dt (trM g) = Dt g := by
  unfold Dt
  rw [det_trM]

theorem vecMeasure_eq : vecMeasure E (Fin k) = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := rfl

theorem vecMul_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val := GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g
  have e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) =
      ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := lintegral_map hF hm
  have h := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  unfold Dt
  rw [vecMeasure_eq, ← e1, h, lintegral_smul_measure]
  try rw [smul_eq_mul]

theorem mulVec_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val) := fun x => by
    show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)
    rw [Matrix.vecMul_transpose]
  refine (lintegral_congr e).trans ?_
  rw [vecMul_eq (trM g) F hF, Dt_trM]

end VectorMeasureTranspose

theorem linear_change_variables_of : D0 → AdelicLinearChange := by
  intro _ E _ _ _ k g F hF
  exact ⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩

end PositivityTheory.AdelicQuotientData

end
end

section
namespace PositivityTheory.AdelicQuotientData

theorem nm_agrees_with_twisted_norm_sigmaGL : D0 → jumpWindows.G0 → N2 := @GlobalTheory.CompanionTheory.UnipotentNormalizer.main

end PositivityTheory.AdelicQuotientData
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace CosetIntegralMeasure

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem meas_mul (g : GA E k) : Measurable (fun h : GA E k => g * h) := by
  exact measurable_const_mul g

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  exact lintegral_map hF (meas_mul _)

end CosetIntegralMeasure

open CosetIntegralMeasure in
theorem coset_integration_of : N0 → N1 → N3 → CosetIntegralParabolic := by
  intro h0 _ _ E _ _ _ k j hj1 hjk F hF
  obtain ⟨hgam, huniq, hmul, hinv, -, hmir, -⟩ := h0 E k j hj1 hjk
  have hd : k - (j - 1 + 1) = k - j := by omega
  let f : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)) →
      ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) := fun x =>
    ⟨(gam x.1)⁻¹ * (x.2 : GL (Fin k) E), hmul (gam x.1)⁻¹ (x.2 : GL (Fin k) E) (hinv (gam x.1) (hgam x.1).1)
      (hmir (x.2 : GL (Fin k) E) x.2.2).2⟩
  have hinj : Function.Injective f := by
    rintro ⟨ξ, p⟩ ⟨ξ', p'⟩ h
    have hv : (gam ξ)⁻¹ * (p : GL (Fin k) E) = (gam ξ')⁻¹ * (p' : GL (Fin k) E) := congrArg Subtype.val h
    have hB : GlobalTheory j ((gam ξ)⁻¹ * (p : GL (Fin k) E))⁻¹ := hinv ((gam ξ)⁻¹ * (p : GL (Fin k) E)) (f (ξ, p)).2
    obtain ⟨q, -, huq⟩ := huniq _ hB
    have e1 : (ξ, (p : GL (Fin k) E)⁻¹) = q :=
      huq (ξ, (p : GL (Fin k) E)⁻¹) ⟨(hmir (p : GL (Fin k) E) p.2).1, by simp only [_root_.mul_inv_rev, inv_inv]⟩
    have e2 : (ξ', (p' : GL (Fin k) E)⁻¹) = q :=
      huq (ξ', (p' : GL (Fin k) E)⁻¹) ⟨(hmir (p' : GL (Fin k) E) p'.2).1, by simp only [hv, _root_.mul_inv_rev, inv_inv]⟩
    have h3 := Prod.mk.inj (e1.trans e2.symm)
    exact Prod.ext h3.1 (Subtype.ext (inv_injective h3.2))
  have hsurj : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    obtain ⟨⟨ξ, q⟩, ⟨hq, heq⟩, -⟩ := huniq γ⁻¹ (hinv γ hγ)
    have hq' : IsMir (j - 1) q := hq
    have heq' : γ⁻¹ = q * gam ξ := heq
    refine ⟨(ξ, ⟨q⁻¹, (hmir q hq').1⟩), Subtype.ext ?_⟩
    show (gam ξ)⁻¹ * q⁻¹ = γ
    rw [← _root_.mul_inv_rev, ← heq', inv_inv]
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hR : ∀ ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) =
      ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
        ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
    intro ξ
    have e0 := lint_nuG {γ : GL (Fin k) E | IsMir (j - 1) γ} (k - (j - 1 + 1))
      (fun h => F ((ratGL E k (gam ξ))⁻¹ * h)) (hF.comp (meas_mul _))
    refine e0.trans ?_
    rw [hd]
    refine tsum_congr fun p => ?_
    simp only [map_mul, map_inv, mul_assoc]
  calc ∫⁻ h, F h ∂nuB E k j
      = ∑' γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j) := lint_nuG {γ : GL (Fin k) E | GlobalTheory j γ} (k - j) F hF
    _ = ∑' x : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam x.1)⁻¹ * (x.2 : GL (Fin k) E)) * h) ∂nuD E k (k - j) :=
        (e.tsum_eq (fun γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) =>
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j))).symm
    _ = ∑' ξ : RowT E k j, ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
        exact ENNReal.tsum_prod (f := fun (ξ : RowT E k j) (p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E))) =>
            ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j))
    _ = ∑' ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) :=
        tsum_congr fun ξ => (hR ξ).symm

end PositivityTheory.AdelicQuotientData

end
end

section
namespace PositivityTheory.AdelicQuotientData

theorem one_more_column_of : D0 → N0 → N1 → N3 → ColumnConjugationMeasure → OneMoreAdelicColumn := @GlobalTheory.CompanionTheory.RS.ColN.one_more_column

end PositivityTheory.AdelicQuotientData
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace tableDegreeOneUnipotent

theorem mul_le_sq_add (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

theorem integ {X : Type} [MeasurableSpace X] {ν : Measure X} {f φ : X → ℂ}
    (hf : AEStronglyMeasurable f ν) (hφ : AEStronglyMeasurable φ ν)
    (h1 : ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν < ∞) (h2 : ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun g => f g * conj (φ g)) ν := by
  refine ⟨hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable hφ), ?_⟩
  show ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν < ∞
  calc ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν ≤ ∫⁻ g, (‖f g‖ₑ ^ 2 + ‖φ g‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun g => ?_
        have hc : ‖conj (φ g)‖ₑ = ‖φ g‖ₑ := by simp [enorm_eq_nnnorm]
        rw [enorm_mul, hc]
        exact mul_le_sq_add _ _
    _ = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν + ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν := lintegral_add_left' (hf.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem pre_of_good {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ} {m : ℕ}
    {f : GA E k → ℂ} (h : Good ψ m f) : Pre ψ m f :=
  ⟨h.cont, h.left, h.law⟩

theorem main (hU1 : U1) (hP1 : P1) (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ)
    (μ : Measure (GA E k)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ) (hψ : StdPsi ψ) :
    ∀ m, m < k → ∀ β, IsWt (nuP E k m) β → ∃ β', IsWt (nuP E k 0) β' ∧
      ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        Integrable (fun g => whit ψ m f g * conj (whit ψ m φ g)) (μ.withDensity β') ∧
        ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, whit ψ m f g * conj (whit ψ m φ g) ∂μ.withDensity β' := by
  intro m
  induction m with
  | zero =>
    intro _ β hβ
    refine ⟨β, hβ, fun f φ hf hφ h1 h2 => ⟨?_, rfl⟩⟩
    exact integ hf.cont.aestronglyMeasurable (pre_of_good hφ).cont.aestronglyMeasurable h1 h2
  | succ m ih =>
    intro hm β hβ
    obtain ⟨β1, hβ1, hL2, hip⟩ := hU1 E k μ ψ hψ (m + 1) (by omega) hm β hβ
    obtain ⟨β', hβ', h⟩ := ih (by omega) β1 hβ1
    refine ⟨β', hβ', fun f φ hf hφ h1 h2 => ?_⟩
    have hf' : Pre ψ m (colT ψ (m + 1) f) := (hP1 E k ψ hψ (m + 1) (by omega) hm f hf).1
    have hφ' : Good ψ m (colT ψ (m + 1) φ) := GlobalTheory.CuspRep.Generic.good_colT hψ hm hφ
    obtain ⟨hi, he⟩ := h _ _ hf' hφ' ((hL2 f hf).trans_lt h1) ((hL2 φ (pre_of_good hφ)).trans_lt h2)
    exact ⟨hi, (hip f φ hf hφ h1 h2).trans he⟩

end tableDegreeOneUnipotent

theorem unitaryGroupGeometricSide_of_quotient_identities : U1 → P1 → U2 := by
  intro hU1 hP1 E _ _ _ k μ _ ψ hψ
  exact tableDegreeOneUnipotent.main hU1 hP1 E k μ ψ hψ

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RhoSigmaFinite

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]

variable (E k) in

def rho : Measure (GA E k) := Measure.sum fun ξ : RowT E k k => Measure.dirac (ratGL E k (gam ξ))

omit [IsTotallyComplex E] in
theorem rho_sFinite [Countable (RowT E k k)] : SFinite (rho E k) := by
  rw [rho]; infer_instance

omit [IsTotallyComplex E] in
theorem lint_rho (F : GA E k → ℝ≥0∞) : ∫⁻ r, F r ∂rho E k = ∑' ξ : RowT E k k, F (ratGL E k (gam ξ)) := by
  rw [rho, lintegral_sum_measure]
  simp only [lintegral_dirac]

omit [IsTotallyComplex E] in
theorem int_rho (Φ : GA E k → ℂ) (hΦ : Measurable Φ) (g : GA E k) :
    ∫ r, Φ (r * g) ∂rho E k = sumF Φ g := by
  by_cases hi : Integrable (fun r => Φ (r * g)) (rho E k)
  · rw [rho, integral_sum_measure hi, sumF]
    simp only [integral_dirac]
  · rw [integral_undef hi, sumF, tsum_eq_zero_of_not_summable]
    intro hs
    apply hi
    refine ⟨(hΦ.comp (measurable_mul_const g)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lint_rho]
    have h1 : Summable fun ξ : RowT E k k => ‖Φ (ratGL E k (gam ξ) * g)‖₊ :=
      NNReal.summable_coe.mp (by simpa using hs.norm)
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mpr h1
    simpa [enorm_eq_nnnorm] using h2.lt_top

end RhoSigmaFinite

open RhoSigmaFinite in
set_option synthInstance.maxHeartbeats 400000 in
theorem unipotent_integral_of : Q1 → Q2 → N0 → N3 → CosetIntegralParabolic → U0 := by
  intro hQ1 hQ2 hN0 hN3 hN4a E _ _ _ k μ _ hk β hβ
  have : Countable (RowT E k k) := (hN0 E k k hk le_rfl).2.2.2.2.2.2.1
  have : SFinite (rho E k) := rho_sFinite
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).1 (k - 1) (by omega)
  have key : ∀ g, ∑' ξ : RowT E k k, ∫⁻ h, β ((ratGL E k (gam ξ))⁻¹ * h * g) ∂nuP E k (k - 1) = 1 := by
    intro g
    rw [← hN4a E k k hk le_rfl (fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g))]
    exact hβ.2 g
  set β' : GA E k → ℝ≥0∞ := fun g => ∑' ξ : RowT E k k, β ((ratGL E k (gam ξ))⁻¹ * g) with hβ'
  have hwt : IsWt (nuP E k (k - 1)) β' := by
    refine ⟨Measurable.ennreal_tsum fun ξ => hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_tsum (f := fun ξ h => β ((ratGL E k (gam ξ))⁻¹ * (h * g)))
      fun ξ => (hβ.1.comp ((measurable_const_mul _).comp (measurable_mul_const g))).aemeasurable]
    simpa only [mul_assoc] using key g
  have hH : ∀ᵐ h ∂nuP E k (k - 1), h ∈ {x : GA E k | ∃ γ, IsMir (k - 1) γ ∧ ratGL E k γ = x} := by
    filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
    rw [hh, uu_eq_one (by omega) hu, mul_one]
    exact ⟨γ, hγ, rfl⟩
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k (k - 1) ∂rho E k = 1 := fun g => by
    rw [lint_rho]; exact key g
  refine ⟨β', hwt, fun Φ hΦ hΦi => ?_, fun Φ hΦ hΦi hint => ?_⟩
  · have := hQ1 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g)
    rw [this]
    simp only [lint_rho]
  · have := (hQ2 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g) hint).2
    rw [this]
    simp only [int_rho Φ hΦ]

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace AdmissibleVectors

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
theorem map_wd (μ : Measure (GA E k)) [μ.IsHaarMeasure] (β : GA E k → ℝ≥0∞) (t : GA E k) :
    Measure.map (MeasurableEquiv.mulLeft t⁻¹) (μ.withDensity β) = μ.withDensity fun g => β (t * g) := by
  ext s hs
  rw [Measure.map_apply (MeasurableEquiv.mulLeft t⁻¹).measurable hs,
    withDensity_apply _ ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), ← lintegral_indicator hs]
  rw [← lintegral_mul_left_eq_self (μ := μ) _ t]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

end AdmissibleVectors

open AdmissibleVectors in
set_option synthInstance.maxHeartbeats 400000 in
theorem sum_wt_mul_massS_le_inv_pow_mul_total_mass : Q1 → Q2 → N2 → N3 → C1 := by
  intro _ hQ2 hN2 hN3 E _ _ _ k μ _ hk β hβ w l Φ hΦ hΦu hint
  set t := fl k w (Iwasawa.torusPow (w.adicCompletion E) k l) with ht
  obtain ⟨hsf, hinv, -⟩ := (hN3 E k).1 0 (by omega)
  have := hsf
  obtain ⟨hUU, -⟩ := (hN3 E k).2.2.2 hk
  have hq0 : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set c : ℝ≥0∞ := ENNReal.ofReal ((Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l) with hc
  have hcpos : 0 < (Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l :=
    zpow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hq0)) _
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hcpos).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ0m : Measurable fun g => β (t * g) := hβ.1.comp (measurable_const_mul t)
  set β' : GA E k → ℝ≥0∞ := fun g => c⁻¹ * β (t * g) with hβ'
  have hβ'm : Measurable β' := hβ0m.const_mul _
  have hwt : IsWt (nuP E k 0) β' := by
    refine ⟨hβ'm, fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_const_mul c⁻¹ (f := fun h => β (t * (h * g))) (hβ0m.comp (measurable_mul_const g))]
    have := hN2 E k w l (fun h => β (h * (t * g))) (hβ.1.comp (measurable_mul_const _))
    rw [← ht] at this
    simp only [mul_assoc, inv_mul_cancel_left] at this
    rw [this, hβ.2 (t * g), mul_one, ENNReal.inv_mul_cancel hc0 hctop]

  have hH : ∀ᵐ h ∂nuP E k 0, h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)} := by
    set A := {h : GA E k | ¬ UU 0 h}
    have hA : nuP E k 0 A = 0 := ae_iff.1 hUU
    set S := toMeasurable (nuP E k 0) A
    have hS : MeasurableSet S := measurableSet_toMeasurable _ _
    have hS0 : nuP E k 0 S = 0 := by rw [measure_toMeasurable]; exact hA
    have hcm : Measurable fun h : GA E k => t * h * t⁻¹ := (measurable_const_mul t).mul_const _
    have := hN2 E k w l (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS, hS0, mul_zero] at this
    have h2 := (lintegral_eq_zero_iff ((measurable_one.indicator hS).comp hcm)).1 this
    filter_upwards [h2] with h hh
    by_contra hn
    have : t * h * t⁻¹ ∈ S := subset_toMeasurable _ _ hn
    simp [Set.indicator_of_mem this] at hh
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k 0 ∂Measure.dirac (1 : GA E k) = 1 := fun g => by
    rw [lintegral_dirac]; simpa using hβ.2 g
  have hΦ'm : Measurable fun g => Φ (t * g) := hΦ.comp (measurable_const_mul t)
  have hΦ'H : ∀ h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)}, ∀ g, Φ (t * (h * g)) = Φ (t * g) := by
    intro h hh g
    have := hΦu _ hh (t * g)
    simpa [mul_assoc] using this
  have hmap := map_wd μ β t
  have hsm : μ.withDensity (fun g => β (t * g)) = c • μ.withDensity β' := by
    rw [← withDensity_smul _ hβ'm]
    congr 1
    funext g
    simp only [hβ', Pi.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
  have hint0 : Integrable (fun g => Φ (t * g)) (μ.withDensity fun g => β (t * g)) := by
    rw [← hmap, integrable_map_equiv]
    simpa [Function.comp_def] using hint
  have hint' : Integrable (fun g => Φ (t * g)) (μ.withDensity β') := by
    have h1 : μ.withDensity β' = c⁻¹ • μ.withDensity (fun g => β (t * g)) := by
      rw [hsm, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
    rw [h1]
    exact hint0.smul_measure (ENNReal.inv_ne_top.2 hc0)
  have hQ := hQ2 (GA E k) μ (nuP E k 0) (Measure.dirac 1) _ β' β hinv hH hwt hβ.1 hone
    (fun g => Φ (t * g)) hΦ'm hΦ'H hint'
  simp only [integral_dirac, one_mul] at hQ
  refine ⟨hQ.1, ?_⟩
  have e1 : ∫ g, Φ g ∂μ.withDensity β = ∫ g, Φ (t * g) ∂μ.withDensity fun g => β (t * g) := by
    rw [← hmap, integral_map_equiv]
    simp [MeasurableEquiv.coe_mulLeft]
  rw [e1, hsm, integral_smul_measure, hQ.2, hc, ENNReal.toReal_ofReal hcpos.le, Complex.real_smul]
  push_cast
  rfl

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

section PK7

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.UG Formalism.L2.Host

theorem local_unramified_of : JacquetShalikaLocal.L7 → JacquetShalikaLocal.lift_levelP_alt₂ → jumpWindows.G0 → jumpWindows.G5 → K7 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc
  refine ⟨WeilJacquetShalikaLaw.psiW ψ w, WeilJacquetShalikaLaw.psiOK hψ hc, fun y => rfl, ?_⟩
  intro z φ hφ hsat h hh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · have h0 : ∀ g, Wh ψ (0 : XB E a) g = 0 := fun g => by
      obtain ⟨Λ, hΛ'⟩ := hΛ g
      rw [← hΛ' 0 hφ, map_zero]
    rw [h0, h0, zero_mul]
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w a, Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = Wh ψ φ h := by
    change Wh ψ φ (h * fl a w 1) = _
    rw [map_one, mul_one]
  by_cases h0 : vs = 0
  · have e : ∀ x, (vs : GL (Fin a) (w.adicCompletion E) → ℂ) x = 0 := fun x =>
      congrFun (congrArg Subtype.val h0) x
    have e1 : Wh ψ φ (h * fl a w u) = 0 := e u
    rw [e1, ← hv1, e 1, zero_mul]
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w a,
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w a)
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1] at this
  exact this

end PK7

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LevelScalarAction

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lev_smul {S : Finset (Pl E)} {x : XB E k} (h : Lev S x) (c : ℂ) : Lev S (c • x) := by
  intro w hw
  filter_upwards [h w hw] with u hu
  have hu' : repW k w u x = x := hu
  change repW k w u (c • x) = c • x
  rw [map_smul, hu']

end LevelScalarAction

theorem global_level_of : jumpWindows.G0 → jumpWindows.G1 → jumpWindows.AlmostEverywhereSpherical → jumpWindows.G2c → jumpWindows.G5 → K8 → K9 := by
  intro hG0 hG1 hG1b hG2c hG5 hK8 E _ _ _ k _ ψ hψ hcond π hπ
  obtain ⟨φ₀, hφ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨x₀, hx₀, -, hlev⟩ := hG1 E k π hπ φ₀ hφ₀
  have hev := hcond.and (hG1b E k π hπ φ₀ hφ₀ x₀ hx₀)
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, fun S hS => ?_⟩
  have hoff : ∀ w, w ∉ S → Cond ψ w ∧ ∀ B, (CG.mk π).HasSat w B → SatFn w B x₀ := by
    intro w hw
    by_contra hc
    exact hw (hS ((Set.Finite.mem_toFinset _).2 hc))
  refine ⟨fun w hw => (hoff w hw).1, fun α hα => ?_⟩
  have hgood : Good ψ (k - 1) (x₀ : GA E k → ℂ) := by
    rw [hx₀]; exact GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E k ψ φ₀ (π.cusp _ hφ₀)
  have hx0 : x₀ ≠ 0 := by
    intro h
    subst h
    exact hne (Subtype.ext (by rw [← hx₀]; rfl))
  obtain ⟨g, hg⟩ := ((hG5 E k ψ hψ).2.2.2 x₀ hgood).2.1 hx0
  have hsat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) x₀ := fun w => (hoff w.1 w.2).2 _ (hα w)
  obtain ⟨g₀, h1, h2, h3⟩ := (hG0 E k).2.2.2.2.2.2.2.2.2.2.1 S g
  have hne0 : Wh ψ x₀ g₀ ≠ 0 :=
    ((hK8 E k ψ hψ S (fun w hw => (hoff w hw).1) α x₀ hgood hsat).2.2 g hg).1 g₀ h1 h2 h3
  refine ⟨(Wh ψ x₀ g₀)⁻¹ • φ₀, π.V.smul_mem _ hφ₀, g₀, (Wh ψ x₀ g₀)⁻¹ • x₀, h3, ?_, ?_, LevelScalarAction.lev_smul (hlev S) _, ?_⟩
  · funext y
    change (Wh ψ x₀ g₀)⁻¹ * x₀ y = (Wh ψ x₀ g₀)⁻¹ * φ₀.1 y
    rw [hx₀]
  · intro w
    obtain ⟨Y, -, -, hY⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hY _).1 (Y.smul_mem _ ((hY x₀).2 (hsat w)))
  · rw [(hG5 E k ψ hψ).2.1, one_mul]
    change whit ψ (k - 1) (fun y => (Wh ψ x₀ g₀)⁻¹ * x₀ y) g₀ = 1
    rw [GlobalTheory.CuspRep.Generic.whit_smul]
    exact inv_mul_cancel₀ hne0

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKIR

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

theorem ht_nonneg (g : GA E k) (ξ : Fin k → E) : 0 ≤ ht g ξ :=
  div_nonneg (height_nonneg _ _) (Real.rpow_nonneg (dt_pos g).le _)

theorem dmin_nonneg (g : GA E k) : 0 ≤ dmin g := by
  unfold dmin
  exact Real.iInf_nonneg fun ξ => ht_nonneg g ξ.1

theorem wt_nonneg (M : ℕ) (g : GA E k) : 0 ≤ wt M g := by
  unfold wt
  exact pow_nonneg (le_min zero_le_one (dmin_nonneg g)) M

end PKIR

theorem kir_of : jumpWindows.S2 → jumpWindows.G0 → jumpWindows.G2a → jumpWindows.G2c → jumpWindows.G5 → jumpWindows.G5b → K2 → K3 → K4 → K9 → KIR := by
  intro hS2 hG0 hG2a hG2c _hG5 hG5b hK2 hK3 hK4 hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS α hα M j hj U hU Y hYc hYi hYπ => ?_⟩
  obtain ⟨_hcond, h9⟩ := hS₀ S hS
  obtain ⟨φ, hφ, h, x, hhS, hx, hsat, hlev, hwh⟩ := h9 α hα
  obtain ⟨ρ, J, hW, hsm⟩ := hK2 E k hk M
  obtain ⟨x₀, hx₀, hsm₀⟩ := hK3 E k hk M ρ J hW π hπ φ hφ
  have hJx₀ : J x₀ = x := DFunLike.coe_injective (hx₀.trans hx.symm)

  obtain ⟨_, _, _, hSg, hST, _⟩ := hS2 _ k (XB E k) (ρ.comp (infGL E k)) hW.poly
  obtain ⟨g1, g2, _, _, _, _, g7, _⟩ := hG0 E k
  have hsm1 : SmV (ρ.comp (infGL E k)) (ρ h x₀) := by
    set y := cInf h
    set hf := (infGL E k y)⁻¹ * h
    have hcf : cInf hf = 1 := by simp only [hf, map_mul, map_inv, g1, y, inv_mul_cancel]
    have hc : ∀ (g : GL (Fin k) (Cinf E)) z, ρ hf ((ρ.comp (infGL E k)) g z) = (ρ.comp (infGL E k)) g (ρ hf z) := by
      intro g z
      simp only [MonoidHom.comp_apply]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, g7 hf hcf g, map_mul, ContinuousLinearMap.mul_apply]
    have := hSg y _ (hST (ρ hf) hc x₀ hsm₀)
    simpa only [MonoidHom.comp_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, hf, mul_inv_cancel_left] using this

  obtain ⟨Yg, hYgc, hYgi, hYgm⟩ := hG2a E k ψ hψ
  have hw := fun w : Off E S => hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
  choose Yw hYwc hYwi hYwm using hw
  set Y' : Submodule ℂ (XB E k) := Y ⊓ Yg ⊓ ⨅ w, Yw w with hY'
  have hmem : ∀ z, z ∈ Y' ↔ (z ∈ Y ∧ z ∈ Yg) ∧ ∀ w, z ∈ Yw w := fun z => by
    simp only [Y', Submodule.mem_inf, Submodule.mem_iInf]
  have hYOK : YOK ψ S Y' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.coe_inf, Submodule.coe_inf, Submodule.coe_iInf]
      exact (hYc.inter hYgc).inter (isClosed_iInter hYwc)
    · intro g hg z hz
      rw [hmem] at hz ⊢
      exact ⟨⟨hYi g z hz.1.1, hYgi g z hz.1.2⟩, fun w => hYwi w g (hg w.1 w.2) z (hz.2 w)⟩
    · intro z hz
      exact ((hYgm z).1 ((hmem z).1 hz).1.2).1
  have hcusp := π.cusp φ hφ
  have hxY' : Rt E k h x ∈ Y' := by
    have hxg : x ∈ Yg := by
      refine (hYgm x).2 ⟨?_, fun γ g => ?_⟩
      · rw [hx]; exact GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E k ψ φ hcusp
      · rw [congrFun hx, congrFun hx]; exact hcusp.1.left γ g
    rw [hmem]
    exact ⟨⟨hYi h x (hYπ x ⟨φ, hφ, hx⟩), hYgi h x hxg⟩,
      fun w => hYwi w h (hhS w.1 w.2) x ((hYwm w x).2 (hsat w))⟩
  have hJ1 : J (ρ h x₀) = Rt E k h x := by rw [hW.inter, hJx₀]
  obtain ⟨x', C, hCU, hx'Y, hsm', hlev', hBlk, hBump⟩ := hK4 E k (wt M) ρ J hW ψ hψ S Y' hYOK j hj U hU (ρ h x₀)
    (hJ1 ▸ hxY') hsm1 (hJ1 ▸ (hG5b E k S).2.1 h x hlev) (hJ1 ▸ hwh)
  obtain ⟨⟨hx'1, hx'2⟩, hx'3⟩ := (hmem _).1 hx'Y
  obtain ⟨hgood, hinv⟩ := (hYgm _).1 hx'2
  refine ⟨J x', hx'1, ⟨hgood, hinv, fun w => (hYwm w _).1 (hx'3 w), hsm x' hsm', hlev', ?_, ⟨C, hCU, hBlk, hBump⟩⟩⟩
  refine ⟨‖x'‖, fun g => ?_⟩
  have hw0 := PKIR.wt_nonneg M g
  rw [hW.mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, mul_comm ‖x'‖]
  exact mul_le_mul_of_nonneg_left (x'.norm_coe_le_norm g) hw0

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ksec_of : jumpWindows.G2c → jumpWindows.G5 → CuspDecayShortRowColumn → K9 → KSec := by
  intro hG2c hG5 hG1d hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS => ⟨(hS₀ S hS).1, fun α hα => ?_⟩⟩
  obtain ⟨φ, hφ, h, x, hh, hx, hsat, -, hone⟩ := (hS₀ S hS).2 α hα
  have hval : ∀ g, Rt E k h x g = φ.1 (g * h) := fun g => by rw [Rt_apply, hx]
  have hgood : Good ψ (k - 1) (x : GA E k → ℂ) := by
    rw [hx]; exact good_of_isCuspForm E k ψ φ (π.cusp φ hφ)
  refine ⟨φ, hφ, h, Rt E k h x, hval, ?_⟩
  refine ⟨(hG5 E k ψ hψ).2.2.1 x h hgood, ?_, ?_, ?_, ?_, ?_, hone⟩
  · intro γ g
    rw [hval, hval, mul_assoc]
    exact (π.cusp φ hφ).1.left γ (g * h)
  · intro t g
    rw [hval, hval, mul_assoc]
    exact hπ φ hφ t (g * h)
  · intro w
    obtain ⟨Y, -, hYst, hYmem⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hYmem _).1 (hYst h (hh w.1 w.2) x ((hYmem x).2 (hsat w)))
  · have e : (⇑(Rt E k h x) : GA E k → ℂ) = fun g => φ.1 (g * h) := funext hval
    rw [e]
    exact (hG1d E k hk π hπ φ hφ h).1
  · have := (hG1d E k hk π hπ φ hφ h).2
    simpa only [hval] using this

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ku_of : jumpWindows.G5 → D0 → KU := by
  intro hG hD E _ _ _ k ψ hψ φ u hφ h1
  obtain ⟨-, -, -, hW⟩ := hG E k ψ hψ
  have hWc : Continuous (Wh ψ φ) := (hW φ hφ).1
  obtain ⟨hpos, hmul, hcont, -⟩ := hD E k
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hmul 1 1
    rw [show (1 : GA E k) * 1 = 1 from mul_one 1] at h
    exact mul_left_cancel₀ (hpos 1).ne' (h.symm.trans (mul_one _).symm)
  set F : GA E k → ℂ := fun c => conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I) with hF
  have hDc : Continuous fun c : GA E k => (Dt c : ℂ) := Complex.continuous_ofReal.comp hcont
  have hFc : Continuous F := (Complex.continuous_conj.comp hWc).mul
    (hDc.cpow continuous_const fun c => Complex.ofReal_mem_slitPlane.2 (hpos c))
  have hF1 : F 1 = 1 := by simp [F, h1, hD1]
  refine ⟨{c | Dt c ∈ Set.Ioo (1 / 2 : ℝ) 2} ∩ {c | 0 < (F c).re}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.preimage hcont).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hFc))
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, hD1, hF1]
      norm_num
  · rintro c ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha.le, hb.le, hc⟩

end PositivityTheory.AdelicQuotientData

end
end

section
namespace PositivityTheory.AdelicQuotientData

theorem last_row_cutoff_of : jumpWindows.S4 → jumpWindows.S8 → jumpWindows.G0 → LastRowCutoff := @GlobalTheory.CompanionTheory.CutOff.exists_cut

end PositivityTheory.AdelicQuotientData
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PRSPole

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem bnd (hJS : GlobalTheory.Published.JacquetShalikaBound) {m : ℕ} (π : CuspSub E m) (hπ : IsNormalised π)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (α : Off E S → Fin m → ℂˣ) (hα : SatOff (CG.mk π) S α) :
    ∀ w a, ‖(α w a : ℂ)‖ ≤ Real.sqrt (nq w) := by
  intro w a
  have hu : (CG.mk π).IsUnitary :=
    (CG.isUnitary_mk π).2 (GlobalTheory.Published.CuspFormsBoundedGL.isUnitary GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL hπ)
  have h := (hJS E m (CG.mk π) hu w.1 _ (hα w) (α w a)
    (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
  show ‖((α w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
  rw [Real.sqrt_eq_rpow]
  exact h.le

end PRSPole

open Classical in
theorem rspole_of : GlobalTheory.Published.JacquetShalikaBound → jumpWindows.G1 → jumpWindows.StandardCharacterExists → W0 → E2 → M1 → KIR → KSec → CornerEmbedding → KLt1 → KLt2 → LastRowCutoff → KEq1 → KEq2 → ORT → KY → RSPole := by
  intro hJS _hG1 hG10 hW0 hE2 hM1 hKIR hKSec hK5e hKLt1 hKLt2 hK11 hKEq1 hKEq2 hORT hKY E _ _ _ m k π π' u hk
    hkm hπ hπ'
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  have hm : 1 ≤ m := hk.trans hkm
  obtain ⟨S₁, hS₁⟩ := hKSec E k hk ψ hψ hcond π' hπ'
  obtain ⟨S₂, hS₂⟩ := hKIR E m hm ψ hψ hcond π hπ
  refine ⟨S₁ ∪ S₂, fun S hS α β hα hβ => ?_⟩
  have hS1 : S₁ ⊆ S := Finset.union_subset_left hS
  have hS2 : S₂ ⊆ S := Finset.union_subset_right hS
  obtain ⟨hCond, hsec⟩ := hS₁ S hS1
  obtain ⟨φ₀', hφ₀', h', φ', hφ'e, hsec⟩ := hsec β hβ
  have hαb := PRSPole.bnd hJS π hπ S α hα
  have hβb := PRSPole.bnd hJS π' hπ' S β hβ
  let μ : Measure (GA E k) := Measure.haar
  obtain ⟨⟨b, hb⟩, -⟩ := hW0 E k μ hk
  rcases hkm.lt_or_eq with hlt | heq
  · obtain ⟨ι, hι⟩ := ((hK5e E m k hkm).1 (Ad E))
    obtain ⟨U, hU, hUd⟩ := hKLt1 E m k hk hlt ψ hψ S hCond ι hι α β u φ' hsec
    obtain ⟨φ, -, hprep⟩ := hS₂ S hS2 α hα (m ^ 3) k hlt U hU ⊤ isClosed_univ (fun _ _ _ => trivial)
      (fun _ _ => trivial)
    have hdat := hUd (m ^ 3) (Nat.one_le_pow _ _ hm) φ hprep
    have hgrow := hKLt2 E m k hk hlt ψ hψ S hCond ι hι α β φ' hsec U φ hprep
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S m α β u _ _ hkm hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun _ => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · simp
  · subst heq
    obtain ⟨U, hU, hUd⟩ := hKEq1 E k hk ψ hψ S hCond α β u φ' hsec
    let φ'' : XB E k := if π = π' then 0 else φ'
    obtain ⟨Y, hYc, hYi, hYm, hYz⟩ := hKY E k μ hk b hb φ''
    have hforms : ∀ x : XB E k, (∃ φ ∈ π.V, (x : GA E k → ℂ) = φ.1) → x ∈ Y := by
      rintro x ⟨φ₁, hφ₁, hx⟩
      have hx' : ∀ g, x g = φ₁.1 g := congrFun hx
      refine (hYm x).2 ⟨fun t g => by rw [hx', hx']; exact hπ φ₁ hφ₁ t g, fun h => ?_⟩
      by_cases he : π = π'
      · have e0 : φ'' = 0 := if_pos he
        rw [e0]
        simp
      · have e1 : φ'' = φ' := if_neg he
        have hO := hORT E k μ hk b hb π π' hπ hπ' he φ₁ hφ₁ φ₀' hφ₀' h h'
        rw [e1]
        simp only [hx', hφ'e]
        exact hO
    obtain ⟨φ, hφY, hprep⟩ := hS₂ S hS2 α hα (k + 1) (k - 1) (by omega) U hU Y hYc hYi hforms
    obtain ⟨η, s, hcut⟩ := hK11 E k hk ψ hψ S hCond U hU φ hprep.smooth hprep.lev
    have hdat := hUd φ hprep η s hcut
    have hcen := ((hYm φ).1 hφY).1
    have hgrow := hKEq2 E k hk ψ hψ S β φ' hsec U φ η s hcut hprep.inv hcen
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S k α β u _ _ le_rfl hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun hne => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · have hne' : π ≠ π' := fun e => hne (by rw [e])
      have e1 : φ'' = φ' := if_neg hne'
      have hz := hYz φ hφY ψ S U η s hcut
      rw [e1] at hz
      exact hz

end PositivityTheory.AdelicQuotientData

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem rsPole_of_inputs (eJS2G0 : jumpWindows.G0) (eCAUCHY : CAUCHY) (eJS2S1 : jumpWindows.S1) (eJS1L7 : JacquetShalikaLocal.L7) (eJS1L12 : JacquetShalikaLocal.lift_levelP_alt₂) (eJS2G5 : jumpWindows.G5) (eJS2S7 : jumpWindows.S7) (eJS2S10 : jumpWindows.MirabolicColumnBlock) (eJS2G5b : jumpWindows.G5b) (eJS2S2 : jumpWindows.S2) (eJS2S9 : jumpWindows.S9) (eJS2G1 : jumpWindows.G1) (eJS2G1b : jumpWindows.AlmostEverywhereSpherical) (eJS2G2c : jumpWindows.G2c) (eJS2G2a : jumpWindows.G2a) (eJS2G11 : jumpWindows.FourierUniquenessMirabolic) (eJS2S4 : jumpWindows.S4) (eJS2S8 : jumpWindows.S8) (eJS2G14 : jumpWindows.CuspidalIrreducibleSubrep) (eJS2SmoNorm : jumpWindows.SmoNorm) (eBlkJacquetShalikaBound : GlobalTheory.Published.JacquetShalikaBound) (eJS2G10 : jumpWindows.StandardCharacterExists) : RSPole :=
  have hQ1 : Q1 := isUnit_last_join
  have hQ2 : Q2 := closedSubgroup_cutoff_exists
  have hD0 : D0 := determinant_basic_of_G0 eJS2G0
  have hMOD0 : AdelicLinearChange := linear_change_variables_of hD0
  have hK5e : CornerEmbedding := corner_embedding_of eJS2G0
  have hMOD1 : ColumnConjugationMeasure := algebraic_modulus_one_of_finiteOrder_char hMOD0 hK5e
  have hN0 : N0 := mem_unipotent_fixer_of
  have hN1 : N1 := monic_polynomial_is_matrix_charpoly hD0 hMOD1
  have hN2 : N2 := nm_agrees_with_twisted_norm_sigmaGL hD0 eJS2G0
  have hN3 : N3 := galois_fixed_adelic_matrices_descend hD0 hN0 hN1
  have hN4a : CosetIntegralParabolic := coset_integration_of hN0 hN1 hN3
  have hN4b : OneMoreAdelicColumn := one_more_column_of hD0 hN0 hN1 hN3 hMOD1
  have hW0 : W0 := fundamental_domain_of hQ1 hD0 hN3
  have hV1 : V1 := volume_shell_of hQ1 hQ2 hD0 hN3 hW0
  have hP0 : P0 := poisson_base_holds
  have hP1 : P1 := p1_holds hN0 hP0
  have hP2 : P2 := p2_of hP1
  have hP3 : P3 := crystalline_clause_of_admitted
  have hU1 : U1 := twistedGeometricSide_unfolding hQ1 hQ2 hN0 hN3 hN4a hN4b hP0 hP1 hP2
  have hU2 : U2 := unitaryGroupGeometricSide_of_quotient_identities hU1 hP1
  have hU0 : U0 := unipotent_integral_of hQ1 hQ2 hN0 hN3 hN4a
  have hH0 : H0 := height_change_of_D0 hD0
  have hG1d : CuspDecayShortRowColumn := cusp_decay_short_row_of hD0 hH0
  have hG2m : MinkowskiBoundAlt := minkowski_bound_of hD0
  have hG3t : ThetaSeriesBound := theta_bound_holds
  have hG4t : ThetaDecaying := theta_decaying_of_bound hD0 hN0 hH0 hG3t
  have hK1 : K1 := firstCohomologyBound_of_boundaryBound hD0 hH0
  have hG5t : RowsInCompactSet := rows_compact_of_bound hD0 hN0 hH0 hG3t hK1
  have hC0 : C0 := open_decomposition_of_G0 eJS2G0
  have hC1 : C1 := sum_wt_mul_massS_le_inv_pow_mul_total_mass hQ1 hQ2 hN2 hN3
  have hC2 : C2 := torus_exponential_of_open eJS2G0 hC0 hC1
  have hD1 : D1 := log_norm_estimate_of_Q hQ1 hD0 hN3 hC0
  have hE1 : E1 := height_bound_of_weights hD0 hW0 hV1
  have hE2 : E2 := duality_diagonalClass_of_affineProperBaseChange hD0 hV1 hE1
  have hM0 : M0 := moderate_growth_of hD0 hN0 hP2 hU0 hU2 hV1 hG4t
  have hK8a : LocalHeckeAlgebra := localHeckeAlgebra_statement
  have hM1 : M1 := mean_convergence_of eJS2G0 hD0 hP2 hC0 hC2 hD1 hM0 hK8a eCAUCHY
  have hK2 : K2 := secondCohomologyBound_of_boundaryBound hH0 hK1
  have hK3 : K3 := koszulThree_of_det eJS2S1 hH0 hG1d hK1
  have hK7 : K7 := local_unramified_of eJS1L7 eJS1L12 eJS2G0 eJS2G5
  have hK8 : K8 := spherical_function_of eJS2G0 eJS2G5 hC0 hK7
  have hK4a : InfinitePlaceStep := infinite_place_step_of eJS2S7 eJS2S10 eJS2G0 eJS2G5 eJS2G5b hP2
  have hK4b : FinitePlaceStep := finite_place_of_jump_windows eJS2S2 eJS2S9 eJS2S10 eJS2G0 eJS2G5 eJS2G5b hP2
  have hK4 : K4 := kept_block_at_of_pair_level_chain_threshold eJS2S10 eJS2G0 hK4a hK4b
  have hK9 : K9 := global_level_of eJS2G0 eJS2G1 eJS2G1b eJS2G2c eJS2G5 hK8
  have hKIR : KIR := kir_of eJS2S2 eJS2G0 eJS2G2a eJS2G2c eJS2G5 eJS2G5b hK2 hK3 hK4 hK9
  have hKSec : KSec := ksec_of eJS2G2c eJS2G5 hG1d hK9
  have hK5a : TransformsEmbedding := transform_embedding_of eJS2G11 hP0 hP1 hP2 hK5e
  have hK5b : FourierSeriesColumn := fourier_column_of hN0 hP0 hP1 hK5e
  have hK5c : ShortRowsEmbedding := short_rows_embedding_of hD0 hG2m hK1 hK5e
  have hK6 : K6 := last_row_integral_of eJS2G0 hK5e hK8
  have hKU : KU := ku_of eJS2G5 hD0
  have hKLt1 : KLt1 := kernel_less_first_of eJS2G0 eJS2G5 hD0 hP2 hC0 hK1 hK5e hK5a hK5b hK5c hK6 hK7 hK8 hK8a hKU
  have hKLt2 : KLt2 := kernel_less_second_of hD0 hN0 hH0 hG5t hK1 hK5e hK5a hK5b hK5c hK6
  have hK11 : LastRowCutoff := last_row_cutoff_of eJS2S4 eJS2S8 eJS2G0
  have hK12 : PoissonCutoffFormula := poisson_cutoff_of hD0 hMOD0 hN0 hH0 hG3t hK1
  have hKEq1 : KEq1 := kernel_equality_first_of eJS2G0 eJS2G5 hD0 hN0 hP2 hP3 hC0 hG5t hK1 hK7 hK8 hK8a hKU
  have hKEq2 : KEq2 := kernel_equality_second_of hD0 hN0 hH0 hG4t hG5t hK12
  have hORT : ORT := cusp_orthogonality_of eJS2G14 eJS2SmoNorm hQ2 hD0 hN3 hW0
  have hKY : KY := ky_of hW0
  have hRSPole : RSPole := rspole_of eBlkJacquetShalikaBound eJS2G1 eJS2G10 hW0 hE2 hM1 hKIR hKSec hK5e hKLt1 hKLt2 hK11 hKEq1 hKEq2 hORT hKY
  hRSPole

end PositivityTheory.AdelicQuotientData

end
end
