import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussianStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandardStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatumStatement

section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCommuting_cartanInvolution_moved_standard : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  first | exact @GlobalTheory.StdUnn.CartanMove.cartan_move_std | exact GlobalTheory.StdUnn.CartanMove.cartan_move_std | (intros; apply GlobalTheory.StdUnn.CartanMove.cartan_move_std <;> assumption)
end

section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeckeChar_restrictionEta_inv : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (m : ℕ), IsHeckeChar D χ → ResEta D χ m → IsHeckeChar D χ⁻¹ ∧ ResEta D χ⁻¹ m := by
  first | exact @GlobalTheory.StdUnn.isHeckeChar_resEta_inv | exact GlobalTheory.StdUnn.isHeckeChar_resEta_inv | (intros; apply GlobalTheory.StdUnn.isHeckeChar_resEta_inv <;> assumption)
end

section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c → (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  first | exact @GlobalTheory.StdUnn.holValueAt_npow_sub_mul | exact GlobalTheory.StdUnn.holValueAt_npow_sub_mul | (intros; apply GlobalTheory.StdUnn.holValueAt_npow_sub_mul <;> assumption)
end

section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∃ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ IsCharAF D.host.F (shift ψ lam) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ lam) θ l ∧ ∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖ := by
  first | exact @GlobalTheory.StdUnn.shift_char_realPar | exact GlobalTheory.StdUnn.shift_char_realPar | (intros; apply GlobalTheory.StdUnn.shift_char_realPar <;> assumption)
end

section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFlatSection_eq_translate_standardSection : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A) (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) → s0 B A.rank = sZero A B ∧ (∀ (z : ℂ) (g : GA D (dblSp A)), flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g = npow (absA D (aP A p)) (sZero A B - z) * sect omS (hgtStd A a κ p) Φ z (κ (g * p))) ∧ ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := by
  first | exact @GlobalTheory.StdUnn.flat_swSec_eq_sect | exact GlobalTheory.StdUnn.flat_swSec_eq_sect | (intros; apply GlobalTheory.StdUnn.flat_swSec_eq_sect <;> assumption)
end

section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem sw_doubled_of_std : GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelWeilUnitaryConvergent := by
  intro hP D ψ A B hAB hB2 hW χB omh hWe a hMaj _ θ sS sB hθ hsS hsB hK mW 𝓨 hcov ν hν f hf
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D A m0 hm0
  obtain ⟨p, hp⟩ := hp0 A a hMaj κ hκ
  obtain ⟨lam, hlam, hψ', l, hl, hlabs⟩ := GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters D ψ hWe.std θ hθ m0 hm0
  obtain ⟨omS, hT⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ A B χB omh hWe mW 𝓨 hcov θ hθ κ
  obtain ⟨s', hs'std, hs'⟩ := GlobalTheory.T.compactCommuting_cartanInvolution_moved_standard D A m0 hm0 κ hκ a p hp θ hθ sS hsS hK
  have hf' : IsFockVec ψ θ (dblSp A) B s' sB (omh ((p : GA D (dblSp A))⁻¹, 1) f) :=
    GlobalTheory.T.isPolynomialFockThetaVector_weilOperator_cartan D ψ (dblSp A) B 1 χB omh hWe θ hθ sS s' sB _ hs' f hf
  have hschw := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B mW 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f),
      ((hschw ψ hWe.std θ hθ A B mW 𝓨 hcov).1 _ hf'.1)⟩
  have hΦ : Φ.1 ∈ fockA θ B A.rank l sB :=
    GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ hWe.std θ hθ A B mW 𝓨 hcov m0 hm0 s' sB hs'std hsB l hlabs _ hf'
  have hχ := GlobalTheory.T.isHeckeChar_restrictionEta_inv D χB B.rank hWe.hecT hWe.resT
  have hWS : IsWeilSch (shift ψ lam) χB⁻¹ θ B mW omS :=
    ⟨GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam⟩
  have hH := GlobalTheory.T.standardUnitaryHeight_isSiegelHeightFunction D A m0 hm0 κ hκ a p hp
  obtain ⟨hInt, hEis, hHol⟩ := hP D A.rank B hAB hB2 hW (shift ψ lam) hψ' χB⁻¹ hχ.1 hχ.2 θ hθ mW 𝓨 hcov omS hWS
    (hgtStd A a κ p) hH l hl sB hsB ν hν Φ hΦ
  obtain ⟨h0, hflat, hact⟩ := GlobalTheory.T.doubledFlatSection_eq_translate_standardSection D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam a p f hf.1 Φ rfl
  have hth : ∀ g : GA D (dblSp A), theta omS Φ (κ (g * p)) = fun h => thetaKO omh g h f := fun g => by
    funext h
    rw [GlobalTheory.T.thetaKernel_eq_tsum_schrodingerFunction D ψ A B χB omh hWe mW 𝓨 hcov f hf.1 g h, theta, hact g]
  have hmean : ∀ g : GA D (dblSp A), GlobalTheory.ThetaMean.thetaMean omh ν f g = thetaInt omS ν Φ (κ (g * p)) := fun g => by
    rw [thetaInt, hth g]; rfl
  have hP' := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A m0 hm0 κ hκ
  have hG' := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A m0 hm0 κ hκ
  have Heisenberg₂ := fun (z : ℂ) (hz : (A.rank : ℝ) / 2 < z.re) =>
    GlobalTheory.T.cosetSum_along_mulEquiv_subgroups _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank) hP' hG'
      (sect omS (hgtStd A a κ p) Φ z) (p : GA D (dblSp A)) (npow (absA D (aP A p)) (sZero A B - z))
      (flat A a (swSec A B omh mW 𝓨 f) (sZero A B) z) (fun g => hflat z g) (hEis z hz).1
  refine ⟨fun g => ?_, ⟨fun z hz => ⟨(Heisenberg₂ z hz).1, fun g => ((Heisenberg₂ z hz).2 g).1 ((hEis z hz).2 _)⟩, fun g => ?_⟩⟩
  · rw [← hth g]; exact hInt _
  · have hr : 0 < absA D (aP A p) := hom_pos _ _
    have := GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor (fun z => GlobalTheory.Eis.cosetSum (P D A.rank) (GF D A.rank) (sect omS (hgtStd A a κ p) Φ z) (κ (g * p)))
      (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh mW 𝓨 f) (sZero A B)) g) (s0 B A.rank) _ (absA D (aP A p))
      ((A.rank : ℝ) / 2) hr (hHol (κ (g * p))) (fun z hz => by
        rw [h0]; exact ((Heisenberg₂ z hz).2 g).2)
    rw [h0] at this
    rw [hmean g]
    exact this

end GlobalTheory.StdUnn
end
