import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdPre
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinCore
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.TtSmul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTparMain
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.DarbouxAnti
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnipotentBorelTuples.BorelTupU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKTunitMeas
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.ThetaW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoRat
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdMid
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GoodSigPq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopMChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocNbar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocalOperatorLongWeylIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LocOpCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilFull
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.PolyKFinOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinGsT
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.Splitting
import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtB
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.IsCompactK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.ExistsAtPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpMain
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.BorelTup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldTop

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem tHeis_k : _root_.PositivityTheory.SiegelWeilFormula.THeis_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ Z X
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, hf, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  constructor
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [rho_rho, map_smul, smul_eq_mul, symp_cols, frame_yy_A d.ok.frame, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.trace_zero, neg_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul, ← Matrix.add_mul]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [hBx, Matrix.transpose_mul, ← Matrix.mul_assoc, rho_rho, map_smul, smul_eq_mul, add_comm,
      l_shift h hψ _ _ hΦ, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    rw [darboux_anti d.dd, Matrix.mul_assoc Z, ← Matrix.transpose_mul, symp_cols, hf, Matrix.mul_one, trace_gram,
      map_neg]
    linear_combination (Algebra.trace (AF F) (AE F E) (Matrix.trace (Z * (X.map (cA σ))ᵀ * (incM F d.A.J)ᵀ))) *
      (invOf_two_add_invOf_two : (⅟(2 : AF F) + ⅟2 = 1))
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.UpToPf
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem w_cols_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) :
    mat2 w * incM F d.b.1.toCols₂ = incM F d.b.1.toCols₁ ∧
    mat2 w⁻¹ * incM F d.b.1.toCols₂ = ((ε : ℤ) : AE F E) • incM F d.b.1.toCols₁ := by
  obtain ⟨t0, hB, -, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have h1 := inFrame_mul hw
  have he : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hN : (Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) *
      Matrix.fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp [smul_smul, he]
  have h2 := inv_mul_frame h1 hN
  rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
  obtain ⟨-, h1b⟩ := Matrix.fromCols_inj h1
  obtain ⟨-, h2b⟩ := Matrix.fromCols_inj h2
  refine ⟨?_, ?_⟩
  · rw [h1b]; simp
  · rw [h2b]; simp
theorem tt_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (X Z : Mx F E d.m d.n) :
    d.tt (d.gram (((ε : ℤ) : AE F E) • X) Z) = ((ε : ℤ) : AF F) * d.tt (d.gram X Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]
  rw [Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]
theorem upTo_of_k (hU : _root_.PositivityTheory.SiegelWeilFormula.TW.Uniq_k) : _root_.PositivityTheory.SiegelWeilFormula.TW.UpTo_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  obtain ⟨hw1, hw2⟩ := _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.w_cols_k d hw
  have hsp := h.weil.2.1.toIsSplitting
  obtain ⟨C, hC⟩ := hU F E σ d ν hν (d.l ∘ₗ d.om w) (hsp.adm w d.l h.adm) (by
    intro Z Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hsp.impl w _ Φ hΦ]
    have e : actB (cA σ) w (Z * (incM F d.b.1.toCols₂)ᵀ) =
        (Z * (incM F t0.1)ᵀ) * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      change Z * (incM F d.b.1.toCols₂)ᵀ * (mat2 w)ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw1, hBx, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e]
    convert h.kill (Z * (incM F t0.1)ᵀ) _ (hsp.pres w Φ hΦ) using 4
    all_goals rfl)
  refine ⟨C, fun Φ hΦ X => ?_⟩
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) = _
  have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ =
      (((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw2, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [l_rho_om h w _ hΦ, key]
  have hm : d.dd.rho d.B.ψ ((((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ) Φ ∈ d.sch :=
    GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  have e1 := hC _ hm
  simp only [LinearMap.comp_apply] at e1
  rw [e1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only
  rw [(_root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k F E σ d Φ hΦ (((ε : ℤ) : AE F E) • X) Z).2, _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.tt_smul_k]
end PositivityTheory.SiegelWeilFormula.TW.UpToPf
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.TowU
namespace PositivityTheory.SiegelWeilFormula.TW.Twu
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
local instance  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩
theorem uniq_k : _root_.PositivityTheory.SiegelWeilFormula.TW.Uniq_k := by
  classical
  intro F E _ _ _ _ _ σ d ν hν Λ hΛ hinv
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tunit.T_chart_k d
  by_cases hC : C = 0
  · refine ⟨0, fun Φ hΦ => ?_⟩
    have h0 : d.T Φ = 0 := funext fun X => by rw [hT Φ hΦ X, hC, zero_mul]; rfl
    rw [(_root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij F E σ d).2.2 Φ hΦ h0, map_zero, zero_mul]
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  obtain ⟨hμ, hint⟩ := _root_.PositivityTheory.SiegelWeilFormula.KTunit.map_haar_k d τ ν hν
  obtain ⟨c, hc⟩ := translation_invariant_functional_haar d.B.ψ hψ d.κ (ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)) hμ (Λ ∘ₗ S0') (hop.adm' Λ hΛ) (by
    intro a φ hφ
    have e0 := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ a)
    have ea : (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ a) (τ k)) = a := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_cinv_k d τ a
    rw [ea] at e0
    rw [← schr_zero_right, ← e0, LinearMap.comp_apply, LinearMap.comp_apply, rhoS' _ φ hφ]
    exact hinv _ _ (hop.pres' φ hφ))
  refine ⟨c / C, fun Φ hΦ => ?_⟩
  have h1 := hc (S0 Φ) (hop.pres Φ hΦ)
  rw [LinearMap.comp_apply, hop.left Φ hΦ] at h1
  rw [h1, ← hint]
  have e2 : ∫ Z, d.T Φ Z ∂ν = C * ∫ Z, S0 Φ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ Z) ∂ν := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Z => hT Φ hΦ Z)
  rw [e2]
  field_simp
end PositivityTheory.SiegelWeilFormula.TW.Twu
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isW_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) : w ∈ rat2 σ d.Y := by
  refine PositivityTheory.SiegelWeilFormula.kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
  rw [(hw : inFrame d.b w = _)]
  ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
theorem thetaW_k : _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaW_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun ε w hw Φ hΦ => ?_, GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ⟩
  exact ⟨d.ok.dbl.weil.2.1.pres w Φ hΦ, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_rational_invariant d w (_root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.isW_rat_k d hw) Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_nbar_of (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) {ε : ℤˣ} {w₀ : d.G} (hw₀ : d.IsW ε w₀)
    {C s : ℂ} {B : d.MF → d.MF} (hW' : R.StepOK w w₀ (locFT C s) B) :
    ∃ κ : ℂ, κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f) := by
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    intro f hf X
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    rw [map_one, Module.End.one_apply, hT'] at e
    exact congrFun e X
  have key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    intro f hf u
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z)
    rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz : ∀ f : d.LF, IsSw f → f = 0 := by
      intro f hf
      funext u
      have := key0 f hf u
      rw [hb, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hX₀
    refine ⟨1, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_⟩
    · rw [hz f hf]
      simp [locFT_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ
    have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := by
      intro f hf
      funext u
      have := key0 f hf u
      simp only [Pi.smul_apply, smul_eq_mul, hκ]
      field_simp
      linear_combination -this
    have hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      intro y c hc hy f hf
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
          · rw [hz]; simp
          · rw [hz]; simp [Complex.inv_I]
        rw [Matrix.conjTranspose_smul, hc, hs]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · have : f = 0 := funext hf0
        rw [this, R.locOp_zero hT hG hL y]
        simp [locFT_zero, chirp_zero]
      push Not at hf0
      obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        intro X
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
        have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]
        apply mul_left_cancel₀ hu₀
        linear_combination -this
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e := (hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
      rw [hrel] at e1
      apply R.tens_cancel hΨ.1 hΨ.2.1
      rw [← e1, e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨κ, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.localOperator_longWeyl_integral (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ y : GR d.n, mR y = JJ d.n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have hεR : ε = R.ε := R.isW_eps w hw₀
  obtain ⟨C₀, B, hC₀, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C₀ s) B := hW
  obtain ⟨κ, hκ, -, hnb, -⟩ := R.locOp_nbar_of hT hG hL hw₀ hW'
  have hk : ((R.sg w : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Units.ne_zero _)
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 * |((R.sg w : ℤ) : ℝ)| := by
    have h1 : |((R.sg w : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
    rw [h1, hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  obtain ⟨c, hc, hfres⟩ := GlobalTheory.T.fourier_transform_matrix_space_involution d.m d.n C₀ s ((R.sg w : ℤ) : ℝ) hC₀ hk hsn
  refine ⟨κ⁻¹ * c, mul_ne_zero (inv_ne_zero hκ) hc, fun y hy f hf => ?_⟩
  obtain ⟨y₁, y₂, h1, h2, rfl⟩ := jj_split y hy
  have hb1 : (1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hbm : (-1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = -1 := by rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  have hf1 : IsSw (L y₁ f) := (hL y₁ f hf).1
  have hf2 : IsSw (L y₂ (L y₁ f)) := (hL y₂ _ hf1).1
  rw [R.locOp_mul hT hG hL (y₁ * y₂) y₁ f hf, R.locOp_mul hT hG hL y₁ y₂ _ hf1,
    R.locOp_nU hT hG hL y₁ 1 hb1 h1 _ hf2, hnb y₂ (-1) hbm h2 _ hf1, R.locOp_nU hT hG hL y₁ 1 hb1 h1 f hf]
  have hx : (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • (-1 : Matrix (Fin d.n) (Fin d.n) ℂ) = 1 := by
    rw [hεR]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rw [he, hz] <;> simp [Complex.inv_I]
  rw [hx]
  obtain ⟨φ, hφ⟩ := hf
  have hch : ∀ g : d.LF, chirp ((R.sg w : ℤ) : ℂ) (1 : Matrix (Fin d.n) (Fin d.n) ℂ) g =
      fun u => Complex.exp (2 * Real.pi * Complex.I * (((R.sg w : ℤ) : ℝ) : ℂ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u := fun g => by
    funext u
    simp [chirp]
  have hin : (fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) =
      chirp ((R.sg w : ℤ) : ℂ) 1 f := rfl
  have h0 : Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) *
        ((Matrix.of (0 : Fin d.m → Fin d.n → ℂ))ᴴ * Matrix.of (0 : Fin d.m → Fin d.n → ℂ)))) = 1 := by
    simp
  simp only [hin]
  rw [h0, one_mul, Pi.smul_apply, smul_eq_mul, hch, hch, ← hφ]
  have := hfres φ
  simp only [locFT] at this ⊢
  rw [this, hφ]
  ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
open PositivityTheory.SiegelWeilFormula.KFock
namespace PositivityTheory.SiegelWeilFormula.KLI
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem goodAway0_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : ∃ Ψ, R.GoodAway w Ψ ∧ Ψ 0 ≠ 0 := by
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have h0 : Ψ 0 ≠ 0 := by
    have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
      funext k
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
      rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
      rfl
    have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
      rw [hc]
      exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
    have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
    simpa [Ψ, hg0] using hp
  refine ⟨Ψ, ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun hz => h0 (by rw [hz]; rfl), fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩, h0⟩
theorem locOp_cont_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    ∀ (P : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ), Continuous fun y => L y (fP P) u := by
  intro P u
  obtain ⟨Ψ, hΨ, hΨ0⟩ := _root_.PositivityTheory.SiegelWeilFormula.KLI.goodAway0_k R w
  obtain ⟨Φ, hΦ, hTΦ⟩ := R.exists_adm hT hΨ (isSw_fP P)
  obtain ⟨Z, hZw, hZf, hZu⟩ := R.loc_surj w 0 u
  have hΨZ : Ψ Z = Ψ 0 := by simpa using hΨ.1 0 Z hZw hZf
  have hZu' : R.loc w Z = u := by simpa using hZu
  have key : ∀ y, L y (fP P) u = d.T (d.om (R.ι w y) Φ) Z / Ψ 0 := by
    intro y
    have e := congrFun ((hL y (fP P) (isSw_fP P)).2 Ψ hΨ.1 Φ hΦ hTΦ) Z
    rw [e]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZu', hΨZ]
    field_simp
  set v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) := Z * (incM F d.b.1.toCols₂)ᵀ with hv_def
  have hfv : finOne F • v = 0 := by rw [hv_def, ← Matrix.smul_mul, hZf, Matrix.zero_mul]
  have hev : finOne F • d.dd.e v = 0 := by rw [← LinearEquiv.map_smul, hfv, map_zero]
  let π2 : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : π2 (finOne F) = 1 := rfl
  have hv : ∀ i, ((d.dd.e v).1 i).2 = 0 ∧ ((d.dd.e v).2 i).2 = 0 := by
    intro i
    have e1 := congrFun (congrArg Prod.fst hev) i
    have e2 := congrFun (congrArg Prod.snd hev) i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply] at e1 e2
    refine ⟨?_, ?_⟩
    · have := congrArg π2 e1
      rw [map_mul, h1, one_mul, map_zero] at this
      exact this
    · have := congrArg π2 e2
      rw [map_mul, h1, one_mul, map_zero] at this
      exact this
  have hadm := rho_adm F d.B.ψ d.ok.good.std d.ok.dbl.adm (d.dd.e v) hv
  have hc := d.ok.dbl.weil.2.1.cont _ hadm Φ hΦ
  refine ((hc.comp (R.cont w)).div_const (Ψ 0)).congr fun y => (key y).symm
end PositivityTheory.SiegelWeilFormula.KLI
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.KLI
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem locHyp_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    LocHyp (R.sg w) L := by
  have hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.goodAwayEx_k
  refine
    { sw := fun y f hf => (hL y f hf).1
      one := R.locOp_one hT hG hL
      mul := R.locOp_mul hT hG hL
      lin := R.locOp_lin hT hG hL
      nU := R.locOp_nU hT hG hL
      mM := ?_
      nbar := ?_
      longWeylFunctional := R.localOperator_longWeyl_integral hT hA hG hL
      cont := _root_.PositivityTheory.SiegelWeilFormula.KLI.locOp_cont_k hT R hL }
  · obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
    exact ⟨k, fun y a ha hy f hf => hk y a ha hy f hf⟩
  · obtain ⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
    exact ⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, fun y c hc hy f hf' => hf y c hc hy f hf'⟩
theorem locInst_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (_hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (_hLi : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k) : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k := by
  intro F E _ _ _ _ _ σ d R w L hL
  obtain ⟨sL, ρ, e, hD, h1, h2⟩ := locData_of (_root_.PositivityTheory.SiegelWeilFormula.KLI.locHyp_of_k hT hA R hL)
  exact ⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩
end PositivityTheory.SiegelWeilFormula.KLI
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global GlobalTheory.HeisSchA
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
theorem finLevel_k : _root_.GlobalTheory.ThK.Dbl.FinLevel_k := by
  intro F E _ _ _ _ _ σ B m n A Y hB κ _ dd K hK Φ hΦ
  have lin : ∀ (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      actB (cA σ) k (epsF F • u) = epsF F • actB (cA σ) k u := fun k u => Matrix.smul_mul _ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ∀ {α β : Type} [Finite α] [Finite β], IsModuleTopology (AF F) (Matrix α β (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (_ → _ → AE F E))
  have c : Continuous fun y : ((κ → AF F) × (κ → AF F)) × G2 σ Y => dd.e (actB (cA σ) y.2 (dd.e.symm y.1)) :=
    (IsModuleTopology.continuous_of_linearMap dd.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap dd.e.symm.toLinearMap).comp continuous_fst).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose)
  obtain ⟨s, hs, h⟩ := finite_values hB.std (hK.eventually_forall_of_forall_eventually
    (P := fun w k => schr B.ψ (epsF F • dd.e (actB (cA σ) k (dd.e.symm w))) Φ = Φ) fun k _ =>
      (c.tendsto' (0, k) 0 (by simp [actB])).eventually (level hB.std.1 hΦ))
  refine ⟨{u | epsF F • u = u ∧ ∀ k ∈ K, dd.rho B.ψ (actB (cA σ) k u) Φ = Φ}, fun u hu => ⟨fun i => ?_, fun i => ?_,
    fun k hk => ⟨by rw [← lin, hu.1], fun k' hk' => ?_⟩⟩, fun u hu => ?_, s, hs, fun Ψ hΨ => h Ψ fun w hw => ?_⟩
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · have := hu.2 _ (mul_mem hk' hk)
    simpa [actB, Matrix.mul_assoc] using this
  · simpa [actB] using hu.2 1 (one_mem _)
  · have := hΨ (epsF F • dd.e.symm w) ⟨by rw [smul_smul, epsF_sq], fun k hk => by
      rw [lin, Darboux.rho, map_smul]; exact hw k hk⟩
    rwa [Darboux.rho, map_smul, LinearEquiv.apply_symm_apply] at this
end GlobalTheory.ThK.Dbl
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isCompact_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsCompact (d.K : Set d.G) := by
  have hB := d.ok.good
  have hK := d.ok.stdK
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm d.B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := SiegelEisensteinSeries.BRoad.isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ d.K, ∀ i j, inFrame d.b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame d.b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame d.b k).map (piInf (d.B.emb w)) ∈ Matrix.unitaryGroup (Fin d.n ⊕ Fin d.n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :=
    (fun M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) => incM F d.b.1 * M * incM F (d.b⁻¹).1) ''
      Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ d.K, mat2 k ∈ S := fun k hk => ⟨inFrame d.b k, fun i _ j _ => hentry k hk i j, by
    show incM F d.b.1 * (incM F (d.b⁻¹).1 * mat2 k * incM F d.b.1) * incM F (d.b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (d.B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (d.B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  have hKset : (d.K : Set d.G) =
      (⋂ w, {k | (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (d.K : Set d.G) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F d.Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ d.Y) d.K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (d.K.inv_mem hk)⟩
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem splitting_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om :=
  d.ok.dbl.weil.2.1.toIsSplitting
theorem imp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (k : d.G) :
    Box.Imp d.B.ψ (d.om k) fun w => d.dd.e (actB (cA σ) k (d.dd.e.symm w)) :=
  ⟨(_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).pres k, (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).adm k, fun w w' => by simp only [actB, map_add, Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := (_root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d).impl k (d.dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩
theorem om_D_k (k : d.G) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) : d.om k (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e (actB (cA σ) k u)) (d.om k Φ) := by
  have := (_root_.PositivityTheory.SiegelWeilFormula.KK.imp_k d k).inter d.ok.good.std (Box.at_e d.dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this
theorem D_kfS_k {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) :
    Box.D (d.dd.e u) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := Box.exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = Box.D (d.dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact Box.DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, Box.at_actB k hv, _, h2 k hk x hx, _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i
theorem vac_kfS_k (θ : InfinitePlace F → Matrix (Fin d.m) (Fin d.m) ℂ)
    (θ' : InfinitePlace F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ)
    (hc : ∀ k ∈ d.K, ∀ w, Commute ((mat2 k).map (piInf (d.B.emb w))) (θ' w)) (ε : InfinitePlace F → ℤˣ) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : ∀ u u', At (evI F) u → At (evI F) u' → Box.Rel d.B.emb ε θ θ' u u' →
      Box.D (d.dd.e u') Φ = Complex.I • Box.D (d.dd.e u) Φ) : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d := by
  have hB := d.ok.good
  have hs := _root_.PositivityTheory.SiegelWeilFormula.KK.splitting_k d
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := _root_.GlobalTheory.ThK.Dbl.finLevel_k F E σ d.B d.m d.n d.A d.Y hB d.κ d.dd d.K (_root_.PositivityTheory.SiegelWeilFormula.KK.isCompact_K_k d) Φ hΦ
  have radd : ∀ u (x y : d.Fn), d.dd.rho d.B.ψ u (x + y) = d.dd.rho d.B.ψ u x + d.dd.rho d.B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : d.Fn), d.dd.rho d.B.ψ u (c • x) = c • d.dd.rho d.B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ d.Fn :=
    { carrier := {Ψ | Ψ ∈ d.sch ∧ (∀ u ∈ Λ, d.dd.rho d.B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Box.Rel d.B.emb ε θ θ' u u' → Box.D (d.dd.e u') Ψ = Complex.I • Box.D (d.dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by
        simp only [Box.D, Box.DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [Box.D] at e1 e2 ⊢
        rw [Box.DP_add h.1 h'.1, Box.DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [Box.D] at e1 ⊢
        rw [Box.DP_smul h.1, Box.DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : d.κ → AF F), (∀ i, evI F (y i) = 0) → Dense.pt x 0 + y = Dense.pt x (Box.fn y) := fun x y hy => by
      rw [← Box.pt_self (Dense.pt x 0 + y), Box.nf_add, Box.nf_pt, show Box.nf y = 0 from funext hy, add_zero]
      exact congrArg (Dense.pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (Dense.pt 0 (Box.fn z) i) = 0 := fun i => congrFun (Dense.evI_pt 0 (Box.fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (Dense.pt (Box.nf z) 0) (Box.at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show Box.fn (Dense.pt 0 (Box.fn z)) = Box.fn z from rfl, Box.pt_self] at this
    obtain ⟨f, e⟩ := Box.slice Ψ.2.1 (Box.fn y)
    have g : Box.Gs d.dd.e d.B.emb ε θ θ' f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (Dense.pt x (Box.fn y))
      rwa [Pi.smul_apply, Box.D, Box.D, Box.DP_pt e, Box.DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show Box.nf y = 0 from funext (s1 y hy), Box.pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← Box.actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← Box.actB_inv k u, ← Box.actB_inv k u', ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ a) h.1, ← _root_.PositivityTheory.SiegelWeilFormula.KK.om_D_k k (Box.at_actB _ b) h.1,
      ← map_smul]
    refine congrArg (d.om k) (h.2.2 _ _ (Box.at_actB _ a) (Box.at_actB _ b) fun w => ?_)
    have cm := (hc k⁻¹ (inv_mem hk) w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem exists_at_place_k (w : InfinitePlace F) (V : Matrix (Fin d.m) (Fin d.n) ℂ) :
    ∃ V' : Mx F E d.m d.n, At (evI F) V' ∧ ∀ w', d.cw w' V' = if w' = w then V else 0 := by
  have h := d.ok.good.cm
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h d.B.emb fun w' =>
    if w' = w then V i j else 0
  refine ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w' => ?_⟩
  ext i j
  show piInf (d.B.emb w') (x i j) = _
  rw [hz i j w']
  split_ifs <;> rfl
theorem mZ_place_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (tA : Matrix (Fin d.n) (Fin d.n) (AE F E)) (htA : _root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * tA)
    {V' : Mx F E d.m d.n} {V : Matrix (Fin d.m) (Fin d.n) ℂ} (hV : ∀ w', d.cw w' V' = if w' = w then V else 0)
    (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (V' * tAᵀ) X = -(2 * ((((R.ε : ℤ) : ℂ)) * trace ((d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * V.map star)).re) := by
  have e1 : V' * tAᵀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ = V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ := by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, e1, _root_.PositivityTheory.SiegelWeilFormula.KK.trace_sp_k, Finset.sum_eq_single w]
  · congr 3
    have hX : (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = V * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w
      rw [if_pos rfl] at this
      rw [show V'.map (piInf (d.B.emb w)) = d.cw w V' from rfl, this]
      rfl
    rw [hX, hVb]
    exact trace_form_sign_eq (_root_.PositivityTheory.SiegelWeilFormula.KK.frame_form_k R w) (d.cw w X) V
  · intro w' _ hw'
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w')) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w'
      rw [if_neg hw'] at this
      rw [show V'.map (piInf (d.B.emb w')) = d.cw w' V' from rfl, this, Matrix.zero_mul]
    rw [hVb]
    simp
  · intro h; exact absurd (Finset.mem_univ w) h
theorem var_span'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) :
    ∃ (Z₁ Z₂ : Mx F E d.m d.n) (c₁ c₂ : ℂ), At (evI F) Z₁ ∧ At (evI F) Z₂ ∧
      ∀ X, evX (MvPolynomial.X k) (R.loc w X) = c₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₁ X : ℂ) + c₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₂ X : ℂ) := by
  obtain ⟨tA, htA⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.firstColumns_eq_diag_mul (d := d)
  set τ := d.B.emb w
  set fr := (R.fr w).1
  set fi := ((R.fr w)⁻¹).1
  set A := d.A.J.map τ.1
  set e : ℂ := ((R.ε : ℤ) : ℂ)
  have he : e * e = 1 := by rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
  have hes : star e = e := by simp [e]
  have hz : star R.ζ * R.ζ = 1 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [Complex.ext_iff]
  have hfi : fr * fi = 1 := by simp only [fr, fi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hif : fi * fr = 1 := by simp only [fr, fi]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set P := (((R.sg w : ℤ) : ℂ) * R.ζ) • (fr.map star * frᵀ)
  have hAP : A * P = 1 := by
    have hA := A_eq hfi hz (R.hfr w)
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl] at hA
    rw [hA]
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have t1 : fiᵀ * fi.map star * (fr.map star * frᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fi.map star), ← mapStar_mul, hif]
      rw [show (1 : Matrix (Fin d.m) (Fin d.m) ℂ).map star = 1 by ext i j; simp [one_apply, apply_ite]]
      rw [Matrix.one_mul, ← transpose_mul, hfi, transpose_one]
    rw [t1]
    have hs2 : ((R.sg w : ℤ) : ℂ) * R.ζ * (((R.sg w : ℤ) : ℂ) * star R.ζ) = 1 := by
      calc _ = (((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * (star R.ζ * R.ζ) := by ring
        _ = 1 := by rw [hz, mul_one]; rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
    rw [hs2, one_smul]
  have key : ∀ M : Matrix (Fin d.m) (Fin d.n) ℂ, ∃ Z : Mx F E d.m d.n, At (evI F) Z ∧
      ∀ X, (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ) = -(2 * e) * ((trace ((d.cw w X)ᵀ * M)).re : ℂ) := by
    intro M
    obtain ⟨V', hV'a, hV'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.exists_at_place_k (d := d) w ((P * M).map star)
    refine ⟨V' * tAᵀ, at_mul hV'a _, fun X => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_place_k R w tA htA hV' X]
    have : (d.cw w X)ᵀ * A * ((P * M).map star).map star = (d.cw w X)ᵀ * M := by
      rw [show ((P * M).map star).map star = P * M by ext i j; simp only [Matrix.map_apply, star_star], ← Matrix.mul_assoc, Matrix.mul_assoc _ A, hAP,
        Matrix.mul_one]
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl, this]
    have hre : (e * trace ((d.cw w X)ᵀ * M)).re = e.re * (trace ((d.cw w X)ᵀ * M)).re := by
      rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
    rw [hre]
    rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h] <;> ring
  have hM : ∀ (c : ℂ) (x : Matrix (Fin d.m) (Fin d.n) ℂ),
      trace (xᵀ * Matrix.of fun b j => if j = k.2.1 then c * fi k.1 b else 0) = c * (fi * x) k.1 k.2.1 := fun c x => by
    simp only [trace, diag, mul_apply, transpose_apply, of_apply, mul_ite, mul_zero]
    rw [Finset.sum_eq_single k.2.1 (fun j _ hj => by simp [hj]) (by simp)]
    simp only [if_pos rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by simp only [if_true]; ring
  obtain ⟨Z₁, h1, e1⟩ := key (Matrix.of fun b j => if j = k.2.1 then 1 * fi k.1 b else 0)
  obtain ⟨Z₂, h2, e2⟩ := key (Matrix.of fun b j => if j = k.2.1 then (-Complex.I) * fi k.1 b else 0)
  have hl : ∀ X, evX (MvPolynomial.X k) (R.loc w X) =
      if k.2.2 then (fi * d.cw w X) k.1 k.2.1 else star ((fi * d.cw w X) k.1 k.2.1) := fun X => by
    simp only [evX, MvPolynomial.eval_X, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply]
    split_ifs <;> (try simp only [star_star]) <;> rfl
  have hsplit : ∀ z : ℂ, z = (z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  have hsplit' : ∀ z : ℂ, star z = (z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  refine ⟨Z₁, Z₂, -(e / 2) * (if k.2.2 then 1 else 1), -(e / 2) * (if k.2.2 then Complex.I else -Complex.I), h1, h2,
    fun X => ?_⟩
  rw [hl X, e1 X, e2 X, hM, hM, one_mul]
  have hinv : -(e / 2) * (-(2 * e)) = 1 := by linear_combination he
  split_ifs
  · conv_lhs => rw [hsplit ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) - Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
  · rw [hsplit' ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) + Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def Tl_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, ← map_add]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _
def TK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Submodule ℂ (Mx F E d.m d.n → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d).map (_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d)
theorem D_dg_mem_k {Φ : d.Fn} (hΦ : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) :
    Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d :=
  _root_.PositivityTheory.SiegelWeilFormula.KK.D_kfS_k (fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]) hΦ
theorem mul_var_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => evX (MvPolynomial.X k) (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  obtain ⟨Φ, hΦ, rfl⟩ := hf
  obtain ⟨Z₁, Z₂, c₁, c₂, h1, h2, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.var_span'_k R w k
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
    (c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ,
    add_mem (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h1)) (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h2)), funext fun X => ?_⟩
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_add ((c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)
    ((c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)) X
  simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = _ at t
  change d.T _ X = _ * d.T Φ X
  rw [t]
  change _ * d.T _ X + _ * d.T _ X = _
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h1, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h2, e X]
  field_simp
theorem mul_pol_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Q : PX d.m d.n) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) :
    (fun X => evX Q (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction Q using MvPolynomial.induction_on generalizing f with
  | C a =>
    have : (fun X => evX (MvPolynomial.C a) (R.loc w X) * f X) = a • f := funext fun X => by
      simp [evX]
    rw [this]; exact Submodule.smul_mem _ _ hf
  | add p q hp hq =>
    have : (fun X => evX (p + q) (R.loc w X) * f X) = (fun X => evX p (R.loc w X) * f X) + fun X => evX q (R.loc w X) * f X :=
      funext fun X => by simp [evX, add_mul]
    rw [this]; exact add_mem (hp hf) (hq hf)
  | mul_X p k hp =>
    have : (fun X => evX (p * MvPolynomial.X k) (R.loc w X) * f X) =
        fun X => evX (MvPolynomial.X k) (R.loc w X) * (evX p (R.loc w X) * f X) := funext fun X => by
      simp only [evX, map_mul]; ring
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_var_k R w k (hp hf)
theorem mul_prod_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (s : Finset (InfinitePlace F)) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => (∏ w ∈ s, evX (P w) (R.loc w X)) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert w s hw ih =>
    have : (fun X => (∏ w ∈ insert w s, evX (P w) (R.loc w X)) * f X) =
        fun X => evX (P w) (R.loc w X) * ((∏ w ∈ s, evX (P w) (R.loc w X)) * f X) := funext fun X => by
      rw [Finset.prod_insert hw, mul_assoc]
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_pol_k R w (P w) ih
theorem vac_mem_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ}
    (hg : g ∈ SB _) : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  have hgen : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ R.fock := Submodule.subset_span ⟨fun _ => 1, g, hg, funext fun X => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, fP, evX]⟩
  obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hgen)
  refine ⟨Φ, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_kfS_k (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) (fun k hk w => _root_.PositivityTheory.SiegelWeilFormula.KK.commute_thB_k R hk w) (fun _ => 1) hΦ fun u u' hu hu' hr => ?_, e⟩
  have m1 : Box.D (d.dd.e u') Φ ∈ d.sch := Box.DP_mem hΦ _ _
  have m2 : Box.D (d.dd.e u) Φ ∈ d.sch := Box.DP_mem hΦ _ _
  refine sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem m1 (Submodule.smul_mem _ _ m2)) (funext fun X => ?_))
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_sub (Box.D (d.dd.e u') Φ) (Complex.I • Box.D (d.dd.e u) Φ)) X
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = d.T _ X - Complex.I * d.T _ X at t
  rw [t, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_rel_k R g hΦ e hu hu' hr X, sub_self]
  rfl
theorem fock_le_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have e : (fun X => (∏ w ∈ Finset.univ, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w ∈ Finset.univ, evX (P w) (R.loc w X)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := funext fun X => by
    simp only [fP, _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, Finset.prod_mul_distrib]; ring
  rw [SetLike.mem_coe, e]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_prod_k R P _ (_root_.PositivityTheory.SiegelWeilFormula.KK.vac_mem_k hT hF R hg)
theorem polyKFin_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k := by
  intro hT hF F E _ _ _ _ _ σ d R Φ hΦ hf
  obtain ⟨Φ', h', e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.fock_le_k hT hF R hf
  have : Φ = Φ' := (sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k h')) (by
    rw [show d.T (Φ - Φ') = _root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d (Φ - Φ') from rfl, map_sub]
    exact sub_eq_zero.2 e.symm))).symm ▸ rfl
  rw [this]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.kFin_of_mem_k h'
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem locInst_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k := _root_.PositivityTheory.SiegelWeilFormula.KLI.locInst_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k (_root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_k hT.1)
theorem siegelWeilStd_mid_k (hW : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k) (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k :=
  have hT := _root_.PositivityTheory.SiegelWeilFormula.Fin.tAll_of_k hW
  _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_of_k hT (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT)
    (_root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_full_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds (_root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT)) hKP
    (_root_.PositivityTheory.SiegelWeilFormula.KK.polyKFin_of_k hT _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k) hLD hCT HSt.holLeadB
end PositivityTheory.SiegelWeilFormula.Fin
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
local instance  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩
theorem tUnit_k : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k := by
  intro F E _ _ _ _ _ σ d ν hν x Φ hΦ Φ' hΦ'
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tunit.T_chart_k d
  have hpres : ∀ φ ∈ schA F d.κ, d.om x φ ∈ schA F d.κ := fun φ hφ => d.ok.dbl.weil.2.1.pres x φ hφ
  have hunit := d.ok.dbl.weil.2.1.unit
  obtain ⟨hμ, hint⟩ := _root_.PositivityTheory.SiegelWeilFormula.KTunit.map_haar_k d τ ν hν
  set μ := ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ) with hμdef
  have h1 : ∀ Ψ ∈ d.sch, ∀ Ψ' ∈ d.sch, ∫ X, d.T Ψ X * star (d.T Ψ' X) ∂ν =
      (C * star C) * ∫ y, S0 Ψ y * star (S0 Ψ' y) ∂μ := by
    intro Ψ hΨ Ψ' hΨ'
    rw [← integral_const_mul, ← hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hT _ hΨ, hT _ hΨ', star_mul']
    change _ = C * star C * (S0 Ψ (fun k => d.crd X (τ k)) * star (S0 Ψ' fun k => d.crd X (τ k)))
    ring
  rw [h1 _ (hpres Φ hΦ) _ (hpres Φ' hΦ'), h1 _ hΦ _ hΦ']
  congr 1
  obtain ⟨c, hc0, hctop, hcn⟩ := hop.norm μ μ hμ hμ
  have hp' : ∀ φ ∈ schA F d.κ, (S0 ∘ₗ d.om x ∘ₗ S0') φ ∈ schA F d.κ := fun φ hφ =>
    hop.pres _ (hpres _ (hop.pres' φ hφ))
  have hT' : ∀ φ ∈ schA F d.κ, ∫⁻ y, ‖(S0 ∘ₗ d.om x ∘ₗ S0') φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
    intro φ hφ
    have e1 := hcn _ (hpres _ (hop.pres' φ hφ))
    have e2 := hcn _ (hop.pres' φ hφ)
    rw [hop.right φ hφ] at e2
    have e3 := hunit μ hμ x _ (hop.pres' φ hφ)
    simp only [LinearMap.comp_apply]
    rw [e1, e2, e3]
  have := GlobalTheory.DblUnitaryBox.integral_mul_star_eq μ hμ (S0 ∘ₗ d.om x ∘ₗ S0') hp' hT' (hop.pres Φ hΦ) (hop.pres Φ' hΦ')
  simpa only [LinearMap.comp_apply, hop.left _ hΦ, hop.left _ hΦ'] using this
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem tWeyl_of_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k :=
  _root_.PositivityTheory.SiegelWeilFormula.TW.tWeyl_of_k _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k (_root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.upTo_of_k _root_.PositivityTheory.SiegelWeilFormula.TW.Twu.uniq_k) hP _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.thetaW_k
theorem siegelWeilStd_pre_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k :=
  have hT := _root_.PositivityTheory.SiegelWeilFormula.Fin.tAll_of_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
  _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_mid_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
    (_root_.PositivityTheory.SiegelWeilFormula.KFP.kFinPoly_of_k hT _root_.PositivityTheory.SiegelWeilFormula.Tunit.tUnit_k _root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k (_root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT))
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.ldEx_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds) hCT
end PositivityTheory.SiegelWeilFormula.Fin
end
end
end
