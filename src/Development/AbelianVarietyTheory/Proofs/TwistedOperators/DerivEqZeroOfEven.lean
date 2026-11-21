import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAwayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamilyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelCoordinatesBijOnAndWeilLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitution
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilNormCont

theorem continuous_meanSquareNorm_weilRep_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  intro D ψ S T χS χT om μ 𝓕 hom hμ f₁ f₂ h₁ h₂
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b, hb⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₂ h₂ {1} isCompact_singleton
  have hb' : ∀ w, ‖f₂ w‖ ≤ b := fun w => by simpa using hb 1 rfl w
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₁ h₁ K hK
  unfold nrm2
  refine continuousAt_of_dominated (bound := fun _ => (c + b) ^ 2) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    exact ((((hom.om_pres p f₁ h₁).cont.sub h₂.cont).norm.pow 2).measurable).aestronglyMeasurable
  · filter_upwards [hK0] with p hp
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hc p hp w) (hb' w))) 2
  · refine Filter.Eventually.of_forall fun w => ?_
    exact (((hom.om_cont f₁ h₁ w).sub continuous_const).norm.pow 2).continuousAt

end GlobalTheory.WeilNormCont
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_nrm2_om_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  atlas_forward_decl GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_acts_on_pureTensors_placewise : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (g : GA D S) (h : GA D T), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  first | exact @GlobalTheory.PlaceTensor.PureOm.isPure_om | exact GlobalTheory.PlaceTensor.PureOm.isPure_om | (intros; apply GlobalTheory.PlaceTensor.PureOm.isPure_om <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerModel_coordinates_bijOn_and_weil_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ (m n : ℕ) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a (latO S T ΛS ΛT fun _ => True) κ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Set.BijOn (fun Φ => Tm (pull a κ Φ)) (GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v))) {f | IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f} ∧ ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ (γ : GL (Fin n) (Fv D.host.F v)) (δ : GL (Fin m) (Fv D.host.F v)), (∀ t, κ (actO S T g⁻¹ h⁻¹ t) = (δ⁻¹).val * κ t * γ.val) → ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), om (g, h) (Tm (pull a κ Φ)) = ((splitFacO χS χT x y : Circle) : ℂ) • Tm (pull a κ (linOm v γ δ Φ)) := by
  first | exact @GlobalTheory.SplitCoordModel.bijOn_and_om_linear | exact GlobalTheory.SplitCoordModel.bijOn_and_om_linear | (intros; apply GlobalTheory.SplitCoordModel.bijOn_and_om_linear <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceAdjointMatrix_isCoordinate_equivariant : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  first | exact @GlobalTheory.PlaceTensor.adjCo_isCoord | exact GlobalTheory.PlaceTensor.adjCo_isCoord | (intros; apply GlobalTheory.PlaceTensor.adjCo_isCoord <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_inner_eq_fockInnerProduct_mul_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ P Q, ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f P) (pureTensorO ψ θ S T sS sT BS BT f Q) = fockIp P Q * (nrm2 μ 𝓕 f : ℂ) := by
  first | exact @GlobalTheory.FockIsometry.ipO_pureTensorO | exact GlobalTheory.FockIsometry.ipO_pureTensorO | (intros; apply GlobalTheory.FockIsometry.ipO_pureTensorO <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_acts_on_fockVectors_by_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → ∀ c : ℂ, om (g, h) f = c • f → ∀ P, om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  first | exact @GlobalTheory.FockCompact.om_pureTensorO_compact | exact GlobalTheory.FockCompact.om_pureTensorO_compact | (intros; apply GlobalTheory.FockCompact.om_pureTensorO_compact <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumEven

theorem cartan_laws {k p : ℕ} {G s B Y : Matrix (Fin k) (Fin k) ℂ} (hB : IsONBasis G s B p) (hY : IsPMat p Y) :
    (∃ κ, IsKMat p κ ∧ B * κ * B⁻¹ = s) ∧ (B * Y * B⁻¹)ᴴ * G + G * (B * Y * B⁻¹) = 0 ∧
      s * (B * Y * B⁻¹) = -(B * Y * B⁻¹ * s) := by
  obtain ⟨ε, hε, hBG, hsB⟩ := hB
  obtain ⟨hYh, hY0⟩ := hY

  have hEE : (diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hEh : (diagonal fun a => (ε a : ℂ))ᴴ = diagonal fun a => (ε a : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]

  have hEY : (diagonal fun a => (ε a : ℂ)) * Y = -(Y * diagonal fun a => (ε a : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · rw [hY0 i j hij]
      simp
    · rcases hε i with ⟨hi, hip⟩ | ⟨hi, hip⟩ <;> rcases hε j with ⟨hj, hjp⟩ | ⟨hj, hjp⟩
      · exact absurd (iff_of_true hip hjp) hij
      · rw [hi, hj]
        push_cast
        ring
      · rw [hi, hj]
        push_cast
        ring
      · exact absurd (iff_of_false (not_lt.2 hip) (not_lt.2 hjp)) hij
  have hoff : ∀ i j, ¬ (i.val < p ↔ j.val < p) → (diagonal fun a => (ε a : ℂ)) i j = 0 := by
    intro i j hij
    apply Matrix.diagonal_apply_ne
    intro h
    subst h
    exact hij Iff.rfl
  generalize (diagonal fun a => (ε a : ℂ)) = E at hEE hEh hEY hoff hBG hsB

  have hdet : IsUnit B.det := by
    have h1 : (Bᴴ * G * B * E).det = 1 := by rw [hBG, hEE, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul] at h1
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at h1
    simp at h1
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hc3 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi', Matrix.conjTranspose_one]
  have hc4 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  have hc1 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, B⁻¹ * (B * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hc2 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Bᴴ * ((B⁻¹)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hc4, Matrix.one_mul]
  have hs : s = B * E * B⁻¹ := by
    calc s = s * B * B⁻¹ := by rw [Matrix.mul_assoc, hBi', Matrix.mul_one]
      _ = B * E * B⁻¹ := by rw [hsB]
  have hG : G = (B⁻¹)ᴴ * E * B⁻¹ := by
    rw [← hBG]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B⁻¹)ᴴ, hc3, Matrix.one_mul, hBi', Matrix.mul_one]
  subst hs hG
  refine ⟨⟨E, ⟨?_, hoff⟩, rfl⟩, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hEh, hEE]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hYh]
    simp only [Matrix.mul_assoc, hc1, hc2]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
  · simp only [Matrix.mul_assoc, hc1]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem atTau_oneP {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {s X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : IsCartanInv (gramAt D V τ) s) (hX : X ∈ lieAt V τ)
    (ha : s * X = -(X * s)) (t : ℝ) : atTau θ V τ s * oneP θ V τ X t = oneP θ V τ X (-t) * atTau θ V τ s := by
  obtain ⟨hss, hsU, -⟩ := hs
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hsU (GlobalTheory.Mem.Lift.exp_mem hX t),
    ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (GlobalTheory.Mem.Lift.exp_mem hX (-t)) hsU, GlobalTheory.FockKill.conj_exp hss ha t]

theorem ipO_smul_smul {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f g : Mx D m n → ℂ) :
    ipO μ 𝓕 (c • f) (c • g) = (Complex.normSq c : ℂ) * ipO μ 𝓕 f g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← Complex.mul_conj]
  ring

theorem coeff_even : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → BS τ * YS * (BS τ)⁻¹ ∈ lieAt S τ ∧ BT τ * YT * (BT τ)⁻¹ ∈ lieAt T τ ∧ ∀ f g, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ t : ℝ, ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT τ YS YT hYS hYT
  obtain ⟨⟨κS, hκS, hsS⟩, hlS, haS⟩ := cartan_laws (hbS τ) hYS
  obtain ⟨⟨κT, hκT, hsT⟩, hlT, haT⟩ := cartan_laws (hbT τ) hYT
  refine ⟨hlS, hlT, ?_⟩
  intro f g hf hvf hg hvg μ 𝓕 hμ t
  obtain ⟨mS, mT, hchar⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
  have hUS : sS τ ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ) := by
    obtain ⟨-, h, -⟩ := hcS τ
    exact h
  have hUT : sT τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    obtain ⟨-, h, -⟩ := hcT τ
    exact h
  have hssS : sS τ * sS τ = 1 := by
    obtain ⟨h, -, -⟩ := hcS τ
    exact h
  have hssT : sT τ * sT τ = 1 := by
    obtain ⟨h, -, -⟩ := hcT τ
    exact h

  have hmul : ∀ a b φ, om a (om b φ) = om (a * b) φ := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) φ) →
      om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) φ = c • φ :=
    ⟨_, fun φ hφ hvφ => hchar sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT φ hφ hvφ κS κT hκS hκT _ _
      (by rw [hsS]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ hUS)
      (by rw [hsT]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ hUT)⟩
  by_cases hf0 : f = 0
  · subst hf0
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO]

  have hkk : om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f) = f := by
    have h1 : ((1 : GA D S), (1 : GA D T)) = (1 : GA D S × GA D T) := rfl
    rw [hmul, Prod.mk_mul_mk, ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hUS hUS,
      ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hUT hUT, hssS, hssT, GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ,
      GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ, h1, map_one, Module.End.one_apply]
  rw [hc f hf hvf, map_smul, hc f hf hvf, smul_smul] at hkk
  have hcc : c * c = 1 := by
    by_contra hne
    apply hf0
    have h0 : (c * c - 1) • f = 0 := by rw [sub_smul, hkk, one_smul, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  have hn : (Complex.normSq c : ℂ) = 1 := by
    have h2 : Complex.normSq c * Complex.normSq c = 1 := by
      rw [← Complex.normSq_mul, hcc, Complex.normSq_one]
    have h3 : Complex.normSq c = 1 := by nlinarith [Complex.normSq_nonneg c]
    rw [h3, Complex.ofReal_one]

  have hconj : (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) *
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) =
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) *
      (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) := by
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, atTau_oneP hθ S τ (hcS τ) hlS haS (-t),
      atTau_oneP hθ T τ (hcT τ) hlT haT (-t), neg_neg]

  have hU : ∀ p φ φ', IsThetaFunO ψ S T φ → IsThetaFunO ψ S T φ' →
      ipO μ 𝓕 (om p φ) (om p φ') = ipO μ 𝓕 φ φ' := fun p φ φ' hφ hφ' =>
    GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hom μ 𝓕 hμ p φ φ' hφ hφ'
  calc ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g
      = ipO μ 𝓕 (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ))
          (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := (hU _ _ g (hom.om_pres _ f hf) hg).symm
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t)
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := by
      congr 1
      rw [hmul, hmul, hconj]
    _ = ipO μ 𝓕 (c • om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) (c • g) := by
      rw [hc f hf hvf, hc g hg hvg, map_smul]
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
      rw [ipO_smul_smul, hn, one_mul]

end GlobalTheory.VacuumEven
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_matrixCoefficient_even : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → BS τ * YS * (BS τ)⁻¹ ∈ lieAt S τ ∧ BT τ * YT * (BT τ)⁻¹ ∈ lieAt T τ ∧ ∀ f g, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ t : ℝ, ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
  atlas_forward_decl GlobalTheory.VacuumEven.coeff_even
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceTensor.GenPair

theorem exists_pairing {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (G : BoundedContinuousFunction Z ℂ) :
    ∃ L : BoundedContinuousFunction Z ℂ →L[ℂ] ℂ, ∀ F, L F = ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν := by
  have hint : ∀ F : BoundedContinuousFunction Z ℂ, MeasureTheory.Integrable (fun w => F w * (starRingEnd ℂ) (G w)) ν :=
    fun F => (F * star G).integrable ν
  refine ⟨LinearMap.mkContinuous
    { toFun := fun F => ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν
      map_add' := fun F F' => by
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint F) (hint F')
      map_smul' := fun c F => by
        simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ } ((ν Set.univ).toReal * ‖G‖) fun F => ?_, fun F => rfl⟩
  have hb : ∀ w, ‖F w * (starRingEnd ℂ) (G w)‖ ≤ ‖F‖ * ‖G‖ := fun w => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (F.norm_coe_le_norm w) (G.norm_coe_le_norm w) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hb)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc _ ≤ ‖F‖ * ‖G‖ * (ν Set.univ).toReal := by simpa [Measure.real] using this
    _ = _ := by ring

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.DefLift GlobalTheory.DefLift.Gen

theorem blk_sub_vecL {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} (Y : O → Matrix (Fin m) (Fin m) ℂ)
    (X : O → Matrix (Fin n) (Fin n) ℂ) (τ' : O) (u : Matrix (Fin m) (Fin n) ℂ) :
    (GlobalTheory.RealWeil.blk Y (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) X) *ᵥ
                 vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext p
  obtain ⟨⟨i, j⟩, τ⟩ := p
  have key : ∀ (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ)
      (v : (Fin m × Fin n) × O → ℂ), (GlobalTheory.RealWeil.blk b a *ᵥ v) ((i, j), τ) = (b τ * cpt v τ * a τ) i j :=
    fun b a v => by rw [← cpt_blk]; rfl
  have hc : cpt (vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ)) τ = (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) τ := rfl
  rw [Matrix.sub_mulVec, Pi.sub_apply, key, key, hc]
  show _ = (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) τ i j
  by_cases h : τ = τ'
  · subst h
    simp
  · simp [h]

open scoped Classical

variable {D : D7} {θ : InfFam D}

theorem oneP_zero (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : oneP θ V τ X 0 = 1 := by
  have h := GlobalTheory.Mem.Lift.oneP_add hθ hX 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel]
  exact GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX

theorem hasDerivAt_mM (hθ : IsInfFam θ) {S T : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hX : X ∈ lieAt S τ) {Y : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hY : Y ∈ lieAt T τ) (k l : GlobalTheory.RealWeil.Ix S T) :
    HasDerivAt (fun t : ℝ => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t) k l)
      ((GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X) :
        Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) k l) 0 := by
  obtain ⟨⟨i, j⟩, τ₁⟩ := k
  obtain ⟨⟨i', j'⟩, τ₂⟩ := l
  have hS : ∀ t : ℝ, (oneP θ S τ X t)⁻¹ = oneP θ S τ X (-t) := GlobalTheory.PlaceTensor.GenPair.oneP_inv hθ hX
  simp only [mM_apply, hS, GlobalTheory.RealWeil.blk, Matrix.sub_apply, Matrix.blockDiagonal_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h : τ₁ = τ₂
  · subst h
    simp only [if_true]
    have hb := hasDerivAt_comp hθ hY τ₁ i i'
    have ha0 := hasDerivAt_comp hθ hX τ₁ j' j
    have ha : HasDerivAt (fun t : ℝ => Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X t)) j' j)
        ((Pi.single τ X : D.what₂.Tau → _) τ₁ j' j) (-0) := by rw [neg_zero]; exact ha0
    have hT0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt T (oneP θ T τ Y 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]; exact compAt_fin (one_mem _) τ₁
    have hS0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX]; exact compAt_fin (one_mem _) τ₁
    refine (hb.mul (ha.scomp 0 (hasDerivAt_neg 0))).congr_deriv ?_
    simp only [Function.comp_apply, neg_zero, hT0, hS0, Matrix.one_apply]
    split_ifs <;> simp <;> ring
  · simp only [h, if_false, sub_zero]
    exact hasDerivAt_const _ _

theorem exists_generator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  intro D ψ θ S T χS χT om hW hθ τ X hX Y hY
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hweak : GlobalTheory.Ker.IsWeak ψ S T om := GlobalTheory.Ker.isWeak_of_datum hW
  have hcont : OmCont ψ S T om := hW.om_cont
  have hγc : Continuous fun t : ℝ => (oneP θ S τ X t, oneP θ T τ Y t) :=
    (GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
  have hγa : ∀ s t : ℝ, (oneP θ S τ X (s + t), oneP θ T τ Y (s + t)) =
      (oneP θ S τ X s, oneP θ T τ Y s) * (oneP θ S τ X t, oneP θ T τ Y t) := fun s t => by
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY]; rfl
  have hγm : ∀ t : ℝ, oneP θ S τ X t ∈ GinfC S ∧ oneP θ T τ Y t ∈ GinfC T := fun t =>
    ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩
  obtain ⟨lam, hlam⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ hσ ψ hψ S T om hweak hcont
    (fun t => (oneP θ S τ X t, oneP θ T τ Y t)) hγc hγa hγm _
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  have h0 : mM θ S T (oneP θ S τ X 0, oneP θ T τ Y 0) = 1 := by
    rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX, GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]
    exact (mM θ S T).map_one
  have hlie := GlobalTheory.Mem.Lift.GenZero.lie_of_path (HM S T)
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X))
    (fun t => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t)) h0 (fun t => mM_unitary hθ _)
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.DefLift.Gen.exists_extension hσ hψ
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) lam
  refine ⟨Gn, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    ⟨GlobalTheory.RealWeil.toB hψ f hf, GlobalTheory.RealWeil.coe_toB hψ f hf⟩
  obtain ⟨hnt, hGF⟩ := hGn F hf
  have hAt : IsThetaFunO ψ S T ((nOp (rhoV hψ σ S T) (HM S T)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
      + lam • F).1 : WO S T → ℂ) := by
    rw [← GlobalTheory.DefLift.Gen.coe_add_smul]
    exact GlobalTheory.OrientedHeis.theta_add hnt (GlobalTheory.OrientedHeis.theta_smul lam hf)
  have hcomm : ∀ (τ' : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u F.1) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn F.1) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ'
        ((Pi.single τ Y : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) τ' * u -
          u * (Pi.single τ X : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) τ') F.1 := by
    intro τ' u
    have hdt := GlobalTheory.DefLift.Gen.theta_dH hσ hψ F hf
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    have e2 := (hGn _ hdt).2
    have e4 := nOp_add_comm HM_herm HM_det hlie (isHeis_rhoB hσ hψ) lam
      (GlobalTheory.RealWeil.sm_of_theta hσ hψ F hf) (GlobalTheory.RealWeil.sm_of_theta hσ hψ _ hnt)
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    rw [← GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' u, e2, hGF, ← GlobalTheory.DefLift.Gen.coe_dH hσ hψ _ hAt τ' u, e4,
      GlobalTheory.PlaceTensor.GenPair.blk_sub_vecL, GlobalTheory.DefLift.Gen.coe_add_sub]
    exact GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' _
  obtain ⟨u, hu1, hu2⟩ := hlam F hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hGF]; exact hAt
  · intro v
    rw [hcomm, Pi.single_eq_same, Pi.single_eq_same]
  · intro τ' h v
    have hc := hcomm τ' v
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.zero_mul, Matrix.mul_zero, sub_zero,
      GlobalTheory.DefLift.Gen.dRho_zero hσ hψ F hf] at hc
    exact sub_eq_zero.mp hc
  · intro w
    have h2 : HasDerivAt (fun t => ev _ _ w (u t)) (ev _ _ w (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F)) 0 :=
      ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [ev_apply, hu1] at h2
    rw [hGF]; exact h2
  · intro μ 𝓕 hμ g hg
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
      rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨L, hL⟩ := GlobalTheory.PlaceTensor.GenPair.exists_pairing (μ.restrict 𝓕) (GlobalTheory.RealWeil.toB hψ g hg).1
    have h2 : HasDerivAt (fun t => L (u t).1) (L (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F).1) 0 :=
      ((L.comp (BB ψ S T).subtypeL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [hL, hu1, GlobalTheory.RealWeil.coe_toB] at h2
    rw [hGF]; exact h2

end GlobalTheory.PlaceTensor.GenPair

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_oneParameter_generator_commutators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  atlas_forward_decl GlobalTheory.PlaceTensor.GenPair.exists_generator
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_operator_acts_by_noncompact_quadratic_ops : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ Gn : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (BT τ * YT * (BT τ)⁻¹ * u - u * (BS τ * YS * (BS τ)⁻¹)) f) ∧ ∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → (∀ g, IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ipO μ 𝓕 (Gn f) g = 0) → ∀ P, Gn (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT f (fockP τ (pS τ) (pT τ) YS YT P) := by
  first | exact @GlobalTheory.FockLieQuad.acts_by_fockP | exact GlobalTheory.FockLieQuad.acts_by_fockP | (intros; apply GlobalTheory.FockLieQuad.acts_by_fockP <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_thetaLattice_halves_selfDual_frames : ∀ D : D7, SplitLattice D := by
  first | exact @GlobalTheory.SplitLatticeHalves.splitLattice | exact GlobalTheory.SplitLatticeHalves.splitLattice | (intros; apply GlobalTheory.SplitLatticeHalves.splitLattice <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum : ∀ D : D7, InertVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.inertVacuumFixed | exact GlobalTheory.PlaceTensor.inertVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.inertVacuumFixed <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_latticeStabilisers_fix_weilVacuum : ∀ D : D7, SplitVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.splitVacuumFixed | exact GlobalTheory.PlaceTensor.splitVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.splitVacuumFixed <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_pureTensors : ∀ D : D7, FockPure D := by
  first | exact @GlobalTheory.FockPureTensor.fockPure | exact GlobalTheory.FockPureTensor.fockPure | (intros; apply GlobalTheory.FockPureTensor.fockPure <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaLift_localVector : ∀ D : D7, ThetaVecLocal D := by
  first | exact @GlobalTheory.AdjVecLocal.thetaVecLocal | exact GlobalTheory.AdjVecLocal.thetaVecLocal | (intros; apply GlobalTheory.AdjVecLocal.thetaVecLocal <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStepVector_localPureTensor : ∀ D : D7, StepVecLocal D := by
  first | exact @GlobalTheory.StepVec.stepVecLocal | exact GlobalTheory.StepVec.stepVecLocal | (intros; apply GlobalTheory.StepVec.stepVecLocal <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem unitary (D : D7) : Unitary D := by
  intro ψ S T χS χT om hW
  have hstd := hW.std
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨⟨(μ₀, 𝓕₀), h₀⟩, fun q hq f₁ f₂ hf₁ hf₂ => ?_⟩
  have L := GlobalTheory.T.theta_inner_product_hermitian D ψ S T q.1 q.2 hstd hq f₁ f₂ hf₁ hf₂
  refine ⟨fun c => GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul c hf₁) hf₂, L.1, L.2.2.2.2.2.1,
    L.2.2.2.2.2.2.2, fun w => ⟨?_, (L.2.2.2.2.2.2.1 w).1⟩, fun p => ⟨hW.om_pres p f₁ hf₁, ?_⟩,
    GlobalTheory.T.continuous_nrm2_om_sub D ψ S T χS χT om q.1 q.2 hW hq f₁ f₂ hf₁ hf₂⟩
  · exact (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₁ hf₁
  · exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW q.1 q.2 hq p f₁ f₂ hf₁ hf₂

theorem restrictedTensor (D : D7) : RestrictedTensor D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  have hstd := base_std hB
  have hinf := base_inf hB
  refine ⟨fun p f hf => ⟨((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hstd hinf f hf.1).2 p hf).1,
      GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW hinf p f hf⟩,
    fun x hx => GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x hx, fun f hf ε hε => ?_,
    fun x f hx => ⟨fun w => GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w,
      fun g h => GlobalTheory.T.weilRep_acts_on_pureTensors_placewise D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x f hx g h⟩⟩
  obtain ⟨f', hf', hlt⟩ := GlobalTheory.T.heisenberg_translates_span_dense_thetaFunctions D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ f hf ε hε
  refine ⟨f', Submodule.span_mono ?_ hf', hlt⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨_, GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ (fun _ => f₀) f₀
    (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1 w⟩

theorem coeffProduct (D : D7) : CoeffProduct D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ x₂ f₂ h₁ h₂ g h
  exact GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ x₂ _ f₂
    (GlobalTheory.T.weilRep_acts_on_pureTensors_placewise D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ h₁ g h) h₂

theorem cA_cA {D : D7} {e : AE D} {p : Place D} (h : e + cA D e = idem D p) : cA D (cA D e) = e := by
  have hp : cA D (idem D p) = idem D p := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p
  have h2 : cA D e + cA D (cA D e) = cA D e + e := by
    rw [← map_add, h, hp, ← h, add_comm]
  exact add_left_cancel h2

theorem isSplitIdem_cA {D : D7} {e : AE D} {p : Place D} (he : IsSplitIdem D e) (h : e + cA D e = idem D p) :
    IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, hε⟩ := he
  have hcc := cA_cA h
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [hcc, mul_comm, h2]
  · rw [hcc, add_comm, hε]

theorem splitModel (D : D7) : SplitModel D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := GlobalTheory.T.splitPlace_matrix_coordinate_on_half D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  refine ⟨(GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v e he.1 he.2.1).1, fun Tm hTm => ?_⟩
  have M := GlobalTheory.T.schrodingerModel_coordinates_bijOn_and_weil_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e e he.1 he.2.1 (Or.inl rfl)
    T.rank S.rank (mapCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalf_eq_pull]
  exact ⟨M.1, fun ν hν => GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v e he.1 T.rank S.rank
    (mapCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ S BS g) (grpCo φ T BT h) (fun t => hC.2 g h t) Φ hΦ⟩

theorem splitModelAdj (D : D7) : SplitModelAdj D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := GlobalTheory.T.splitPlaceAdjointMatrix_isCoordinate_equivariant D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hs : IsSplitIdem D (cA D e) := isSplitIdem_cA he.1 he.2.1
  have hsum : cA D e + cA D (cA D e) = idem D (.inl v) := by
    rw [cA_cA he.2.1, add_comm]
    exact he.2.1
  refine ⟨(GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v (cA D e) hs hsum).1, fun Tm hTm => ?_⟩
  have M := GlobalTheory.T.schrodingerModel_coordinates_bijOn_and_weil_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e (cA D e) he.1 he.2.1 (Or.inr rfl)
    S.rank T.rank (adjCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalfAdj_eq_pull]
  exact ⟨M.1, fun ν hν => GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v (cA D e) hs S.rank T.rank
    (adjCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ T BT h) (grpCo φ S BS g) (fun t => hC.2 g h t) Φ hΦ⟩

theorem deriv_eq_zero_of_even {c : ℝ → ℂ} {a : ℂ} (h : HasDerivAt c a 0) (he : ∀ t, c (-t) = c t) : a = 0 := by
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id' (0 : ℝ)).neg
  have h0 : HasDerivAt c a (-(0 : ℝ)) := by rwa [neg_zero]
  have h1 := h0.scomp (0 : ℝ) hn
  have h2 : (c ∘ fun t : ℝ => -t) = c := funext fun t => he t
  rw [h2] at h1
  have h3 := h.unique h1
  rw [neg_one_smul] at h3
  linear_combination h3 / 2

private theorem exists_conj_mul_eq_mul {ι : Type*} {n : ℕ} (C C' : ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i, C i * C' i = 1)
    (s B : ι → Matrix (Fin n) (Fin n) ℂ) :
    ∃ s' B' : ι → Matrix (Fin n) (Fin n) ℂ, (∀ i, s' i * C i = C i * s i) ∧ ∀ i, B' i = C i * B i := by
  refine ⟨fun i => C i * s i * C' i, fun i => C i * B i, fun i => ?_, fun i => rfl⟩
  have h' : C' i * C i = 1 := mul_eq_one_comm.mp (h i)
  simp only [Matrix.mul_assoc, h', Matrix.mul_one]

theorem fockModel (D : D7) : FockModel D := by
  intro ψ θ S T χS χT om hW hθ τ
  obtain ⟨mS, mT, hm⟩ := GlobalTheory.T.fockVacuum_maximalCompact_character_realPlace D ψ θ S T χS χT om hW hθ τ
  refine ⟨mS, mT, ?_⟩
  intro sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac P
  have hstd := hW.std
  have hPT : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) := by
    intro Q
    obtain ⟨sS', BS', hS', hBS'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D S)) sS BS
    obtain ⟨sT', BT', hT', hBT'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D T)) sT BT
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS' BS BS' sT sT' BT BT' 1 1
      hS' hT' hBS' hBT' f hf Q).1
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨hPT P, fun μ 𝓕 hμ Q => GlobalTheory.T.fockVectors_inner_eq_fockInnerProduct_mul_norm D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT
      f hf hvac μ 𝓕 hμ P Q,
    fun κS κT hκS hκT g h hg hh => GlobalTheory.T.maximalCompact_acts_on_fockVectors_by_substitution D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT
      hBS hBT f hf τ κS κT hκS hκT g h hg hh _
      (hm sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac κS κT hκS hκT g h hg hh) P,
    fun YS YT hYS hYT w => ?_⟩
  have hL := GlobalTheory.T.fockVacuum_matrixCoefficient_even D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT
  obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_oneParameter_generator_commutators D ψ θ S T χS χT om hW hθ τ _ hL.1 _ hL.2.1

  have key := GlobalTheory.T.fock_operator_acts_by_noncompact_quadratic_ops D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT μ₀ 𝓕₀ h₀ Gn
    (fun f' hf' => ⟨(hGn f' hf').1, (hGn f' hf').2.1, (hGn f' hf').2.2.1⟩) f hf hvac
    (fun g hg hgv => deriv_eq_zero_of_even ((hGn f hf).2.2.2.2 μ₀ 𝓕₀ h₀ g hg)
      (fun t => hL.2.2 f g hf hvac hg hgv μ₀ 𝓕₀ h₀ t)) P
  rw [← key]
  exact (hGn _ (hPT P)).2.2.2.1 w

theorem placeModels : ∀ D : D7, PlaceModels D := fun D =>
  ⟨unitary D, restrictedTensor D, coeffProduct D, splitModel D, splitModelAdj D, GlobalTheory.T.splitPlace_thetaLattice_halves_selfDual_frames D, GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum D,
    GlobalTheory.T.splitPlace_latticeStabilisers_fix_weilVacuum D, fockModel D, GlobalTheory.T.fockVectors_pureTensors D, GlobalTheory.T.definiteThetaLift_localVector D, GlobalTheory.T.thetaChainStepVector_localPureTensor D⟩

end GlobalTheory.PlaceTensor
end
