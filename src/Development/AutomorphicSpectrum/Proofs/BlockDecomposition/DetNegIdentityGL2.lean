import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIntegrandIntegrable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerInducedOfFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionInvariance
import GroundTheory.HeightsAndTheta.Theta.WeilNonarchProps
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHolomorphyInParameter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightPartialFourierSupportBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalZetaOfAnnulusFunction

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.HaarTinv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem tinv_mul (g h : GL (Fin 2) F) : tinv (g * h) = tinv g * tinv h := by
  apply Units.ext
  change ((g * h)⁻¹ : GL (Fin 2) F).valᵀ = (g⁻¹ : GL (Fin 2) F).valᵀ * (h⁻¹ : GL (Fin 2) F).valᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem tinv_tinv (g : GL (Fin 2) F) : tinv (tinv g) = g := by
  apply Units.ext
  change (g.valᵀ)ᵀ = g.val
  simp

theorem continuous_tinv : Continuous (tinv : GL (Fin 2) F → GL (Fin 2) F) := by
  rw [Units.continuous_iff]
  exact ⟨(Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) F)).matrix_transpose,
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_transpose⟩

def tinvEquiv : GL (Fin 2) F ≃* GL (Fin 2) F where
  toFun := tinv
  invFun := tinv
  left_inv := tinv_tinv
  right_inv := tinv_tinv
  map_mul' := tinv_mul

theorem tinv_mem_iff (k : GL (Fin 2) F) :
    tinv k ∈ GLnLocal.integralGL F 2 ↔ k ∈ GLnLocal.integralGL F 2 := by
  have key : ∀ {k : GL (Fin 2) F}, k ∈ GLnLocal.integralGL F 2 → tinv k ∈ GLnLocal.integralGL F 2 := by
    intro k hk
    obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
    exact (GLnLocal.mem_integralGL_iff F 2).2 ⟨fun i j => h2 j i, fun i j => h1 j i⟩
  exact ⟨fun h => by simpa [tinv_tinv] using key h, key⟩

variable [MeasurableSpace F] [BorelSpace F]

theorem map_tinv_hG (ψ : AddChar F Circle) :
    Measure.map (tinv : GL (Fin 2) F → GL (Fin 2) F) (LFS.hG ψ) = LFS.hG ψ := by
  have hc : Continuous (tinv : GL (Fin 2) F → GL (Fin 2) F) := continuous_tinv
  have hm : Measurable (tinvEquiv (F := F)) := hc.measurable
  haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  haveI hH : ((LFS.hG ψ).map (tinvEquiv (F := F))).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map (LFS.hG ψ) tinvEquiv hc hc
  change (LFS.hG ψ).map (tinvEquiv (F := F)) = LFS.hG ψ
  set μ := LFS.hG ψ with hμ
  set K := GLnLocal.integralGL F 2 with hKdef
  have hKo : IsOpen (K : Set (GL (Fin 2) F)) := GLnLocal.isOpen_integralGL F 2
  have hK0 : μ K ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (tinvEquiv (F := F))) μ
  have hpre : (tinvEquiv (F := F)) ⁻¹' (K : Set (GL (Fin 2) F)) = K := by
    ext k
    exact tinv_mem_iff k
  have hmap : (μ.map (tinvEquiv (F := F))) K = μ K := by
    rw [Measure.map_apply hm hKo.measurableSet]
    exact congrArg μ hpre
  have hs : Measure.haarScalarFactor (μ.map (tinvEquiv (F := F))) μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin 2) F) => ν K) e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [hmap] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hs, one_smul]


def tinvHomeo : GL (Fin 2) F ≃ₜ GL (Fin 2) F where
  toEquiv := (tinvEquiv (F := F)).toEquiv
  continuous_toFun := continuous_tinv
  continuous_invFun := continuous_tinv

theorem integral_tinv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : AddChar F Circle)
    (f : GL (Fin 2) F → E) : ∫ g, f (tinv g) ∂LFS.hG ψ = ∫ g, f g ∂LFS.hG ψ := by
  have he : MeasurableEmbedding (tinv : GL (Fin 2) F → GL (Fin 2) F) :=
    (tinvHomeo (F := F)).measurableEmbedding
  conv_rhs => rw [← map_tinv_hG ψ]
  exact (he.integral_map f).symm


end GlobalTheory.CompanionTheory.GL2LocalData.HaarTinv
end
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac

open scoped NNReal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem det_ne (h : GL (Fin 2) F) : (h.val).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero

def kr (a b : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F :=
  Matrix.kroneckerMap (· * ·) a bᵀ

theorem toM_kr (a b : Matrix (Fin 2) (Fin 2) F) (X : Fin 2 × Fin 2 → F) :
    toM (kr a b *ᵥ X) = a * toM X * b := by
  ext i j
  simp only [toM, kr, Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  ring

theorem det_kr (a b : Matrix (Fin 2) (Fin 2) F) : (kr a b).det = a.det ^ 2 * b.det ^ 2 := by
  have := Matrix.det_kronecker a bᵀ
  simpa [kr, Matrix.kronecker, Matrix.det_transpose] using this

theorem pair_eq (N A : Matrix (Fin 2) (Fin 2) F) :
    ∑ i, ∑ j, N i j * A i j = Matrix.trace (N * Aᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

theorem c_val : (dg2 (-1) (-1) : GL (Fin 2) F).val = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem c_inv : (dg2 (-1) (-1) : GL (Fin 2) F)⁻¹ = dg2 (-1) (-1) := by
  apply inv_eq_of_mul_eq_one_left
  apply Units.ext
  rw [Units.val_mul, c_val]
  simp

theorem first_val (h z : GL (Fin 2) F) :
    (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val = -(z.valᵀ * w2.val * h.val) := by
  have : (tinv (dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val = -z.valᵀ := by
    show (((dg2 (-1) (-1) * z)⁻¹)⁻¹ : GL (Fin 2) F).valᵀ = _
    rw [inv_inv, Units.val_mul, c_val]
    simp
  rw [Units.val_mul, Units.val_mul, this]
  simp

theorem second_val (z : GL (Fin 2) F) :
    ((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val = -(z⁻¹ : GL (Fin 2) F).val := by
  rw [_root_.mul_inv_rev, c_inv, Units.val_mul, c_val]
  simp

theorem tinv_mul_transpose (h : GL (Fin 2) F) : (tinv h).val * h.valᵀ = 1 := by
  show (h⁻¹ : GL (Fin 2) F).valᵀ * h.valᵀ = 1
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]
  simp

theorem pair_sub (h z : GL (Fin 2) F) (M : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace (((z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val) * (-(z.valᵀ * w2.val * h.val))ᵀ)
      = -(M 0 1 + M 1 0) := by
  have e : ((z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val) * (-(z.valᵀ * w2.val * h.val))ᵀ
      = -((z⁻¹ : GL (Fin 2) F).val * (M * w2.val * z.val)) := by
    have : (z.valᵀ * w2.val * h.val)ᵀ = h.valᵀ * (w2.valᵀ * z.val) := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [Matrix.transpose_neg, this, Matrix.mul_neg]
    congr 1
    have w2t : (w2 : GL (Fin 2) F).valᵀ = w2.val := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w2]
    rw [w2t]
    calc _ = (z⁻¹ : GL (Fin 2) F).val * M * ((tinv h).val * h.valᵀ) * (w2.val * z.val) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [tinv_mul_transpose]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [e, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, w2]

theorem modulus_inv_det (z : GL (Fin 2) F) :
    modulus ((z⁻¹ : GL (Fin 2) F).val).det = (modulus (z.val).det)⁻¹ := by
  have h : ((z⁻¹ : GL (Fin 2) F).val).det = ((z.val).det)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]
    simp
  rw [h, modulus_inv]

theorem modulus_tinv_det (h : GL (Fin 2) F) :
    modulus ((tinv h).val).det = (modulus (h.val).det)⁻¹ := by
  show modulus ((h⁻¹ : GL (Fin 2) F).valᵀ).det = _
  rw [Matrix.det_transpose, modulus_inv_det]

theorem mp_neg_two (g : GL (Fin 2) F) :
    mp (GeneralLinearGroup.det g) (-2) = ((((modulus (g.val).det)⁻¹ ^ 2 : ℝ≥0) : ℝ) : ℂ) := by
  have : ((GeneralLinearGroup.det g : Fˣ) : F) = (g.val).det := by
    simp only [GeneralLinearGroup.val_det_apply]
  unfold mp
  rw [this, Complex.cpow_neg, Complex.cpow_ofNat]
  push_cast
  rw [inv_pow]

noncomputable def gI (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (Y : Matrix (Fin 2) (Fin 2) F)
    (y : Fin 2 → F) (N : Fin 2 × Fin 2 → F) : ℂ :=
  Φ (cat3 (toM N) y) * (ψ (∑ i, ∑ j, N (i, j) * Y i j) : ℂ)

theorem dFT_eq (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F) :
    dFT ψ Φ (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val
        (((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val *ᵥ e1) =
      ∫ N, gI ψ Φ (-(z.valᵀ * w2.val * h.val)) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) N
        ∂GroundTheory.Heights₂.Theta.selfDualPi (Fin 2 × Fin 2) ψ := by
  rw [first_val, second_val, Matrix.neg_mulVec]
  unfold dFT
  simp only [neg_neg]
  rfl

theorem Rpart_eq (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F) :
    Rpart ψ (Pf Φ h z) =
      ∫ X, gI ψ Φ (-(z.valᵀ * w2.val * h.val)) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1)
          (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val *ᵥ X)
        ∂GroundTheory.Heights₂.Theta.selfDualPi (Fin 2 × Fin 2) ψ := by
  unfold Rpart
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hM := toM_kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val X
  have hp : ∑ i, ∑ j, (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val *ᵥ X) (i, j) *
        (-(z.valᵀ * w2.val * h.val) : Matrix (Fin 2) (Fin 2) F) i j = -(X (0, 1) + X (1, 0)) := by
    have h1 : ∑ i, ∑ j, toM (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val *ᵥ X) i j *
        (-(z.valᵀ * w2.val * h.val) : Matrix (Fin 2) (Fin 2) F) i j = -(X (0, 1) + X (1, 0)) := by
      rw [pair_eq, hM, pair_sub]
      rfl
    exact h1
  simp only [gI, Pf, hM, hp]

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F),
    dFT ψ Φ (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val
        (((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val *ᵥ e1) =
      mp (GeneralLinearGroup.det z) (-2) * mp (GeneralLinearGroup.det h) (-2) *
        Rpart ψ (Pf Φ h z) := by
  intro F _ _ _ _ _ _ ψ _ Φ h z
  have hP : (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val).det ≠ 0 := by
    rw [det_kr]
    exact mul_ne_zero (pow_ne_zero _ (det_ne _)) (pow_ne_zero _ (det_ne _))
  have key := GroundTheory.Heights₂.Theta.integral_comp_mulVec (ψ := ψ) hP
    (gI ψ Φ (-(z.valᵀ * w2.val * h.val)) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1))
  have hm : modulus (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val).det =
      (modulus (z.val).det)⁻¹ ^ 2 * (modulus (h.val).det)⁻¹ ^ 2 := by
    rw [det_kr, modulus_mul, pow_two, pow_two, modulus_mul, modulus_mul, modulus_inv_det,
      modulus_tinv_det, pow_two, pow_two]
  rw [dFT_eq, Rpart_eq, key, mp_neg_two, mp_neg_two, ← mul_assoc]
  have hc : (((((modulus (z.val).det)⁻¹ ^ 2 : ℝ≥0) : ℝ) : ℂ) *
      ((((modulus (h.val).det)⁻¹ ^ 2 : ℝ≥0) : ℝ) : ℂ)) *
      ((((modulus (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val).det)⁻¹ : ℝ≥0) : ℝ) : ℂ) = 1 := by
    have h0 : (modulus (z.val).det)⁻¹ ^ 2 * (modulus (h.val).det)⁻¹ ^ 2 ≠ 0 :=
      hm ▸ modulus_ne_zero hP
    have h1 := mul_inv_cancel₀ h0
    rw [hm]
    exact_mod_cast h1
  rw [hc, one_mul]

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_weyl_transpose_inverse : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F), dFT ψ Φ (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val (((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val *ᵥ e1) = mp (GeneralLinearGroup.det z) (-2) * mp (GeneralLinearGroup.det h) (-2) * Rpart ψ (Pf Φ h z) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac.main
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def cellU (F : Type) [Field F] : Set ((Fin 2 → F) × F × F) := {p | p.2.2 ≠ 0 ∧ p.1 1 ≠ 0}

theorem isOpen_cellU : IsOpen (cellU F) := by
  have h1 : Continuous fun p : (Fin 2 → F) × F × F => p.2.2 := continuous_snd.snd
  have h2 : Continuous fun p : (Fin 2 → F) × F × F => p.1 1 := (continuous_apply 1).comp continuous_fst
  exact (isOpen_compl_singleton.preimage h1).inter (isOpen_compl_singleton.preimage h2)

def cellG (p : cellU F) : GL (Fin 2) F :=
  uni2 p.1.2.1 * dg2 (Units.mk0 p.1.2.2 p.2.1) 1 * hr p.1.1

theorem continuous_cellG : Continuous (cellG : cellU F → GL (Fin 2) F) := by
  have he : Topology.IsEmbedding (GJHaar.ch : GL (Fin 2) F → Fin 2 × Fin 2 → F) :=
    (Measures.glChart F 2).isOpenEmbedding.isEmbedding
  rw [he.continuous_iff]
  have hy : Continuous fun p : cellU F => p.1.2.2 := continuous_subtype_val.snd.snd
  have hx : Continuous fun p : cellU F => p.1.2.1 := continuous_subtype_val.snd.fst
  have h0 : Continuous fun p : cellU F => p.1.1 0 := (continuous_apply 0).comp continuous_subtype_val.fst
  have h1 : Continuous fun p : cellU F => p.1.1 1 := (continuous_apply 1).comp continuous_subtype_val.fst
  have hc : (GJHaar.ch ∘ cellG : cellU F → _) = fun p =>
      GJHaar.ent p.1.1 (p.1.2.1 * p.1.1 1) (p.1.2.2 / p.1.1 1 + p.1.2.1 * p.1.1 0) := by
    funext p
    exact GJHaar.ch_g _ _ p.2.2
  rw [hc]
  refine continuous_pi fun ij => ?_
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j
  · exact (hy.div h1 fun p => p.2.2).add (hx.mul h0)
  · exact hx.mul h1
  · exact h0
  · exact h1

end GlobalTheory.CompanionTheory.GJTwo
end
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in

def cellPsi (p : (Fin 2 → F) × F × F) : GL (Fin 2) F :=
  if h : p ∈ cellU F then cellG ⟨p, h⟩ else 1

def cellD (p : (Fin 2 → F) × F × F) : ℝ≥0 := ((modulus p.2.2 : ℝ) ^ (-2 : ℤ)).toNNReal

def cellNu (ψ : AddChar F Circle) : Measure ((Fin 2 → F) × F × F) :=
  ((cM ψ).restrict (cellU F)).withDensity fun p => (cellD p : ℝ≥0∞)

theorem measurable_cellPsi : Measurable (cellPsi : (Fin 2 → F) × F × F → GL (Fin 2) F) := by
  have hU : MeasurableSet (cellU F) := isOpen_cellU.measurableSet
  refine measurable_of_restrict_of_restrict_compl hU ?_ ?_
  · have he : (cellU F).domRestrict (cellPsi : _ → GL (Fin 2) F) = cellG := by
      funext p
      exact dif_pos p.2
    rw [he]
    exact continuous_cellG.measurable
  · have he : ((cellU F)ᶜ).domRestrict (cellPsi : _ → GL (Fin 2) F) = fun _ => 1 := by
      funext p
      exact dif_neg p.2
    rw [he]
    exact measurable_const

theorem measurable_cellD : Measurable (cellD : (Fin 2 → F) × F × F → ℝ≥0) := by
  have hm : Measurable fun p : (Fin 2 → F) × F × F => (modulus p.2.2 : ℝ) :=
    (NNReal.continuous_coe.comp (continuous_modulus.comp continuous_snd.snd)).measurable
  have he : (cellD : (Fin 2 → F) × F × F → ℝ≥0) =
      fun p => (((modulus p.2.2 : ℝ) ^ 2)⁻¹).toNNReal := by
    funext p
    simp only [cellD, _root_.zpow_neg]
    norm_cast
  rw [he]
  exact (hm.pow_const 2).inv.real_toNNReal

theorem lintegral_cell (hm : GJm1) {ψ : AddChar F Circle} (hψ : IsStd ψ)
    (f : GL (Fin 2) F → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂LFS.hG ψ =
      ∫⁻ p, (cellU F).indicator (fun p => f (cellPsi p) * (cellD p : ℝ≥0∞)) p ∂cM ψ := by
  have hU : MeasurableSet (cellU F) := isOpen_cellU.measurableSet
  have hG : Measurable ((cellU F).indicator (fun p => f (cellPsi p) * (cellD p : ℝ≥0∞))) :=
    ((hf.comp measurable_cellPsi).mul measurable_cellD.coe_nnreal_ennreal).indicator hU
  refine (hm F ψ hψ f hf).trans ?_
  rw [cM, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun r => ?_
  have h2 : Measurable fun q : F × F =>
      (cellU F).indicator (fun p => f (cellPsi p) * (cellD p : ℝ≥0∞)) (r, q) :=
    hG.comp measurable_prodMk_left
  rw [lintegral_prod _ h2.aemeasurable]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  by_cases h : y = 0 ∨ r 1 = 0
  · have hn : (r, x, y) ∉ cellU F := fun hc => h.elim hc.1 hc.2
    rw [dif_pos h]
    exact (Set.indicator_of_notMem hn _).symm
  · have hn : (r, x, y) ∈ cellU F := ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
    rw [dif_neg h]
    refine Eq.trans ?_ (Set.indicator_of_mem hn _).symm
    simp only [cellPsi, dif_pos hn]
    rfl

theorem hG_eq_map (hm : GJm1) {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    LFS.hG ψ = Measure.map cellPsi (cellNu ψ) := by
  have hU : MeasurableSet (cellU F) := isOpen_cellU.measurableSet
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have h3 := lintegral_withDensity_eq_lintegral_mul ((cM ψ).restrict (cellU F))
    (measurable_cellD (F := F)).coe_nnreal_ennreal (hf.comp measurable_cellPsi)
  rw [lintegral_map hf measurable_cellPsi, lintegral_cell hm hψ f hf, cellNu,
    lintegral_indicator hU]
  refine Eq.trans ?_ h3.symm
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact mul_comm _ _

theorem Ff_eq (f : GL (Fin 2) F → ℂ) :
    Ff f = (cellU F).indicator fun p => (cellD p : ℝ) • (f ∘ cellPsi) p := by
  funext p
  by_cases h : p.2.2 = 0 ∨ p.1 1 = 0
  · have hn : p ∉ cellU F := fun hc => h.elim hc.1 hc.2
    rw [Set.indicator_of_notMem hn, Ff, dif_pos h]
  · have hn : p ∈ cellU F := ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
    rw [Set.indicator_of_mem hn, Ff, dif_neg h, Function.comp_apply, cellPsi, dif_pos hn,
      Complex.real_smul, mul_comm, cellD, Real.coe_toNNReal _ (by positivity)]
    rfl

end GlobalTheory.CompanionTheory.GJTwo
end
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integrable_Ff {ψ : AddChar F Circle} (hψ : IsStd ψ) {f : GL (Fin 2) F → ℂ}
    (hf : Integrable f (LFS.hG ψ)) :
    Integrable (GJTwo.Ff f) (GJTwo.cM ψ) ∧
      ∫ g, f g ∂LFS.hG ψ = ∫ p, GJTwo.Ff f p ∂GJTwo.cM ψ := by
  have hU : MeasurableSet (GJTwo.cellU F) := GJTwo.isOpen_cellU.measurableSet
  have hmap := GJTwo.hG_eq_map GJHaar.gjm1 hψ
  rw [hmap] at hf
  have hs := hf.aestronglyMeasurable
  constructor
  · rw [integrable_map_measure hs GJTwo.measurable_cellPsi.aemeasurable, GJTwo.cellNu,
      integrable_withDensity_iff_integrable_smul GJTwo.measurable_cellD] at hf
    rw [GJTwo.Ff_eq, integrable_indicator_iff hU]
    exact hf
  · rw [hmap, integral_map GJTwo.measurable_cellPsi.aemeasurable hs, GJTwo.cellNu,
      integral_withDensity_eq_integral_smul GJTwo.measurable_cellD, GJTwo.Ff_eq,
      integral_indicator hU]
    rfl

theorem integral_fibre {ψ : AddChar F Circle} {G : (Fin 2 → F) × F × F → ℂ}
    (hG : Integrable G (GJTwo.cM ψ)) :
    ∫ p, G p ∂GJTwo.cM ψ =
      ∫ r, ∫ y, ∫ x, G (r, x, y) ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂LFS.vol2 ψ := by
  haveI : SigmaFinite (LFS.vol2 ψ) := by unfold LFS.vol2; infer_instance
  rw [GJTwo.cM] at hG
  rw [GJTwo.cM, integral_prod _ hG]
  refine integral_congr_ae ?_
  filter_upwards [hG.prod_right_ae] with r hr
  exact integral_prod_symm _ hr

theorem Ff_cell {ψ : AddChar F Circle} (A : GL (Fin 2) F → ℂ)
    (P : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F → ℂ)
    (hA : ∀ u z, A (uni2 u * z) = (ψ u : ℂ) * A z)
    (hP : ∀ u z M, P (uni2 u * z) M = P z ((uni2 (-u)).val * M))
    (B : (Matrix (Fin 2) (Fin 2) F → ℂ) → ℂ) (r : Fin 2 → F) (x y : F) (h : ¬ (y = 0 ∨ r 1 = 0)) :
    GJTwo.Ff (fun z => A z * B (P z)) (r, x, y) =
      (A (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r) *
          (((modulus y : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ)) *
        ((ψ x : ℂ) * B (fun M => P (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r)
          ((uni2 (-x)).val * M))) := by
  have hP' : P (uni2 x * (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r)) =
      fun M => P (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r) ((uni2 (-x)).val * M) :=
    funext fun M => hP _ _ M
  simp only [GJTwo.Ff, dif_neg h]
  rw [mul_assoc (uni2 x), hA, hP']
  ring

end D

theorem core : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → (∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = ∫ t, (ψ t : ℂ) * Rpart ψ (fun M => p ((uni2 (-t)).val * M)) ∂selfDualMeasure ψ) → ∀ (A : GL (Fin 2) F → ℂ) (P : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F → ℂ), (∀ u z, A (uni2 u * z) = (ψ u : ℂ) * A z) → (∀ u z M, P (uni2 u * z) M = P z ((uni2 (-u)).val * M)) → (∀ z, SB2 (P z)) → Integrable (fun z => A z * Lpart ψ (P z)) (LFS.hG ψ) → Integrable (fun z => A z * Rpart ψ (P z)) (LFS.hG ψ) → ∫ z, A z * Lpart ψ (P z) ∂LFS.hG ψ = ∫ z, A z * Rpart ψ (P z) ∂LFS.hG ψ := by
  intro F _ _ _ _ _ _ ψ hψ hyp A P hA hP hS h1 h2
  obtain ⟨i1, q1⟩ := integrable_Ff hψ h1
  obtain ⟨i2, q2⟩ := integrable_Ff hψ h2
  rw [q1, q2, integral_fibre i1, integral_fibre i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases h : y = 0 ∨ r 1 = 0
  · simp only [GJTwo.Ff, dif_pos h]
  · simp only [Ff_cell A P hA hP (Lpart ψ) r _ y h, Ff_cell A P hA hP (Rpart ψ) r _ y h]
    rw [integral_const_mul, integral_const_mul, hyp _ (hS _)]

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_right_partial_fourier_integral_eq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → (∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = ∫ t, (ψ t : ℂ) * Rpart ψ (fun M => p ((uni2 (-t)).val * M)) ∂selfDualMeasure ψ) → ∀ (A : GL (Fin 2) F → ℂ) (P : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F → ℂ), (∀ u z, A (uni2 u * z) = (ψ u : ℂ) * A z) → (∀ u z M, P (uni2 u * z) M = P z ((uni2 (-u)).val * M)) → (∀ z, SB2 (P z)) → Integrable (fun z => A z * Lpart ψ (P z)) (LFS.hG ψ) → Integrable (fun z => A z * Rpart ψ (P z)) (LFS.hG ψ) → ∫ z, A z * Lpart ψ (P z) ∂LFS.hG ψ = ∫ z, A z * Rpart ψ (P z) ∂LFS.hG ψ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini.core
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice

theorem fubini3 {F : Type} [MeasurableSpace F] (μ : Measure F) [SFinite μ] (J : F × F × F → ℂ)
    (hJ : Integrable J (μ.prod (μ.prod μ))) :
    ∫ b, ∫ d, ∫ a, J (a, b, d) ∂μ ∂μ ∂μ = ∫ a, ∫ b, ∫ d, J (a, b, d) ∂μ ∂μ ∂μ := by
  have h1 : ∫ a, ∫ b, ∫ d, J (a, b, d) ∂μ ∂μ ∂μ = ∫ a, ∫ t, J (a, t) ∂(μ.prod μ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hJ.prod_right_ae] with a ha
    exact (integral_prod (fun t => J (a, t)) ha).symm
  have h2 : ∫ a, ∫ t, J (a, t) ∂(μ.prod μ) ∂μ = ∫ t, ∫ a, J (a, t) ∂μ ∂(μ.prod μ) :=
    integral_integral_swap (f := fun a t => J (a, t)) hJ
  have h3 : ∫ t, ∫ a, J (a, t) ∂μ ∂(μ.prod μ) = ∫ b, ∫ d, ∫ a, J (a, b, d) ∂μ ∂μ ∂μ :=
    integral_prod (fun t => ∫ a, J (a, t) ∂μ) hJ.integral_prod_right
  rw [h1, h2, h3]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem hcs_comp {X : Type} [TopologicalSpace X] [T2Space X] {p : Matrix (Fin 2) (Fin 2) F → ℂ}
    (hp : HasCompactSupport p) (ι : X → Matrix (Fin 2) (Fin 2) F) (r : Matrix (Fin 2) (Fin 2) F → X)
    (hι : Continuous ι) (hr : Continuous r) (h : Function.LeftInverse r ι) :
    HasCompactSupport (fun x => p (ι x)) :=
  hp.comp_isClosedEmbedding (h.isClosedEmbedding hr hι)

def J (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ) (t : F × F × F) : ℂ :=
  p !![t.1, t.2.1; t.2.2, 1] * (ψ (-(t.2.1 + t.2.2)) : ℂ)

theorem integrable_J {ψ : AddChar F Circle} (hψ : Continuous ψ) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) :
    Integrable (J ψ p) ((selfDualMeasure ψ).prod ((selfDualMeasure ψ).prod (selfDualMeasure ψ))) := by
  have hι : Continuous (fun t : F × F × F => (!![t.1, t.2.1; t.2.2, 1] : Matrix (Fin 2) (Fin 2) F)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hr : Continuous (fun M : Matrix (Fin 2) (Fin 2) F => ((M 0 0, M 0 1, M 1 0) : F × F × F)) := by
    fun_prop
  have hc : HasCompactSupport (fun t : F × F × F => p !![t.1, t.2.1; t.2.2, 1]) :=
    hcs_comp hp.2 _ _ hι hr (fun t => by simp)
  have hcont : Continuous (J ψ p) := by
    unfold J
    refine (hp.1.continuous.comp hι).mul ?_
    exact continuous_subtype_val.comp (hψ.comp (by fun_prop))
  exact hcont.integrable_of_hasCompactSupport (hc.mul_right)

theorem mul_Lpart {ψ : AddChar F Circle} (hψ : Continuous ψ) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) (u : F) :
    (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) =
      ∫ d, ∫ a, J ψ p (a, -u, d) ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
  set μ := selfDualMeasure ψ with hμ
  have hι : Continuous (fun y : F × F => (!![y.1 - u * y.2, -u; y.2, 1] : Matrix (Fin 2) (Fin 2) F)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hr : Continuous (fun M : Matrix (Fin 2) (Fin 2) F => ((M 0 0 + u * M 1 0, M 1 0) : F × F)) := by
    fun_prop
  have hc : HasCompactSupport (fun y : F × F => p !![y.1 - u * y.2, -u; y.2, 1]) :=
    hcs_comp hp.2 _ _ hι hr (fun t => by simp)
  set h : F × F → ℂ := fun y => p !![y.1 - u * y.2, -u; y.2, 1] * (ψ (-y.2) : ℂ) with hh
  have hint : Integrable h (μ.prod μ) := by
    have hcont : Continuous h := by
      refine (hp.1.continuous.comp hι).mul ?_
      exact continuous_subtype_val.comp (hψ.comp (by fun_prop))
    exact hcont.integrable_of_hasCompactSupport hc.mul_right
  have hL : Lpart ψ (fun M => p ((uni2 (-u)).val * M)) = ∫ y, h y ∂(μ.prod μ) := by
    unfold Lpart LFS.vol2
    rw [← ((measurePreserving_finTwoArrow μ).symm MeasurableEquiv.finTwoArrow).integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e0 : (MeasurableEquiv.finTwoArrow.symm y : Fin 2 → F) 0 = y.1 := rfl
    have e1 : (MeasurableEquiv.finTwoArrow.symm y : Fin 2 → F) 1 = y.2 := rfl
    have hm : (uni2 (-u)).val * col2 (MeasurableEquiv.finTwoArrow.symm y) = !![y.1 - u * y.2, -u; y.2, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uni2, col2, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    simp only [hh, hm, e1]
  rw [hL, integral_prod_symm h hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
  have hs : ∫ x, h (x, d) ∂μ = ∫ a, p !![a, -u; d, 1] * (ψ (-d) : ℂ) ∂μ :=
    integral_sub_right_eq_self (fun a => p !![a, -u; d, 1] * (ψ (-d) : ℂ)) (u * d)
  simp only []
  rw [hs, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hψm : (ψ (-(-u + d)) : ℂ) = (ψ u : ℂ) * (ψ (-d) : ℂ) := by
    rw [show -(-u + d) = u + -d by ring, AddChar.map_add_eq_mul]; simp
  simp only [J, hψm]
  ring

theorem sliceForm : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ →
    ∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p →
      ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = rr ψ p 1 := by
  intro F _ _ _ _ _ _ ψ hψ p hp
  have h1 : ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ =
      ∫ u, (fun b => ∫ d, ∫ a, J ψ p (a, b, d) ∂selfDualMeasure ψ ∂selfDualMeasure ψ) (-u) ∂selfDualMeasure ψ :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => mul_Lpart hψ.1 hp u)
  have h2 := integral_neg_eq_self (fun b => ∫ d, ∫ a, J ψ p (a, b, d) ∂selfDualMeasure ψ ∂selfDualMeasure ψ)
    (selfDualMeasure ψ)
  rw [h1, h2, fubini3 _ _ (integrable_J hψ.1 hp)]
  rfl

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_partial_fourier_twisted_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = rr ψ p 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice.sliceForm
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.FlR

section Iter

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]

theorem int4 (f : X × X × X × X → ℂ) (hf : Integrable f (μ.prod (μ.prod (μ.prod μ)))) :
    ∫ q, f q ∂(μ.prod (μ.prod (μ.prod μ))) = ∫ x, ∫ y, ∫ z, ∫ w, f (x, y, z, w) ∂μ ∂μ ∂μ ∂μ := by
  rw [integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with x hx
  rw [integral_prod _ hx]
  refine integral_congr_ae ?_
  filter_upwards [hx.prod_right_ae] with y hy
  exact integral_prod _ hy

end Iter

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ent (a b d c : F) : Fin 2 × Fin 2 → F :=
  fun ij => (!![a, b; d, c] : Matrix (Fin 2) (Fin 2) F) ij.1 ij.2

@[simp] theorem ent_00 (a b d c : F) : ent a b d c (0, 0) = a := by simp [ent]
@[simp] theorem ent_01 (a b d c : F) : ent a b d c (0, 1) = b := by simp [ent]
@[simp] theorem ent_10 (a b d c : F) : ent a b d c (1, 0) = d := by simp [ent]
@[simp] theorem ent_11 (a b d c : F) : ent a b d c (1, 1) = c := by simp [ent]

theorem toM_ent (a b d c : F) : toM (ent a b d c) = !![a, b; d, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM]

theorem ent_eta (X : Fin 2 × Fin 2 → F) : ent (X (0, 0)) (X (0, 1)) (X (1, 0)) (X (1, 1)) = X := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp

theorem measurable_ent : Measurable fun q : F × F × F × F => ent q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  refine measurable_pi_iff.mpr fun ij => ?_
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, ent_00, ent_01, ent_10, ent_11] <;> fun_prop

def eqA : (F × F × F × F) ≃ᵐ (Fin 2 × Fin 2 → F) where
  toFun q := ent q.2.1 q.2.2.1 q.2.2.2 q.1
  invFun X := (X (1, 1), X (0, 0), X (0, 1), X (1, 0))
  left_inv q := by simp
  right_inv X := ent_eta X
  measurable_toFun := measurable_ent.comp
    (f := fun q : F × F × F × F => (q.2.1, q.2.2.1, q.2.2.2, q.1)) (by fun_prop)
  measurable_invFun := by
    change Measurable fun X : Fin 2 × Fin 2 → F => (X (1, 1), X (0, 0), X (0, 1), X (1, 0))
    fun_prop

def eqB : (F × F × F × F) ≃ᵐ (Fin 2 × Fin 2 → F) where
  toFun q := ent q.2.2.2 q.2.2.1 q.2.1 q.1
  invFun X := (X (1, 1), X (1, 0), X (0, 1), X (0, 0))
  left_inv q := by simp
  right_inv X := ent_eta X
  measurable_toFun := measurable_ent.comp
    (f := fun q : F × F × F × F => (q.2.2.2, q.2.2.1, q.2.1, q.1)) (by fun_prop)
  measurable_invFun := by
    change Measurable fun X : Fin 2 × Fin 2 → F => (X (1, 1), X (1, 0), X (0, 1), X (0, 0))
    fun_prop

theorem mpA (ψ : AddChar F Circle) : MeasurePreserving (eqA (F := F))
    (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ)))) (mM ψ) := by
  refine ⟨eqA.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [eqA.map_apply]
  have : (eqA (F := F)) ⁻¹' Set.univ.pi s = s (1, 1) ×ˢ s (0, 0) ×ˢ s (0, 1) ×ˢ s (1, 0) := by
    ext ⟨c, a, b, d⟩
    simp [eqA, Set.mem_pi, Prod.forall, Fin.forall_fin_two]
    tauto
  rw [this]
  simp only [Measure.prod_prod]
  rw [Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  ring

theorem mpB (ψ : AddChar F Circle) : MeasurePreserving (eqB (F := F))
    (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ)))) (mM ψ) := by
  refine ⟨eqB.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [eqB.map_apply]
  have : (eqB (F := F)) ⁻¹' Set.univ.pi s = s (1, 1) ×ˢ s (1, 0) ×ˢ s (0, 1) ×ˢ s (0, 0) := by
    ext ⟨c, d, b, a⟩
    simp [eqB, Set.mem_pi, Prod.forall, Fin.forall_fin_two]
    tauto
  rw [this]
  simp only [Measure.prod_prod]
  rw [Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  ring

theorem iterA (ψ : AddChar F Circle) (g : (Fin 2 × Fin 2 → F) → ℂ) (hg : Integrable g (mM ψ)) :
    ∫ X, g X ∂mM ψ = ∫ c, ∫ a, ∫ b, ∫ d, g (ent a b d c)
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
  rw [← (mpA ψ).integral_comp' g]
  exact int4 _ _ (((mpA ψ).integrable_comp_emb eqA.measurableEmbedding).mpr hg)

theorem iterB (ψ : AddChar F Circle) (g : (Fin 2 × Fin 2 → F) → ℂ) (hg : Integrable g (mM ψ)) :
    ∫ X, g X ∂mM ψ = ∫ c, ∫ d, ∫ b, ∫ a, g (ent a b d c)
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
  rw [← (mpB ψ).integral_comp' g]
  exact int4 _ _ (((mpB ψ).integrable_comp_emb eqB.measurableEmbedding).mpr hg)

def toMH : (Fin 2 × Fin 2 → F) ≃ₜ Matrix (Fin 2) (Fin 2) F where
  toFun := toM
  invFun M := fun ij => M ij.1 ij.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_matrix fun i j => continuous_apply (i, j)
  continuous_invFun := continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

def nH (t : F) : Matrix (Fin 2) (Fin 2) F ≃ₜ Matrix (Fin 2) (Fin 2) F where
  toFun M := (uni2 (-t)).val * M
  invFun M := ((uni2 (-t))⁻¹ : GL (Fin 2) F).val * M
  left_inv M := Units.inv_mul_cancel_left _ M
  right_inv M := Units.mul_inv_cancel_left _ M
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

theorem schwartz_bruhat_unipotent_shift {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) (t : F) :
    SB2 fun M => p ((uni2 (-t)).val * M) :=
  ⟨hp.1.comp_continuous (nH t).continuous, hp.2.comp_homeomorph (nH t)⟩

theorem integrable_sb (ψ : AddChar F Circle) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p)
    {χ : (Fin 2 × Fin 2 → F) → ℂ} (hχ : Continuous χ) :
    Integrable (fun X => p (toM X) * χ X) (mM ψ) := by
  have hc : Continuous fun X : Fin 2 × Fin 2 → F => p (toM X) :=
    hp.1.continuous.comp (toMH (F := F)).continuous
  have hs : HasCompactSupport fun X : Fin 2 × Fin 2 → F => p (toM X) :=
    hp.2.comp_homeomorph (toMH (F := F))
  haveI : IsFiniteMeasureOnCompacts (mM ψ) := by
    unfold mM
    infer_instance
  exact (hc.mul hχ).integrable_of_hasCompactSupport hs.mul_right

theorem rr_mem (ψ : AddChar F Circle) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) :
    rr ψ p ∈ schwartzBruhat F := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun c₀ => ?_, ?_⟩
  · have hinv := GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant
      (X := Matrix (Fin 2) (Fin 2) F) (f := p) ⟨hp.1, hp.2⟩
    have hcont : Continuous fun c : F => (!![0, 0; 0, c - c₀] : Matrix (Fin 2) (Fin 2) F) := by
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    have h2 : Filter.Tendsto (fun c : F => (!![0, 0; 0, c - c₀] : Matrix (Fin 2) (Fin 2) F))
        (𝓝 c₀) (𝓝 0) := by
      have h0 : (!![0, 0; 0, c₀ - c₀] : Matrix (Fin 2) (Fin 2) F) = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      simpa only [h0] using hcont.tendsto c₀
    filter_upwards [h2.eventually hinv] with c hc
    have key : ∀ a b d, p !![a, b; d, c] = p !![a, b; d, c₀] := fun a b d => by
      rw [← hc !![a, b; d, c₀]]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simp only [rr, key]
  · refine HasCompactSupport.intro (K := (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) '' tsupport p)
      (hp.2.image (by fun_prop)) fun c hc => ?_
    have h0 : ∀ a b d, p !![a, b; d, c] = 0 := fun a b d =>
      image_eq_zero_of_notMem_tsupport fun h => hc ⟨_, h, by simp⟩
    simp [rr, h0]

theorem uni2_mul_uni2_eq_uni2_add (t a b d c : F) :
    (uni2 (-t)).val * !![a, b; d, c] = !![a - t * d, b - t * c; d, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Rpart_shift (ψ : AddChar F Circle) (hψ : Continuous ψ) {p : Matrix (Fin 2) (Fin 2) F → ℂ}
    (hp : SB2 p) (t : F) :
    Rpart ψ (fun M => p ((uni2 (-t)).val * M)) =
      localFourier (selfDualMeasure ψ) ψ (rr ψ p) (-t) := by
  have hψc : Continuous fun x : F => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hχ₀ : Continuous fun X : Fin 2 × Fin 2 → F => (ψ (-(X (0, 1) + X (1, 0))) : ℂ) :=
    hψc.comp (by fun_prop)
  have hχ₁ : Continuous fun X : Fin 2 × Fin 2 → F => (ψ (X (1, 1) * -t) : ℂ) :=
    hψc.comp (by fun_prop)
  have h₀ := integrable_sb ψ (schwartz_bruhat_unipotent_shift hp t) hχ₀
  have hχ₂ : Continuous fun X : Fin 2 × Fin 2 → F =>
      (ψ (-(X (0, 1) + X (1, 0))) : ℂ) * (ψ (X (1, 1) * -t) : ℂ) := hχ₀.mul hχ₁
  have h₁ := integrable_sb ψ hp hχ₂
  have e₀ : Rpart ψ (fun M => p ((uni2 (-t)).val * M)) =
      ∫ X, p (toM X) * ((ψ (-(X (0, 1) + X (1, 0))) : ℂ) * (ψ (X (1, 1) * -t) : ℂ)) ∂mM ψ := by
    rw [Rpart, iterB ψ _ h₀, iterB ψ _ h₁]
    refine integral_congr_ae (.of_forall fun c => ?_)
    refine integral_congr_ae (.of_forall fun d => ?_)
    simp only [ent_01, ent_10, ent_11, toM_ent, uni2_mul_uni2_eq_uni2_add]
    have s₁ : ∀ b, ∫ a, p !![a - t * d, b - t * c; d, c] * (ψ (-(b + d)) : ℂ) ∂selfDualMeasure ψ =
        ∫ a, p !![a, b - t * c; d, c] * (ψ (-(b + d)) : ℂ) ∂selfDualMeasure ψ := fun b =>
      integral_sub_right_eq_self (fun a => p !![a, b - t * c; d, c] * (ψ (-(b + d)) : ℂ)) (t * d)
    simp only [s₁]
    rw [← integral_sub_right_eq_self (μ := selfDualMeasure ψ)
      (fun b => ∫ a, p !![a, b; d, c] * ((ψ (-(b + d)) : ℂ) * (ψ (c * -t) : ℂ)) ∂selfDualMeasure ψ) (t * c)]
    refine integral_congr_ae (.of_forall fun b => ?_)
    refine integral_congr_ae (.of_forall fun a => ?_)
    have hk : (ψ (-(b + d)) : ℂ) = (ψ (-(b - t * c + d)) : ℂ) * (ψ (c * -t) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    dsimp only
    rw [hk]
  rw [e₀, iterA ψ _ h₁]
  simp only [ent_01, ent_10, ent_11, toM_ent, localFourier, rr, ← integral_mul_const, mul_assoc]

end D

theorem integral_Rpart_shift : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ t, (ψ t : ℂ) * Rpart ψ (fun M => p ((uni2 (-t)).val * M)) ∂selfDualMeasure ψ = rr ψ p 1 := by
  intro F _ _ _ _ _ _ ψ hs p hp
  obtain ⟨hc, h1, -⟩ := hs
  have hinv := localFourier_localFourier_selfDual hc h1 (rr_mem ψ hp) (-1)
  rw [neg_neg] at hinv
  rw [← hinv]
  simp only [Rpart_shift ψ hc hp]
  have := integral_neg_eq_self (fun t => localFourier (selfDualMeasure ψ) ψ (rr ψ p) t * (ψ (t * -1) : ℂ)) (selfDualMeasure ψ)
  rw [show localFourier (selfDualMeasure ψ) ψ (localFourier (selfDualMeasure ψ) ψ (rr ψ p)) (-1) =
    ∫ t, localFourier (selfDualMeasure ψ) ψ (rr ψ p) t * (ψ (t * -1) : ℂ) ∂selfDualMeasure ψ from rfl, ← this]
  refine integral_congr_ae (.of_forall fun t => ?_)
  simp [mul_comm]

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.FlR
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_partial_fourier_twisted_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ t, (ψ t : ℂ) * Rpart ψ (fun M => p ((uni2 (-t)).val * M)) ∂selfDualMeasure ψ = rr ψ p 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.FlR.integral_Rpart_shift
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_block_concatenation (A B : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    Continuous fun M : Matrix (Fin 2) (Fin 2) F => cat3 (A * M * B) v := by
  have h : Continuous fun M : Matrix (Fin 2) (Fin 2) F => A * M * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine continuous_matrix fun i j => ?_
  have he : ∀ a b, Continuous fun M : Matrix (Fin 2) (Fin 2) F => (A * M * B) a b :=
    fun a b => h.matrix_elem a b
  fin_cases i <;> fin_cases j <;> simp [cat3] <;> first | exact he _ _ | exact continuous_const

def firstCols (X : Matrix (Fin 2) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => X i j.castSucc

theorem continuous_firstCols : Continuous (firstCols (F := F)) :=
  continuous_matrix fun i j => continuous_id.matrix_elem i j.castSucc

theorem first_columns_concatenation (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    firstCols (cat3 A v) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [firstCols, cat3]

end D

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair

theorem GlobalTheory.CompanionTheory.GL2DualWhittakerPair.pullback_schwartz_bruhat_M2 : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), Φ ∈ LFS.SB F → ∀ h z : GL (Fin 2) F, SB2 (Pf Φ h z) := by
  intro F _ _ _ _ _ _ Φ hΦ h z
  obtain ⟨hl, hc⟩ := hΦ
  set A : GL (Fin 2) F := z⁻¹ with hA
  set B : GL (Fin 2) F := tinv h with hB
  set v : Fin 2 → F := A.val *ᵥ e1 with hv
  have hι : Continuous fun M : Matrix (Fin 2) (Fin 2) F => cat3 (A.val * M * B.val) v :=
    continuous_block_concatenation _ _ _
  refine ⟨hl.comp_continuous hι, ?_⟩
  let q : Matrix (Fin 2) (Fin 3) F → Matrix (Fin 2) (Fin 2) F :=
    fun X => (A⁻¹).val * firstCols X * (B⁻¹).val
  have hq : Continuous q :=
    (continuous_const.matrix_mul continuous_firstCols).matrix_mul continuous_const
  refine HasCompactSupport.of_support_subset_isCompact (hc.isCompact.image hq) ?_
  intro M hM
  refine ⟨cat3 (A.val * M * B.val) v, subset_tsupport _ hM, ?_⟩
  have h1 : (A⁻¹).val * A.val = 1 := by rw [← Units.val_mul]; simp
  have h2 : B.val * (B⁻¹).val = 1 := by rw [← Units.val_mul]; simp
  simp only [q, first_columns_concatenation]
  calc (A⁻¹).val * (A.val * M * B.val) * (B⁻¹).val
      = ((A⁻¹).val * A.val) * M * (B.val * (B⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [h1, h2]; simp
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_schwartz_bruhat_matrix : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), Φ ∈ LFS.SB F → ∀ h z : GL (Fin 2) F, SB2 (Pf Φ h z) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.pullback_schwartz_bruhat_M2
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont

theorem mul_concat_column {F : Type} [Field F] (u A : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) :
    u * cat3 A y = cat3 (u * A) (u *ᵥ y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cat3, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem continuous_Rpart_Pf : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F,
      Continuous fun z : GL (Fin 2) F => Rpart ψ (Pf Φ h z) := by
  intro F _ _ _ _ _ _ ψ _ Φ hΦ h
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.LFHolP.exists_left_invariant hΦ.1 hΦ.2
  have hP : ∀ g u : GL (Fin 2) F, u ∈ U → Pf Φ h (g * u) = Pf Φ h g := by
    intro g u hu
    funext M
    have hu' : u⁻¹ ∈ U := inv_mem hu
    have h1 := hU _ hu' (cat3 ((g⁻¹ : GL (Fin 2) F).val * M * (tinv h).val)
      ((g⁻¹ : GL (Fin 2) F).val *ᵥ e1))
    rw [mul_concat_column] at h1
    simp only [Pf, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec] at h1 ⊢
    exact h1
  have hl : IsLocallyConstant fun z : GL (Fin 2) F => Rpart ψ (Pf Φ h z) :=
    GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant _ U.toSubgroup U.isOpen
      fun g u hu => by simp only [hP g u hu]
  exact hl.continuous

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_right_partial_fourier : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F, Continuous fun z : GL (Fin 2) F => Rpart ψ (Pf Φ h z) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont.continuous_Rpart_Pf
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isCompact_bounded (R M : ℝ) :
    IsCompact {g : GL (Fin 2) F | (∀ i j, (modulus (g.val i j) : ℝ) ≤ R) ∧
      ∀ i j, (modulus ((g⁻¹ : GL (Fin 2) F).val i j) : ℝ) ≤ M} := by
  haveI : T2Space F := inferInstance
  have hM : ∀ S : ℝ, IsCompact {A : Matrix (Fin 2) (Fin 2) F | ∀ i j, (modulus (A i j) : ℝ) ≤ S} := by
    intro S
    have hO : IsCompact {x : F | (modulus x : ℝ) ≤ S} := GlobalTheory.CompanionTheory.LFDual.ZRho.isCompact_modulus_le S
    have h := isCompact_univ_pi fun _ : Fin 2 => isCompact_univ_pi fun _ : Fin 2 => hO
    have e : {A : Matrix (Fin 2) (Fin 2) F | ∀ i j, (modulus (A i j) : ℝ) ≤ S} =
        Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => {x : F | (modulus x : ℝ) ≤ S} :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 2) (Fin 2) F)).isCompact_preimage
    ((hM R).prod ((hM M).image MulOpposite.continuous_op))
  convert h using 1
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

theorem modulus_entry_mul_le {κ k : Matrix (Fin 2) (Fin 2) F} (hκ : ∀ i j, κ i j ∈ 𝒪[F]) {B : ℝ}
    (hk : ∀ i j, (modulus (k i j) : ℝ) ≤ B) (i l : Fin 2) : (modulus ((k * κ) i l) : ℝ) ≤ B := by
  have term : ∀ j, (modulus (k i j * κ j l) : ℝ) ≤ B := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus (k i j) : ℝ) * modulus (κ j l) ≤ modulus (k i j) * 1 :=
          mul_le_mul_of_nonneg_left (GlobalTheory.CompanionTheory.LFCoords.modulus_le_one_real (hκ j l)) (NNReal.coe_nonneg _)
      _ ≤ B := by simpa using hk i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact (GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max _ _).trans (max_le (term 0) (term 1))

theorem exists_one_le_modulus_inv {κ : GL (Fin 2) F} (hκ : κ ∈ GLnLocal.integralGL F 2) :
    ∃ i, 1 ≤ (modulus ((κ⁻¹ : GL (Fin 2) F).val i 0) : ℝ) := by
  have hint := ((GLnLocal.mem_integralGL_iff F 2).1 hκ).1
  have e : κ.val * (κ⁻¹ : GL (Fin 2) F).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e00 := congrFun (congrFun e 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00
  by_contra hcon
  push_neg at hcon
  have term : ∀ j, (modulus (κ.val 0 j * (κ⁻¹ : GL (Fin 2) F).val j 0) : ℝ) < 1 := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus (κ.val 0 j) : ℝ) * modulus ((κ⁻¹ : GL (Fin 2) F).val j 0)
        ≤ 1 * modulus ((κ⁻¹ : GL (Fin 2) F).val j 0) :=
          mul_le_mul_of_nonneg_right (GlobalTheory.CompanionTheory.LFCoords.modulus_le_one_real (hint 0 j)) (NNReal.coe_nonneg _)
      _ < 1 := by simpa using hcon j
  have h1 := GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max (κ.val 0 0 * (κ⁻¹ : GL (Fin 2) F).val 0 0)
    (κ.val 0 1 * (κ⁻¹ : GL (Fin 2) F).val 1 0)
  rw [e00] at h1
  have h2 := max_lt (term 0) (term 1)
  have h3 : (modulus (1 : F) : ℝ) = 1 := by simp
  linarith

theorem inv_val (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) :
    ((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val =
      (κ⁻¹ : GL (Fin 2) F).val * !![((a⁻¹ : Fˣ) : F), -(x * ((a⁻¹ : Fˣ) : F)); 0, ((b⁻¹ : Fˣ) : F)] := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  congr 1
  have e1' : ((dg2 a b)⁻¹ : GL (Fin 2) F).val = !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)] := rfl
  have e2' : ((uni2 x)⁻¹ : GL (Fin 2) F).val = !![1, -x; 0, 1] := rfl
  rw [e1', e2']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem inv_entries_le (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) (hκ : κ ∈ GLnLocal.integralGL F 2)
    (R B : ℝ) (hab : (modulus ((a * b⁻¹ : Fˣ) : F) : ℝ) ≤ B)
    (h1 : ∀ i j, (modulus ((uni2 x * dg2 a b * κ).val i j) : ℝ) ≤ R)
    (h2 : ∀ i, (modulus ((((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) (i j : Fin 2) :
    (modulus (((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val i j) : ℝ) ≤
      max (max R (B * R)) (R * (B * R) * R) := by
  obtain ⟨hint, hint'⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
  have ha : (modulus ((a⁻¹ : Fˣ) : F) : ℝ) ≤ R := by
    obtain ⟨i, hi⟩ := exists_one_le_modulus_inv hκ
    have h := h2 i
    have e : (((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val *ᵥ e1) i =
        (κ⁻¹ : GL (Fin 2) F).val i 0 * ((a⁻¹ : Fˣ) : F) := by
      rw [inv_val]
      simp [Matrix.mulVec, dotProduct, e1, Fin.sum_univ_two, Matrix.mul_apply]
    rw [e, modulus_mul, NNReal.coe_mul] at h
    calc (modulus ((a⁻¹ : Fˣ) : F) : ℝ) = 1 * modulus ((a⁻¹ : Fˣ) : F) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hi (NNReal.coe_nonneg _)
      _ ≤ R := h
  have hT : ∀ i j, (modulus ((uni2 x * dg2 a b).val i j) : ℝ) ≤ R := by
    have e : (uni2 x * dg2 a b).val = (uni2 x * dg2 a b * κ).val * (κ⁻¹ : GL (Fin 2) F).val := by
      rw [← Units.val_mul]
      simp
    rw [e]
    exact modulus_entry_mul_le hint' h1
  have hxb : (modulus (x * (b : F)) : ℝ) ≤ R := by
    have := hT 0 1
    simpa [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two] using this
  have pa : (0 : ℝ) < modulus ((a⁻¹ : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have pb : (0 : ℝ) < modulus ((b⁻¹ : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have pa' : (0 : ℝ) < modulus ((a : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have pab : (0 : ℝ) < modulus ((a * b⁻¹ : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have hB0 : 0 < B := pab.trans_le hab
  have hR0 : 0 < R := pa.trans_le ha
  have hbinv : (modulus ((b⁻¹ : Fˣ) : F) : ℝ) ≤ B * R := by
    have e : (modulus ((b⁻¹ : Fˣ) : F) : ℝ) =
        (modulus ((a * b⁻¹ : Fˣ) : F) : ℝ) * modulus ((a⁻¹ : Fˣ) : F) := by
      rw [← NNReal.coe_mul, ← modulus_mul, ← Units.val_mul]
      congr 3
      simp [mul_comm]
    rw [e]
    exact mul_le_mul hab ha pa.le hB0.le
  have hxa : (modulus (-(x * ((a⁻¹ : Fˣ) : F))) : ℝ) ≤ R * (B * R) * R := by
    have e : x * ((a⁻¹ : Fˣ) : F) = x * (b : F) * ((b⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) := by simp
    rw [GlobalTheory.CompanionTheory.LFCoords.modulus_neg_self, e, modulus_mul, modulus_mul, NNReal.coe_mul, NNReal.coe_mul]
    exact mul_le_mul (mul_le_mul hxb hbinv pb.le hR0.le) ha pa.le (by positivity)
  have hM0 : 0 ≤ max (max R (B * R)) (R * (B * R) * R) :=
    hR0.le.trans ((le_max_left _ _).trans (le_max_left _ _))
  rw [inv_val]
  refine GlobalTheory.CompanionTheory.LFCoords.modulus_mul_entry_le hint' (fun i j => ?_) i j
  fin_cases i <;> fin_cases j
  · exact ha.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact hxa.trans (le_max_right _ _)
  · simpa using hM0
  · exact hbinv.trans ((le_max_right _ _).trans (le_max_left _ _))

theorem ratio_bound {ψ : AddChar F Circle} {ν : Fˣ →* ℂˣ} [MeasurableSpace F] [BorelSpace F]
    {V' : Submodule ℂ (GL (Fin 2) F → ℂ)} (H : WhittakerModelGL2 ψ ν ν⁻¹ V') {W₀ : GL (Fin 2) F → ℂ} (hW : W₀ ∈ V')
    {B C₀ : ℝ} (hB : ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
      ‖W₀ (dg2 a 1 * k)‖ ≤ C₀ * (modulus (a : F) : ℝ) ^ ((1 : ℝ) / 2 - 1) ∧
        (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B))
    (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) (hκ : κ ∈ GLnLocal.integralGL F 2)
    (hz : W₀ (uni2 x * dg2 a b * κ) ≠ 0) : (modulus ((a * b⁻¹ : Fˣ) : F) : ℝ) ≤ B := by
  have hb0 : (b : F) ≠ 0 := b.ne_zero
  have e0 : dg2 a b = dg2 b b * dg2 (a * b⁻¹) 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  have e : uni2 x * dg2 a b * κ = uni2 x * (dg2 b b * (dg2 (a * b⁻¹) 1 * κ)) := by
    rw [e0]
    simp only [mul_assoc]
  rw [e, H.psi W₀ hW, H.cen W₀ hW] at hz
  exact (hB _ κ hκ).2 fun h => hz (by rw [h]; simp)

theorem support_compact : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)), WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W₀ ∈ V', ∀ R : ℝ, ∃ C : Set (GL (Fin 2) F), IsCompact C ∧ ∀ z : GL (Fin 2) F, W₀ z ≠ 0 → (∀ i j, (modulus (z.val i j) : ℝ) ≤ R) → (∀ i, (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) → z ∈ C := by
  intro F _ _ _ _ _ _ ψ _ ν V' H W₀ hW R
  obtain ⟨C₀, B, hB⟩ := H.bound W₀ hW 1 one_pos
  refine ⟨_, isCompact_bounded R (max (max R (B * R)) (R * (B * R) * R)), fun z hz h1 h2 => ⟨h1, ?_⟩⟩
  obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two F z
  exact inv_entries_le x _ _ κ hκ R B (ratio_bound H hW hB x _ _ κ hκ hz) h1 h2

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_support_compact_bounded_entries : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)), WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W₀ ∈ V', ∀ R : ℝ, ∃ C : Set (GL (Fin 2) F), IsCompact C ∧ ∀ z : GL (Fin 2) F, W₀ z ≠ 0 → (∀ i j, (modulus (z.val i j) : ℝ) ≤ R) → (∀ i, (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) → z ∈ C := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt.support_compact
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.InnerIntegralLongWeyl

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem em_inv_eq (h : GL (Fin 2) F) : (em h)⁻¹ = em h⁻¹ := by
  refine (eq_comm.1 (eq_inv_of_mul_eq_one_right ?_))
  apply Units.ext
  have hk : h.val * (h⁻¹ : GL (Fin 2) F).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val, Units.val_one]
  generalize (h⁻¹ : GL (Fin 2) F).val = K at hk ⊢
  generalize h.val = H at hk ⊢
  have e00 : H 0 0 * K 0 0 + H 0 1 * K 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 0) 0
  have e01 : H 0 0 * K 0 1 + H 0 1 * K 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 0) 1
  have e10 : H 1 0 * K 0 0 + H 1 1 * K 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 1) 0
  have e11 : H 1 0 * K 0 1 + H 1 1 * K 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 1) 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

theorem block_long_weyl3_diag_concatenation (x : Fin 2 → F) (h : GL (Fin 2) F) :
    LFS.blk x * (w3 * tinv (em h) : GL (Fin 3) F).val = cat3 (col2 x * (tinv h).val) e1 := by
  have ht : (tinv (em h)).val = ((em h⁻¹).val)ᵀ := by
    change (((em h)⁻¹ : GL (Fin 3) F).val)ᵀ = _
    rw [em_inv_eq]
  have ht2 : (tinv h).val = ((h⁻¹ : GL (Fin 2) F).val)ᵀ := rfl
  rw [Units.val_mul, ht, ht2, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
  generalize (h⁻¹ : GL (Fin 2) F).val = K
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LFS.blk, w3, cat3, col2, e1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

theorem inner_integral_long_weyl_transpose_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (y h : GL (Fin 2) F), LFS.inn ψ Φ y⁻¹ (w3 * tinv (em h)) = Lpart ψ (Pf Φ h y) := by
  intro F _ _ _ _ _ _ ψ Φ y h
  unfold LFS.inn Lpart Pf
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Matrix.mul_assoc, block_long_weyl3_diag_concatenation, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mul_concat_column, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.InnerIntegralLongWeyl
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_integral_eq_left_partial_fourier : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (y h : GL (Fin 2) F), LFS.inn ψ Φ y⁻¹ (w3 * tinv (em h)) = Lpart ψ (Pf Φ h y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InnerIntegralLongWeyl.inner_integral_long_weyl_transpose_inv
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DeterminantLongWeyl

open scoped NNReal

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem det_long_weyl3 : ((GeneralLinearGroup.det (w3 : GL (Fin 3) F) : Fˣ) : F) = -1 := by
  simp only [GeneralLinearGroup.val_det_apply, w3]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_tinv {n : Type} [Fintype n] [DecidableEq n] (g : GL n F) :
    GeneralLinearGroup.det (tinv g) = (GeneralLinearGroup.det g)⁻¹ := by
  ext
  simp [tinv, GeneralLinearGroup.val_det_apply, Matrix.det_transpose]

theorem modulus_neg_one : modulus (-1 : F) = 1 := by
  have h : modulus (-1 : F) ^ 2 = 1 := by
    rw [sq, ← modulus_mul]
    simp [modulus_one]
  exact (pow_eq_one_iff_of_nonneg (by positivity) (by norm_num)).1 h

theorem mp_inv (a : Fˣ) (s : ℂ) : mp a⁻¹ s = mp a (-s) := by
  have h1 : mp a⁻¹ s * mp a s = 1 := by
    rw [← GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_mul, inv_mul_cancel]
    simp [mp, modulus_one]
  have h2 : mp a (-s) * mp a s = 1 := by
    rw [← GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_add, neg_add_cancel]
    simp [mp]
  have h3 : mp a s ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)

end D

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (h : GL (Fin 2) F),
    mp (GeneralLinearGroup.det (w3 * tinv (em h))) 1 = mp (GeneralLinearGroup.det h) (-1) := by
  intro F _ _ _ _ _ _ h
  have hw : mp (GeneralLinearGroup.det (w3 : GL (Fin 3) F)) 1 = 1 := by
    rw [GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_one, det_long_weyl3, modulus_neg_one]
    simp
  rw [map_mul, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_mul, hw, one_mul, det_tinv, mp_inv, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_det_em]

end GlobalTheory.CompanionTheory.DeterminantLongWeyl
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_det_long_weyl_block : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (h : GL (Fin 2) F), mp (GeneralLinearGroup.det (w3 * tinv (em h))) 1 = mp (GeneralLinearGroup.det h) (-1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DeterminantLongWeyl.main
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2LocalData

theorem tinv_mul' {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] (h g : GL n F) :
    tinv (h * g) = tinv h * tinv g := by
  apply Units.ext
  change ((h * g)⁻¹ : GL n F).valᵀ = (h⁻¹ : GL n F).valᵀ * (g⁻¹ : GL n F).valᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

end GlobalTheory.CompanionTheory.GL2LocalData
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem weyl_mul_weyl : (w2 : GL (Fin 2) F) * w2 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2, Matrix.mul_apply, Fin.sum_univ_two]

theorem tinv_one' : tinv (1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  simp [tinv]

theorem transposeInv_weyl : tinv (w2 : GL (Fin 2) F) = w2 := by
  have hi : (w2 : GL (Fin 2) F)⁻¹ = w2 := inv_eq_of_mul_eq_one_left weyl_mul_weyl
  apply Units.ext
  change ((w2 : GL (Fin 2) F)⁻¹).valᵀ = (w2 : GL (Fin 2) F).val
  rw [hi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2]

theorem tinv_tinv (z : GL (Fin 2) F) : tinv (tinv z) = z := by
  apply Units.ext
  change (z.valᵀ)ᵀ = z.val
  simp

theorem h_mul_inv (h z : GL (Fin 2) F) :
    h * (tinv z⁻¹ * w2 * h)⁻¹ = w2 * tinv z := by
  have h1 : tinv z⁻¹ * tinv z = 1 := by
    rw [← GlobalTheory.CompanionTheory.GL2LocalData.tinv_mul', inv_mul_cancel, tinv_one']
  have hi : (tinv z⁻¹)⁻¹ = tinv z := inv_eq_of_mul_eq_one_right h1
  have hw : (w2 : GL (Fin 2) F)⁻¹ = w2 := inv_eq_of_mul_eq_one_left weyl_mul_weyl
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hi, hw]
  group

theorem second_vector_long_weyl_transpose_inv (z : GL (Fin 2) F) :
    e2r (w2 * tinv z) = (z⁻¹ : GL (Fin 2) F).val *ᵥ e1 := by
  have hv : (w2 * tinv z).val = (w2 : GL (Fin 2) F).val * (z⁻¹ : GL (Fin 2) F).valᵀ := rfl
  unfold e2r
  rw [hv]
  generalize (z⁻¹ : GL (Fin 2) F).val = m
  ext j
  fin_cases j <;>
    simp [e1, w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]

theorem dual_whittaker_long_weyl_transpose_inv (W₀ : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) :
    dW2 W₀ (w2 * tinv z) = W₀ z := by
  change W₀ (w2 * tinv (w2 * tinv z)) = W₀ z
  rw [GlobalTheory.CompanionTheory.GL2LocalData.tinv_mul', transposeInv_weyl, tinv_tinv, ← mul_assoc, weyl_mul_weyl, one_mul]

theorem modulus_neg_one : modulus (-1 : F) = 1 := by
  have h : modulus (-1 : F) * modulus (-1 : F) = 1 := by
    rw [← modulus_mul]
    simp
  have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2

theorem mp_of_val_neg (a : Fˣ) (s : ℂ) : mp (-a) s = mp a s := by
  have : modulus (-(a : F)) = modulus (a : F) := by
    rw [← neg_one_mul, modulus_mul, modulus_neg_one, one_mul]
  simp only [mp, Units.val_neg, this]

theorem det_g (h z : GL (Fin 2) F) :
    GeneralLinearGroup.det (tinv z⁻¹ * w2 * h) =
      -(GeneralLinearGroup.det z * GeneralLinearGroup.det h) := by
  apply Units.ext
  have h1 : (tinv z⁻¹).val = z.valᵀ := by
    change ((z⁻¹)⁻¹ : GL (Fin 2) F).valᵀ = z.valᵀ
    rw [inv_inv]
  have h2 : ((w2 : GL (Fin 2) F).val).det = -1 := by
    simp [w2, Matrix.det_fin_two]
  simp only [GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_neg, Matrix.det_mul, h1,
    Matrix.det_transpose, h2]
  ring

theorem main (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (W₀ : GL (Fin 2) F → ℂ) (h z : GL (Fin 2) F) (s : ℂ) :
    e2r (h * (tinv z⁻¹ * w2 * h)⁻¹) = (z⁻¹ : GL (Fin 2) F).val *ᵥ e1 ∧
    dW2 W₀ (h * (tinv z⁻¹ * w2 * h)⁻¹) = W₀ z ∧
    mp (GeneralLinearGroup.det (tinv z⁻¹ * w2 * h)) s =
      mp (GeneralLinearGroup.det z) s * mp (GeneralLinearGroup.det h) s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h_mul_inv, second_vector_long_weyl_transpose_inv]
  · rw [h_mul_inv, dual_whittaker_long_weyl_transpose_inv]
  · rw [det_g, mp_of_val_neg, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_mul]

end D

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_change_of_variables_identities : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (W₀ : GL (Fin 2) F → ℂ) (h z : GL (Fin 2) F) (s : ℂ), e2r (h * (tinv z⁻¹ * w2 * h)⁻¹) = (z⁻¹ : GL (Fin 2) F).val *ᵥ e1 ∧ dW2 W₀ (h * (tinv z⁻¹ * w2 * h)⁻¹) = W₀ z ∧ mp (GeneralLinearGroup.det (tinv z⁻¹ * w2 * h)) s = mp (GeneralLinearGroup.det z) s * mp (GeneralLinearGroup.det h) s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar.main
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair

theorem mp_inv' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F]
    (a : Fˣ) (s : ℂ) : mp a⁻¹ s = mp a (-s) := by
  have h1 : mp a⁻¹ s * mp a s = 1 := by
    rw [← KTwoWhittakerSubgroup.mp_mul]
    simp [mp]
  have h2 : mp a (-s) * mp a s = 1 := by
    rw [← KTwoWhittakerSubgroup.mp_add]
    simp [mp]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h1) (h1.trans h2.symm)

theorem det_unipotent_adele {F : Type} [Field F] (u : F) : GeneralLinearGroup.det (uni2 u) = 1 := by
  ext
  simp [GeneralLinearGroup.val_det_apply, uni2, Matrix.det_fin_two]

theorem unipotent_inv_eq_neg {F : Type} [Field F] (u : F) : (uni2 u)⁻¹ = uni2 (-u) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_neg_identity_GL2 {F : Type} [Field F] : GeneralLinearGroup.det (dg2 (-1 : Fˣ) (-1)) = 1 := by
  ext
  simp [GeneralLinearGroup.val_det_apply, dg2, Matrix.det_fin_two]

theorem main : Ad3.K.GL2LocalData.GodementSectionDual := by
  intro F _ _ _ _ _ _ ψ hψ ν hν0 W₀ hW₀ Φ hΦ₀ h
  have hyp : LFS.Hyp ψ ν W₀ Φ :=
    ⟨hψ, hν0, ⟨V2 ψ ν ν⁻¹, GlobalTheory.CompanionTheory.WhittakerInducedSpan.whittaker_induced_space GlobalTheory.CompanionTheory.WhitFE.feGen F ψ hψ ν ν⁻¹ hν0 (GlobalTheory.CompanionTheory.LocalChar.sInv F ν hν0).1, hW₀⟩, hΦ₀⟩
  haveI hμ : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  haveI hRi : (LFS.hG ψ).IsMulRightInvariant := by unfold LFS.hG; infer_instance
  haveI hinv : (LFS.hG ψ).IsInvInvariant := ⟨Measures.inv_eq_self_GL F 2 (LFS.hG ψ)⟩
  obtain ⟨-, hν, ⟨V', H, hW⟩, hΦ⟩ := id hyp
  set A : GL (Fin 2) F → ℂ := fun z => W₀ z * mp (GeneralLinearGroup.det z) (-(3 / 2)) with hA
  set g3 : GL (Fin 3) F := w3 * tinv (em h) with hg3
  have hLpt : ∀ y : GL (Fin 2) F, W₀ y⁻¹⁻¹ * mp (GeneralLinearGroup.det y⁻¹) (3 / 2) * LFS.inn ψ Φ y⁻¹ g3 =
      A y * Lpart ψ (Pf Φ h y) := by
    intro y
    rw [inv_inv, map_inv, mp_inv', hg3, GlobalTheory.T.inner_integral_eq_left_partial_fourier F ψ Φ y h]
  have hLint : Integrable (fun z => A z * Lpart ψ (Pf Φ h z)) (LFS.hG ψ) := by
    have h0 := (GlobalTheory.CompanionTheory.LFAbs.integrable_wPhi F ψ ν W₀ Φ hyp g3).comp_inv
    exact h0.congr (Filter.Eventually.of_forall hLpt)
  have hL : dW3 (LFS.Wp ψ W₀ Φ) (em h) =
      mp (GeneralLinearGroup.det h) (-1) * ∫ z, A z * Lpart ψ (Pf Φ h z) ∂LFS.hG ψ := by
    change LFS.Wp ψ W₀ Φ g3 = _
    unfold LFS.Wp
    rw [hg3, GlobalTheory.T.modulus_det_long_weyl_block F h, ← hg3]
    congr 1
    rw [← integral_inv_eq_self (fun k => W₀ k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * LFS.inn ψ Φ k g3)]
    exact integral_congr_ae (Filter.Eventually.of_forall hLpt)
  set f : GL (Fin 2) F → ℂ := fun g =>
    dFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * dW2 W₀ (h * g⁻¹) with hf
  have hsub : ∫ g, f g ∂LFS.hG ψ = ∫ z, f (tinv z⁻¹ * w2 * h) ∂LFS.hG ψ := by
    have e1' := integral_mul_right_eq_self (μ := LFS.hG ψ) f (w2 * h)
    have e2' := GlobalTheory.CompanionTheory.GL2LocalData.HaarTinv.integral_tinv ψ (fun u => f (u * (w2 * h)))
    have e3' := integral_inv_eq_self (fun z => f (tinv z * (w2 * h))) (LFS.hG ψ)
    rw [← e1', ← e2', ← e3']
    simp only [mul_assoc]
  have hcen : ∀ z, W₀ (dg2 (-1) (-1) * z) = W₀ z := by
    intro z
    rw [H.cen W₀ hW]
    simp
  have hdet : ∀ (z : GL (Fin 2) F) (s : ℂ),
      mp (GeneralLinearGroup.det (dg2 (-1) (-1) * z)) s = mp (GeneralLinearGroup.det z) s := by
    intro z s
    rw [map_mul, det_neg_identity_GL2, one_mul]
  have hpt : ∀ z : GL (Fin 2) F, f (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h) =
      (mp (GeneralLinearGroup.det h) (1 / 2) * mp (GeneralLinearGroup.det h) (-2)) *
        (A z * Rpart ψ (Pf Φ h z)) := by
    intro z
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.dual_change_of_variables_identities F W₀ h (dg2 (-1) (-1) * z) (1 / 2)
    simp only [hf, hA]
    rw [a1, a2, a3, GlobalTheory.T.partial_fourier_weyl_transpose_inverse F ψ hψ, hcen, hdet]
    have hz : mp (GeneralLinearGroup.det z) (-(3 / 2)) =
        mp (GeneralLinearGroup.det z) (-2) * mp (GeneralLinearGroup.det z) (1 / 2) := by
      rw [← KTwoWhittakerSubgroup.mp_add]
      norm_num
    rw [hz]
    ring
  have hR : ∫ g, f g ∂LFS.hG ψ = (mp (GeneralLinearGroup.det h) (1 / 2) * mp (GeneralLinearGroup.det h) (-2)) *
      ∫ z, A z * Rpart ψ (Pf Φ h z) ∂LFS.hG ψ := by
    rw [hsub, ← integral_mul_left_eq_self (fun z => f (tinv z⁻¹ * w2 * h)) (dg2 (-1) (-1))]
    simp only [hpt]
    rw [integral_const_mul]
  have hAc : Continuous A := by
    obtain ⟨U, hU⟩ := H.smooth W₀ hW
    have hWc : Continuous W₀ :=
      (GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant W₀ U.toSubgroup U.isOpen hU).continuous
    exact hWc.mul (GlobalTheory.CompanionTheory.LFHolP.continuous_mp_det _)
  have hRint : Integrable (fun z => A z * Rpart ψ (Pf Φ h z)) (LFS.hG ψ) := by
    obtain ⟨R, hRs⟩ := GlobalTheory.T.right_partial_fourier_support_bounded F ψ hψ Φ hΦ h
    obtain ⟨C, hC, hCs⟩ := GlobalTheory.T.whittaker_support_compact_bounded_entries F ψ hψ ν V' H W₀ hW R
    refine (hAc.mul (GlobalTheory.T.continuous_right_partial_fourier F ψ hψ Φ hΦ h)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hC fun z hz => ?_)
    have hz' : A z * Rpart ψ (Pf Φ h z) ≠ 0 := hz
    have hr := right_ne_zero_of_mul hz'
    have hw : W₀ z ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hz')
    exact hCs z hw (hRs z hr).1 (hRs z hr).2
  have hcore := GlobalTheory.T.left_right_partial_fourier_integral_eq F ψ hψ
    (fun p hp => (GlobalTheory.T.left_partial_fourier_twisted_integral F ψ hψ p hp).trans (GlobalTheory.T.right_partial_fourier_twisted_integral F ψ hψ p hp).symm)
    A (fun z => Pf Φ h z)
    (fun u z => by
      simp only [hA]
      rw [H.psi W₀ hW, map_mul, det_unipotent_adele, one_mul, mul_assoc])
    (fun u z M => by
      simp only [Pf]
      rw [_root_.mul_inv_rev, unipotent_inv_eq_neg, Units.val_mul, Matrix.mul_assoc _ _ M]
      congr 2
      rw [← Matrix.mulVec_mulVec]
      congr 1
      ext i
      fin_cases i <;> simp [uni2, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
    (fun z => GlobalTheory.T.pullback_schwartz_bruhat_matrix F Φ hΦ h z) hLint hRint
  change dW3 (LFS.Wp ψ W₀ Φ) (em h) = _ * ∫ g, f g ∂LFS.hG ψ
  rw [hL, hR, hcore, ← mul_assoc, ← mul_assoc, ← KTwoWhittakerSubgroup.mp_add, ← KTwoWhittakerSubgroup.mp_add]
  norm_num

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair
end
