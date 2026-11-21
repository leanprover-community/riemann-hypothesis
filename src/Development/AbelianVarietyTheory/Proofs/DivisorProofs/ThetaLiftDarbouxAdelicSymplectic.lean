import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadratic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic

section
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchCoords

open GlobalTheory.FockVacuum in

theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (AE F E)) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_cplx_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoords
end
end

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (AE F E)) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  atlas_forward_decl GlobalTheory.ArchCoords.exists_coords
end

section
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchRhoPure

variable (F : Type) [Field F] [NumberField F] in

def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_apply {F : Type} [Field F] [NumberField F] (a : AF F) : evHom F a = evI F a := rfl

theorem rho_pureA_schrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (AE F E), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f h
  have hw : At (evI F) (d.e u) := fun r hr => by rw [← map_smul, hu r hr, map_zero]
  show schr ψ (d.e u) (pureA F f h) = _
  generalize d.e u = w at hw ⊢
  obtain ⟨p, q⟩ := w
  funext x
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + ArchUniq.locV p :=
    funext fun i => map_add (evHom F) (x i) (p i)
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, evI F (p i) * evI F (q i)) / 2 := by
    set z : mixedEmbedding.mixedSpace F := ∑ i, evI F (p i) * evI F (q i) with hz
    have hpq : evHom F (p ⬝ᵥ q) = z := by
      rw [RingHom.map_dotProduct]; rfl
    have hxq : evHom F (x ⬝ᵥ q) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i) := by
      rw [RingHom.map_dotProduct]; rfl
    have key : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z := by
      rw [← map_add, ← add_mul, ← map_add, invOf_two_add_invOf_two, map_one, one_mul]
    rw [← evHom_apply, map_add, map_mul, hpq, hxq, map_add]
    linarith
  simp only [schr, pureA, GlobalTheory.ArchUniq.schrF, GlobalTheory.ArchUniq.trP, GlobalTheory.ArchUniq.locV] at harch ⊢
  rw [hψ.2.2 _ hAt, hfin, htr, harch, ← mul_assoc]

end GlobalTheory.ArchRhoPure
end
end

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (AE F E), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  atlas_forward_decl GlobalTheory.ArchRhoPure.rho_pureA_schrF
end

section
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLiftComp

open Matrix GlobalTheory.RealLiftGen

theorem exists_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (InfinitePlace F → Mat R S), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) ∧ ∀ w (M M' : Mat R S), C w * M = C w * M' → M = M' := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm R S := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm R S * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm R S), Matrix.mul_assoc (Jm R S), hF, Jm_mul_Jm]
    have h2 : (Jm R S * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm R S * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm R S * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : UG (cA σ) J → InfinitePlace F → Matrix β β ℂ :=
    fun g w => (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMmul : ∀ g h w, M (g * h) w = M g w * M h w := by
    intro g h w
    simp only [hM, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM1 : ∀ w, M 1 w = 1 := by
    intro w
    simp only [hM, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ g w, (M g w)ᵀ * K w * (M g w).map star = K w := by
    intro g w
    have hg := g.2
    change ((g.1 : Matrix β β (AE F E)))ᵀ * J * ((g.1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M g w)ᵀ * J.map (piInf (τ w)) * (M g w).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  let k : UG (cA σ) J →* (InfinitePlace F → Mat R S) :=
    { toFun := fun g w => A' w * M g w * C w
      map_one' := by funext w; simp only [hM1, Matrix.mul_one, hAC, Pi.one_apply]
      map_mul' := by
        intro g h; funext w
        simp only [hMmul, Pi.mul_apply]
        calc A' w * (M g w * M h w) * C w = A' w * M g w * (C w * A' w) * M h w * C w := by
              rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hk : ∀ g w, k g w = A' w * M g w * C w := fun _ _ => rfl
  have hCk : ∀ g w, C w * k g w = M g w * C w := by
    intro g w; simp only [hk, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨k, ?_, fun g w => (hCk g w).symm, fun g w => ?_, fun w X X' h => ?_⟩
  · have h1 : Continuous (fun g : UG (cA σ) J => ((g.1 : Matrix β β (AE F E)))) :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_pi fun w => ?_
    exact (continuous_const.matrix_mul (h1.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (τ w)))).matrix_mul
      continuous_const
  · have hT : (k g w)ᵀ * Jm R S * (k g w).map star = Jm R S := by
      rw [← hF w]
      calc (k g w)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (k g w).map star
          = (C w * k g w)ᵀ * K w * (C w * k g w).map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = (C w)ᵀ * ((M g w)ᵀ * K w * (M g w).map star) * (C w).map star := by
            simp only [hCk, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMu]
    have h2 := congrArg (fun X => X.map star) hT
    simp only [map_star_mul, Jm_map_star, map_star_star] at h2
    exact h2
  · have := congrArg (fun Y => A' w * Y) h
    simpa only [← Matrix.mul_assoc, hAC, Matrix.one_mul] using this

end GlobalTheory.RealLiftComp
end
end

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_orthonormal_J : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (InfinitePlace F → Mat R S), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) ∧ ∀ w (M M' : Mat R S), C w * M = C w * M' → M = M' := by
  atlas_forward_decl GlobalTheory.RealLiftComp.exists_comp
end

section
section
noncomputable section

open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

omit [Fintype l] in
theorem continuous_pPart : Continuous (pPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold pPart
  fun_prop

omit [Fintype l] in
theorem continuous_qPart : Continuous (qPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold qPart
  fun_prop

theorem continuous_inner_rho_schwartz (φ f : Sch l) :
    Continuous fun w : l ⊕ l → ℝ => ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ := by
  have e : ∀ w : l ⊕ l → ℝ, ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ = ∫ x, starRingEnd ℂ (φ x) * rhoFun w f x := by
    intro w
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_rho w (f.toLp 2),
      rhoFun_congr w (f.coeFn_toLp 2 volume)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp [mul_comm]
  simp only [e]
  refine continuous_of_dominated (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 f) (fun w => ?_)
    (fun w => .of_forall fun x => ?_) ((φ.integrable (μ := volume)).norm.mul_const _) (.of_forall fun x => ?_)
  · exact ((continuous_star.comp φ.continuous).mul
      ((continuous_phase w).mul (f.continuous.comp (continuous_add_const _)))).aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_conj, rhoFun, norm_mul, norm_phase, one_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  · simp only [rhoFun, phase]
    have := continuous_pPart (l := l)
    have := continuous_qPart (l := l)
    fun_prop

theorem continuous_rho_schwartz (f : Sch l) : Continuous fun w : l ⊕ l → ℝ => rho w (f.toLp 2) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  set v : L2 l := f.toLp 2 with hv
  set g : L2 l := (rhoSch w₀ f).toLp 2 with hg
  have h0 : rho w₀ v = g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_rho w₀ (f.toLp 2), rhoFun_congr w₀ (f.coeFn_toLp 2 volume),
      (rhoSch w₀ f).coeFn_toLp 2 volume] with x h1 h2 h3
    rw [h1, h2, h3, coe_rhoSch]
  have hsq : ∀ w, ‖rho w v - rho w₀ v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * (⟪g, rho w v⟫_ℂ).re := by
    intro w
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, inner_re_symm, h0,
      RCLike.re_to_complex]
    ring
  have hc : Continuous fun w => ‖rho w v - rho w₀ v‖ ^ 2 := by
    simp only [hsq]
    exact continuous_const.sub (continuous_const.mul (continuous_re.comp (continuous_inner_rho_schwartz (rhoSch w₀ f) f)))
  have ht := hc.tendsto w₀
  simp only [sub_self, norm_zero] at ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto _).comp ht
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

theorem continuous_rho_prod : Continuous fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1 := by
  have hd : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)))) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  exact continuous_prod_of_dense_continuous_lipschitzWith (fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1) 1 hd
    (by rintro _ ⟨f, rfl⟩; exact continuous_rho_schwartz f) fun w => (rho w).lipschitz

theorem continuous_rho : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v :=
  fun l _ v => (continuous_rho_prod (l := l)).comp (f := fun w : l ⊕ l → ℝ => ((v, w) : L2 l × (l ⊕ l → ℝ)))
    (Continuous.prodMk continuous_const continuous_id)

end GlobalTheory.RealWeil
end
end

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_rho_apply : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v := by
  atlas_forward_decl GlobalTheory.RealWeil.continuous_rho
end

section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillator_action_normalising_schrodingerOperators : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  first | exact @GlobalTheory.SchrodOsc.exists_osc | exact GlobalTheory.SchrodOsc.exists_osc | (intros; apply GlobalTheory.SchrodOsc.exists_osc <;> assumption)
end

section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_symplecticHom_of_indefiniteUnitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  first | exact @GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | exact GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | (intros; apply GlobalTheory.ColAction.exists_symplectic_hom_of_unitary <;> assumption)
end

section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLie_of_indefiniteUnitaryLie_rightAction : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  first | exact @GlobalTheory.RealLift.SpLie.exists_sp_rightAct | exact GlobalTheory.RealLift.SpLie.exists_sp_rightAct | (intros; apply GlobalTheory.RealLift.SpLie.exists_sp_rightAct <;> assumption)
end

section
section
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

noncomputable section
open Complex
open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace Real FourierTransform ContDiff SchwartzMap

namespace GlobalTheory.RealWeil.FourierConjProductVanishing

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem ae_eq_zero_of_fourier_eq_zero {D : V → ℂ} (hD : Integrable D) (hF : ∀ ξ, 𝓕 D ξ = 0) :
    D =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hD.locallyIntegrable fun g hg hgc => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  set ψ : 𝓢(V, ℂ) := hg₁.toSchwartzMap hg₂ with hψ
  set φ : 𝓢(V, ℂ) := 𝓕⁻ ψ with hφ
  have h0 : ∀ x, (𝓕 φ) x = (g x : ℂ) := fun x => by
    rw [hφ, FourierTransform.fourier_fourierInv_eq, hψ]
    simp
  have h1 : ∫ x, g x • D x = ∫ x, (𝓕 φ) x * D x := by
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [h0, Complex.real_smul]
  have h2 : ∫ x, (𝓕 φ) x * D x = ∫ x, φ x * 𝓕 D x := by
    have := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner (φ.integrable (μ := volume)) hD
    simpa using! this
  rw [h1, h2]
  simp [hF]

variable {l : Type} [Fintype l]

def pt (p q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) (fun i => q i)

theorem pPart_pt (p q : EuclideanSpace ℝ l) : pPart (pt p q) = p := by
  ext i; simp [pPart, pt]

theorem qPart_pt (p q : EuclideanSpace ℝ l) : qPart (pt p q) = q := by
  ext i; simp [qPart, pt]

theorem fourier_conj_mul_eq_zero (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) (p ξ : EuclideanSpace ℝ l) :
    𝓕 (fun x => conj (f x) * g (x + p)) ξ = 0 := by
  have h1 := h (pt p (-ξ))
  rw [L2.inner_def] at h1
  have h2 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x = 0 := by
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rho (pt p (-ξ)) g] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  have h3 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x =
      cexp (((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) * 𝓕 (fun x => conj (f x) * g (x + p)) ξ := by
    rw [Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [rhoFun, phase, pPart_pt, qPart_pt, smul_eq_mul]
    have e : (((2 * π * ⟪-ξ, x⟫ + π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) =
        ((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I + ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * I := by
      rw [inner_neg_left, real_inner_comm]
      push_cast
      ring
    rw [e, Complex.exp_add]
    ring
  rw [h2] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left (Complex.exp_ne_zero _)

theorem integrable_conj_mul_shift (f g : L2 l) (p : EuclideanSpace ℝ l) :
    Integrable (fun x => conj (f x) * g (x + p)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) f (rho (pt p 0) g)).congr ?_
  filter_upwards [coeFn_rho (pt p 0) g] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]
  simp [rhoFun, phase, pPart_pt, qPart_pt]

theorem eq_zero_or_eq_zero_of_inner_rho (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) : f = 0 ∨ g = 0 := by
  have hz : ∀ p : EuclideanSpace ℝ l, ∀ᵐ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 = 0 := by
    intro p
    filter_upwards [ae_eq_zero_of_fourier_eq_zero (integrable_conj_mul_shift f g p)
      (fourier_conj_mul_eq_zero f g h p)] with x hx
    have hx' : conj ((f : _ → ℂ) x) * (g : _ → ℂ) (x + p) = 0 := hx
    rcases mul_eq_zero.1 hx' with h0 | h0
    · rw [map_eq_zero] at h0
      simp [h0]
    · simp [h0]
  have hfm : Measurable fun x => ‖(f : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable f).measurable.enorm.pow_const 2
  have hgm : Measurable fun x => ‖(g : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable g).measurable.enorm.pow_const 2
  have hprod : (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2) = 0 := by
    calc (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2)
        = ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ∫⁻ p, ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          rw [← lintegral_mul_const _ hfm]
          refine lintegral_congr fun x => ?_
          rw [lintegral_add_left_eq_self (fun y => ‖(g : _ → ℂ) y‖ₑ ^ 2) x]
      _ = ∫⁻ x, ∫⁻ p, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_congr fun x => ?_
          exact (lintegral_const_mul _ (hgm.comp (measurable_const_add x))).symm
      _ = ∫⁻ p, ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_lintegral_swap ?_
          exact ((hfm.comp measurable_fst).mul (hgm.comp measurable_add)).aemeasurable
      _ = 0 := by
          rw [← lintegral_zero]
          exact lintegral_congr fun p => lintegral_eq_zero_of_ae_eq_zero (hz p) |>.trans rfl
  have key : ∀ u : L2 l, (∫⁻ x, ‖(u : _ → ℂ) x‖ₑ ^ 2) = 0 → u = 0 := by
    intro u hu
    have hum : Measurable fun x => ‖(u : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable u).measurable.enorm.pow_const 2
    rw [lintegral_eq_zero_iff hum] at hu
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hu] with x hx
    simpa using hx
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact Or.inl (key f h0)
  · exact Or.inr (key g h0)

theorem rho_symm_apply (w : l ⊕ l → ℝ) (v : L2 l) :
    (rho w).symm v = (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹ • rho (-w) v := by
  rw [LinearIsometryEquiv.symm_apply_eq, map_smul, rho_rho, add_neg_cancel, rho_zero,
    inv_smul_smul₀ (Complex.exp_ne_zero _)]

def opSet (l : Type) [Fintype l] : Set (L2 l →L[ℂ] L2 l) :=
  Set.range fun cw : ℂ × (l ⊕ l → ℝ) => cw.1 • ((rho cw.2).toContinuousLinearEquiv : L2 l →L[ℂ] L2 l)

theorem star_mem_opSet : ∀ A ∈ opSet l, star A ∈ opSet l := by
  rintro _ ⟨⟨c, w⟩, rfl⟩
  refine ⟨⟨conj c * (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹, -w⟩, ?_⟩
  rw [star_smul, ContinuousLinearMap.star_eq_adjoint]
  ext v
  have e := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) (LinearIsometryEquiv.adjoint_eq_symm (rho w))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at e ⊢
  rw [e, rho_symm_apply, smul_smul]
  rfl

theorem irreducible_opSet (S : Submodule ℂ (L2 l)) (hS : IsClosed (S : Set (L2 l)))
    (hst : ∀ A ∈ opSet l, ∀ v ∈ S, A v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  haveI : CompleteSpace S := hS.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro f hf
  have hw : ∀ w, ⟪f, rho w g⟫_ℂ = 0 := by
    intro w
    have hm : rho w g ∈ S := by
      have := hst _ ⟨⟨1, w⟩, rfl⟩ g hg
      simpa using this
    exact Submodule.inner_left_of_mem_orthogonal hm hf
  exact (eq_zero_or_eq_zero_of_inner_rho f g hw).resolve_right hg0

end GlobalTheory.RealWeil.FourierConjProductVanishing

namespace GlobalTheory.RealWeil

open GlobalTheory.RealWeil.FourierConjProductVanishing in

theorem schur_rho_l2 : ∀ (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l), (∀ w v, U (rho w v) = rho w (U v)) →
    ∃ a : ℂ, ∀ v, U v = a • v := by
  intro l _ U hU
  obtain ⟨c, hc⟩ := Formalism.MainNotions.BridgeCSchur.schur_bounded (opSet l) star_mem_opSet
    (fun S hS hst => irreducible_opSet S hS hst) (U.toContinuousLinearEquiv : L2 l →L[ℂ] L2 l) (by
      rintro _ ⟨⟨c, w⟩, rfl⟩
      ext v
      simp [hU])
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) hc
  simpa using this

end GlobalTheory.RealWeil
end
end

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_equivariant_isometry_scalar : ∀ (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l), (∀ w v, U (rho w v) = rho w (U v)) →
    ∃ a : ℂ, ∀ v, U v = a • v := by
  atlas_forward_decl GlobalTheory.RealWeil.schur_rho_l2
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem sq_scalar_character : ∀ (G G' M H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [Group M]
    [TopologicalSpace M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] (pr : G' →* M) (s : G →* M)
    (om : G' →* (H ≃ₗᵢ[ℂ] H)) (ω : G →* (H ≃ₗᵢ[ℂ] H)) (ε : G'), IsCoveringMap pr → Function.Surjective pr →
    (∀ g, pr g = 1 → g = 1 ∨ g = ε) → (∀ v, om ε v = -v) → Continuous s → (∀ v, Continuous fun g => om g v) →
    (∀ v, Continuous fun g => ω g v) → (∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v) →
    ∃ η : G → ℂ, (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      ∀ g g' (a : ℂ), pr g' = s g → (∀ v, ω g v = a • om g' v) → a ^ 2 = η g := by
  intro G G' M H _ _ _ _ _ _ _ _ _ pr s om ω ε hcov hsurj hker hε hs hom hω hrel
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : H)
  have huniq : ∀ g (g₁ g₂ : G') (a b : ℂ), pr g₁ = s g → pr g₂ = s g →
      (∀ v, ω g v = a • om g₁ v) → (∀ v, ω g v = b • om g₂ v) → a ^ 2 = b ^ 2 := by
    intro g g₁ g₂ a b h₁ h₂ ha hb
    have hw : om g₁ v₀ ≠ 0 := by
      intro h; apply hv₀; exact (om g₁).map_eq_zero_iff.mp h
    have hk : pr (g₁⁻¹ * g₂) = 1 := by simp [map_mul, map_inv, h₁, h₂]
    rcases hker _ hk with h | h
    · have h2 : g₂ = g₁ := by rw [← mul_inv_cancel_left g₁ g₂, h, mul_one]
      subst h2
      have : a • om g₂ v₀ = b • om g₂ v₀ := by rw [← ha, ← hb]
      have hab : a = b := smul_left_injective ℂ hw this
      rw [hab]
    · have h2 : g₂ = g₁ * ε := by rw [← h, mul_inv_cancel_left]
      have : a • om g₁ v₀ = (-b) • om g₁ v₀ := by
        rw [← ha, hb, h2, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hε,
          map_neg, smul_neg, neg_smul]
      have hab : a = -b := smul_left_injective ℂ hw this
      rw [hab]; ring
  have hlift : ∀ g, ∃ g', pr g' = s g := fun g => hsurj (s g)
  choose L hL using hlift
  choose A hA using fun g => hrel g (L g) (hL g)
  refine ⟨fun g => A g ^ 2, ?_, ?_, ?_, ?_⟩
  · intro g h
    have hmul : pr (L g * L h) = s (g * h) := by simp [map_mul, hL]
    have hsc : ∀ v, ω (g * h) v = (A g * A h) • om (L g * L h) v := by
      intro v
      rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hA h, LinearIsometryEquiv.map_smul,
        hA g, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, smul_smul, mul_comm (A h)]
    have := huniq (g * h) (L (g * h)) (L g * L h) _ _ (hL _) hmul (hA _) hsc
    simp only
    rw [this]; ring
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨e, he, hpe⟩ := hcov.isLocalHomeomorph (L g₀)
    have hopen : IsOpen (s ⁻¹' e.target) := e.open_target.preimage hs
    have hmem : g₀ ∈ s ⁻¹' e.target := by
      show s g₀ ∈ e.target
      rw [← hL g₀, hpe]; exact e.map_source he
    let f : G → ℂ := fun g => (inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀) ^ 2
    have hf : ContinuousAt f g₀ := by
      have h1 : ContinuousAt (fun g => om (e.symm (s g)) v₀) g₀ :=
        (hom v₀).continuousAt.comp ((e.continuousAt_symm hmem).comp hs.continuousAt)
      exact ((h1.inner (hω v₀).continuousAt).div_const _).pow 2
    refine hf.congr ?_
    filter_upwards [hopen.mem_nhds hmem] with g hg
    have hpr : pr (e.symm (s g)) = s g := by rw [hpe]; exact e.right_inv hg
    obtain ⟨c, hc⟩ := hrel g _ hpr
    have hcval : c = inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀ := by
      rw [hc, inner_smul_right, LinearIsometryEquiv.inner_map_map, mul_div_assoc,
        div_self (inner_self_ne_zero.2 hv₀), mul_one]
    show f g = A g ^ 2
    simp only [f]
    rw [← hcval]
    exact huniq g _ _ c (A g) hpr (hL g) hc (hA g)
  · intro g
    refine pow_ne_zero 2 ?_
    intro h0
    have := hA g v₀
    rw [h0, zero_smul] at this
    exact hv₀ ((ω g).map_eq_zero_iff.mp this)
  · intro g g' a hg' ha
    exact huniq g g' (L g) a (A g) hg' (hL g) ha (hA g)

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_scalar_character_of_double_cover_unitary : ∀ (G G' M H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [Group M]
    [TopologicalSpace M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] (pr : G' →* M) (s : G →* M)
    (om : G' →* (H ≃ₗᵢ[ℂ] H)) (ω : G →* (H ≃ₗᵢ[ℂ] H)) (ε : G'), IsCoveringMap pr → Function.Surjective pr →
    (∀ g, pr g = 1 → g = 1 ∨ g = ε) → (∀ v, om ε v = -v) → Continuous s → (∀ v, Continuous fun g => om g v) →
    (∀ v, Continuous fun g => ω g v) → (∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v) →
    ∃ η : G → ℂ, (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      ∀ g g' (a : ℂ), pr g' = s g → (∀ v, ω g v = a • om g' v) → a ^ 2 = η g := by
  atlas_forward_decl GlobalTheory.sq_scalar_character
end

section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockToSchwartz_intertwines_metaplecticQuadratic : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  first | exact @GlobalTheory.RealLift.QuadFock.quad_fock | exact GlobalTheory.RealLift.QuadFock.quad_fock | (intros; apply GlobalTheory.RealLift.QuadFock.quad_fock <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.ArchRep

section Real

open MeasureTheory Filter Topology GlobalTheory.RealWeil Matrix

theorem hasDerivAt_of_sq {χ : ℝ → ℂ} {a : ℂ} (hc : ContinuousAt χ 0) (h0 : χ 0 = 1)
    (h : HasDerivAt (fun t => χ t ^ 2) a 0) : HasDerivAt χ (a / 2) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at h ⊢
  have h1 : Tendsto (fun t => χ t + 1) (𝓝[≠] 0) (𝓝 2) := by
    have := (hc.tendsto.add_const 1).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [h0, one_add_one_eq_two] at this
  refine (h.div h1 two_ne_zero).congr' ?_
  filter_upwards [h1.eventually_ne two_ne_zero] with t ht
  simp only [zero_add, h0, Pi.div_apply, Complex.real_smul]
  field_simp
  ring

variable {l : Type} [Fintype l] [DecidableEq l]

theorem continuous_sch {G : Type} [Group G] [TopologicalSpace G] {pr : G →* Matrix.symplecticGroup l ℝ}
    {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)} {omS : G →* (Sch l →L[ℂ] Sch l)}
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume) (hpr : Continuous pr)
    (h2 : ∀ v, Continuous fun g => om g v) (lam : Sch l →L[ℂ] ℂ) (f : Sch l) : Continuous fun g => lam (omS g f) := by
  have hm : Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) := continuous_subtype_val.comp hpr
  have key : ∀ A ∈ weylAlg l, ∀ f, Continuous fun g => schwartzToL2 l (A (omS g f)) := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, Continuous fun g => schwartzToL2 l (A (omS g f))) ?_ ?_ ?_ ?_ ?_ hA
    · intro f
      simpa only [h4, ContinuousLinearMap.one_apply, schwartzToL2_apply] using h2 (f.toLp 2 volume)
    · intro A w ih f
      simp only [toLp_dRho_omS h3 h4]
      refine continuous_finset_sum _ fun a _ => Continuous.smul (Complex.continuous_ofReal.comp ?_) (ih _)
      exact (continuous_apply a).comp
        (((continuous_const.matrix_mul hm.matrix_transpose).matrix_mul continuous_const).neg.matrix_mulVec continuous_const)
    · intro f
      simp only [ContinuousLinearMap.zero_apply]
      exact continuous_const
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact Λ.continuous.comp (continuous_pi fun i => key _ (hA i) f)

theorem realRep (hMp : GlobalTheory.Published.RealMetaplecticRepresentation) {G : Type} [Group G] [TopologicalSpace G]
    (s : G →* Matrix.symplecticGroup l ℝ) (hs : Continuous s) (ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (hc : ∀ v, Continuous fun g => ω g v)
    (hi : ∀ g w v, ω g (rho w v) = rho ((s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (ω g v)) :
    ∃ (ρ : G →* (Sch l →L[ℂ] Sch l)) (η : G → ℂ), (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      (∀ g w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(ρ g f₁) = rhoFun ((s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(ρ g f)) ∧
      (∀ g (f₁ f₂ : Sch l), ∫ x, star (ρ g f₁ x) * ρ g f₂ x = ∫ x, star (f₁ x) * f₂ x) ∧
      (∀ (L : Sch l →L[ℂ] ℂ) f, Continuous fun g => L (ρ g f)) ∧
      ∀ γ : ℝ → G, Continuous γ → γ 0 = 1 → ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ,
        (∀ t, (s (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) → ∀ a : ℂ,
        HasDerivAt (fun t => η (γ t)) a 0 → ∀ (L : Sch l →L[ℂ] ℂ) f,
          HasDerivAt (fun t => L (ρ (γ t) f)) (L (quad X f) + a / 2 * L f) 0 := by
  rcases isEmpty_or_nonempty l with hl | hl
  · refine ⟨1, fun _ => 1, fun _ _ => (mul_one _).symm, continuous_const, fun _ => one_ne_zero, fun g w f f₁ h => ?_,
      fun _ _ _ => rfl, fun L f => (continuous_const : Continuous fun _ : G => L f), fun γ _ _ X _ _ a ha L f => ?_⟩
    · rw [Subsingleton.elim ((s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) w]
      exact h
    · have h0 : a = 0 := ha.unique (hasDerivAt_const _ _)
      have hq : quad X f = 0 := by simp [quad]
      rw [h0, hq]
      simpa using hasDerivAt_const (0 : ℝ) (L f)
  obtain ⟨G', _, _, _, pr, om, omS, ⟨hcov, hsurj, ε, -, hker, hε⟩, h2, h3, h4, h5, h6⟩ := hMp l
  have hinj : Function.Injective fun f : Sch l => (f.toLp 2 volume : L2 l) := SchwartzMap.injective_toLp 2 volume
  have hsm : ∀ (c : ℂ) (f : Sch l), ((c • f).toLp 2 volume : L2 l) = c • f.toLp 2 volume := fun c f =>
    (schwartzToL2 l).map_smul c f
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.MetaplecticScalarDeriv.exists_schwartz_one l
  have hv₀ : (f₀.toLp 2 volume : L2 l) ≠ 0 := fun h => by
    have : f₀ = 0 := hinj (h.trans (schwartzToL2 l).map_zero.symm)
    rw [this] at hf₀
    exact zero_ne_one hf₀
  haveI : Nontrivial (L2 l) := nontrivial_of_ne _ _ hv₀
  have hχ : ∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v := fun g g' h => by
    obtain ⟨a, ha⟩ := GlobalTheory.T.schur_equivariant_isometry_scalar l (ω g * om g'⁻¹) fun w v => by
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, Function.comp_apply, h3, hi, mulVec_mulVec, ← h,
        ← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one, Submonoid.coe_one, one_mulVec]
    refine ⟨a, fun v => ?_⟩
    rw [← ha, ← Function.comp_apply (f := ⇑(ω g * om g'⁻¹)), ← LinearIsometryEquiv.coe_mul, mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, mul_one]
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := GlobalTheory.T.sq_scalar_character_of_double_cover_unitary G G' _ (L2 l) pr s om ω ε hcov hsurj (fun g hg => (hker g).1 hg) hε hs h2
    hc hχ
  choose lf hlf using fun g => hsurj (s g)
  choose a ha using fun g => hχ g (lf g) (hlf g)
  have hl0 : ∀ g (f : Sch l), ω g (f.toLp 2 volume) = ((a g • omS (lf g)) f).toLp 2 volume := fun g f => by
    rw [ha, h4, ContinuousLinearMap.smul_apply, hsm]
  let ρ : G →* (Sch l →L[ℂ] Sch l) :=
    { toFun := fun g => a g • omS (lf g)
      map_one' := ContinuousLinearMap.ext fun f => hinj (by
        beta_reduce
        rw [← hl0, map_one]
        rfl)
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => hinj (by
        beta_reduce
        rw [ContinuousLinearMap.mul_apply, ← hl0, ← hl0, ← hl0, map_mul]
        rfl) }
  have hl1 : ∀ g (f : Sch l), ω g (f.toLp 2 volume) = (ρ g f).toLp 2 volume := hl0
  clear_value ρ
  refine ⟨ρ, η, hη1, hη2, hη3, fun g => GlobalTheory.MetaplecticScalarDeriv.intertwine_fun l _ (ω g) (ρ g) (hi g) (hl1 g),
    fun g f₁ f₂ => ?_, continuous_sch hi hl1 hs hc, fun γ hγ hγ0 X hX hγX b hb L f => ?_⟩
  · have e1 := SchwartzMap.inner_toL2_toL2_eq (ρ g f₁) (ρ g f₂) volume
    have e2 := SchwartzMap.inner_toL2_toL2_eq f₁ f₂ volume
    simp only [RCLike.inner_apply] at e1 e2
    simp only [Complex.star_def, mul_comm (starRingEnd ℂ _)]
    rw [← e1, ← e2, ← hl1, ← hl1, LinearIsometryEquiv.inner_map_map]
  · obtain ⟨δ, hδc, hδ0, -, hδX, hδd⟩ := h6 X hX
    have hpr : ∀ t, pr (δ t) = s (γ t) := fun t => Subtype.ext ((hδX t).trans (hγX t).symm)
    choose χ hχ' using fun t => hχ (γ t) (δ t) (hpr t)
    have e1 : ∀ t, ρ (γ t) f = χ t • omS (δ t) f := fun t => hinj (by
      beta_reduce
      rw [← hl1, hχ', h4, hsm])
    have hin : inner ℂ (f₀.toLp 2 volume : L2 l) (f₀.toLp 2 volume) ≠ 0 := inner_self_ne_zero.2 hv₀
    have e2 : χ = fun t => inner ℂ (om (δ t) (f₀.toLp 2 volume)) (ω (γ t) (f₀.toLp 2 volume)) /
        inner ℂ (f₀.toLp 2 volume : L2 l) (f₀.toLp 2 volume) := funext fun t => by
      rw [hχ', inner_smul_right, LinearIsometryEquiv.inner_map_map, mul_div_cancel_right₀ _ hin]
    have hχc : Continuous χ := by
      rw [e2]
      exact (((h2 _).comp hδc).inner ((hc _).comp hγ)).div_const _
    have hχ0 : χ 0 = 1 := by
      rw [e2]
      simp only [hδ0, hγ0, map_one, LinearIsometryEquiv.coe_one, id_eq]
      exact div_self hin
    have hd := hasDerivAt_of_sq hχc.continuousAt hχ0 (a := b) (by
      simpa only [fun t => hη4 _ _ _ (hpr t) (hχ' t)] using hb)
    have hd2 := (metaplectic_schwartz_smooth h3 h4 h5).2.2 L X hX δ hδ0 hδX hδd f
    simp only [e1, map_smul, smul_eq_mul]
    refine (hd.mul hd2).congr_deriv ?_
    rw [hχ0, hδ0, map_one, ContinuousLinearMap.one_apply]
    ring

end Real

section Haar

open MeasureTheory

theorem haar_coords {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ} [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure] (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, ∀ F : V → ℂ, ∫ y, F y ∂μ = k • ∫ x, F (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ), fun F => ?_⟩
  have h1 : ∫ y, F y ∂μ = ∫ x, F (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, F (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def]

end Haar

theorem sumPl_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ w, Module.End ℂ (V w)) (c : ι → ℂ) :
    GlobalTheory.RealLift.sumPl (fun w => L w + c w • 1) = GlobalTheory.RealLift.sumPl L + (∑ w, c w) • 1 := by
  have h1 : ∀ w, GlobalTheory.RealLift.atPl w (1 : Module.End ℂ (V w)) = 1 := fun w => by
    rw [GlobalTheory.RealLift.atPl, Module.End.one_eq_id, Function.update_eq_self w (fun i => (LinearMap.id : V i →ₗ[ℂ] V i))]
    exact PiTensorProduct.map_id
  simp only [GlobalTheory.RealLift.sumPl, GlobalTheory.RealLift.PolRangePf.atPl_add', GlobalTheory.RealLift.PolRangePf.atPl_smul', h1,
    Finset.sum_add_distrib, Finset.sum_smul]

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.RealWeil GlobalTheory.ArchUniq

theorem archRep : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines σ JB, ∀ Y, IsGen τ C γ Y → ∀ (T : Tens F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  intro hP hDer _ F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨n, θ, φ, φ₀, hp, hq, hφ, hφu⟩ := GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_frames F E σ α β κ P Q R S τ JA JB d a b A C hCM hFr
  obtain ⟨k, hkc, hkC, hkJ, hcan⟩ := GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_orthonormal_J F E σ β R S τ JB b C hCM hFr.2.2
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨ω, hωc, hωi⟩ := GlobalTheory.T.exists_oscillator_action_normalising_schrodingerOperators _ _ P Q R S φ hφ (GlobalTheory.T.continuous_rho_apply _) (UG (cA σ) JB) k hkc hkJ
  obtain ⟨s, hsc, hsφ⟩ := GlobalTheory.T.exists_continuous_symplecticHom_of_indefiniteUnitary _ _ P Q R S φ hφ (UG (cA σ) JB) k hkc hkJ
  obtain ⟨ρ, η, hη1, hη2, hη3, hρi, hρu, hρc, hρd⟩ := realRep hP.realMetaplecticRepresentation s hsc ω hωc fun g w v => by
    obtain ⟨c, rfl⟩ := φ.surjective w
    rw [hsφ, hωi]
  obtain ⟨kk, hkk⟩ := GlobalTheory.T.archimedean_frame_character_factorization hP F E σ β R S τ JB b C hCM hFr.2.2 η (fun g h _ _ => hη1 g h) hη2.continuousOn
    fun g _ => hη3 g
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑θ.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑θ := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  clear_value toE toV
  have hS := SchrTransport.schr_coords (trP F κ) θ φ₀ hp hq
  let ρ' : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ) :=
    { toFun := fun g => toV ∘L ρ g ∘L toE
      map_one' := ContinuousLinearMap.ext fun f => by
        rw [map_one]
        exact hVE f
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => by
        simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hEV] }
  have hρ' : ∀ g f, ρ' g f = toV (ρ g (toE f)) := fun _ _ => rfl
  clear_value ρ'
  refine ⟨ρ', fun w => kk w / 2, fun g _ => ⟨fun u hu f f₁ hf h => ?_, fun ν hν f₁ f₂ => ?_⟩, fun L f => ?_,
    fun γ hγ Y hY T L => ?_⟩
  · choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    obtain ⟨c, hc⟩ : ∃ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ, ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ :=
      ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, fun w => by
        have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
        rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    have hu' : At (evI F) (actB (cA σ) g u) := fun t ht => by
      rw [actB, ← Matrix.smul_mul, hu t ht, Matrix.zero_mul]
    have hc' : ∀ w, (actB (cA σ) g u).map (piInf (τ w)) = A w * (c w * (k g w)ᵀ) * (C w)ᵀ := fun w => by
      rw [actB, Matrix.map_mul, hc, Matrix.transpose_map, Matrix.mul_assoc, ← Matrix.transpose_mul, hkC,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have e1 : ⇑f₁ = schrF (trP F κ) (locV (d.e u).1, locV (d.e u).2) ⇑f := by
      funext y
      have := congrFun ((GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ u hu f fun _ => 1).symm.trans (hf fun _ => 1)) (liftV y)
      simpa [pureA, liftV] using this.symm
    have e2 : ⇑(toE f₁) = rhoFun (φ c) ⇑(toE f) := by
      have := hS (locV (d.e u).1, locV (d.e u).2) ⇑(toE f)
      rw [← htoV, hVE, ← e1, ← hφu u c hu hc] at this
      rw [htoE, this]
      funext x
      simp
    have e3 := hρi g _ _ _ e2
    rw [hsφ, hφu _ _ hu' hc'] at e3
    rw [GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ _ hu', hρ', hρ', htoV, htoV, hS, e3]
  · haveI : BorelSpace ({w : InfinitePlace F // w.IsReal} → ℝ) := Pi.borelSpace
    haveI : BorelSpace ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.borelSpace
    haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
    obtain ⟨r, hr⟩ := haar_coords ν θ
    rw [hr, hr]
    congr 1
    simp only [hρ', htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hρu]
    simp only [htoE, Function.comp_apply]
  · simp only [hρ']
    exact (hρc (L ∘L toV) (toE f)).continuousOn
  · have hkY : ∀ (t : ℝ) w, k (γ (Multiplicative.ofAdd t)) w = NormedSpace.exp (t • Y w) := fun t w =>
      hcan w _ _ ((hkC _ w).symm.trans (hY t w))
    have hYu : ∀ w, Y w ∈ upq R S := fun w => GlobalTheory.RealLiftGen.mem_upq_of (Y w) fun t => by
      have := congrArg (fun X => X.map star) (hkJ (γ (Multiplicative.ofAdd t)) w)
      simp only [GlobalTheory.RealLiftGen.map_star_mul, GlobalTheory.RealLiftGen.Jm_map_star, hkY] at this
      refine Eq.trans ?_ this
      congr 2
      ext i j
      simp
    obtain ⟨Z, hZ, hZφ, hZe⟩ := GlobalTheory.T.exists_symplecticLie_of_indefiniteUnitaryLie_rightAction _ _ P Q R S φ hφ Y hYu
    have hsZ : ∀ t : ℝ, (s (γ (Multiplicative.ofAdd t)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        NormedSpace.exp (t • Z) := fun t => Matrix.toLin'.injective (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := φ.surjective v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hsφ, hZe]
      simp only [hkY])
    have hd := hρd (fun t => γ (Multiplicative.ofAdd t)) (hγ.1.comp continuous_ofAdd) (by simp) Z hZ hsZ _
      (hkk γ hγ Y hY) (L ∘L toV) (toE (Φ T))
    obtain ⟨D, hD⟩ := hDer F E σ α β κ ψ JA JB d hψ
    have hΨ : ∀ c T, (toE.toLinearMap ∘ₗ Φ) (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) ((toE.toLinearMap ∘ₗ Φ) T) := by
      intro c T
      obtain ⟨u, ⟨hu, hc⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM fun w => A w * c w * (C w)ᵀ
      have e1 := (GlobalTheory.RealLift.actsLaws F κ (Φ T) _ _).2.2.2.2 _ (hΦ.2 u hu c hc T) (hD u hu (Φ T)).1
      ext x
      obtain ⟨y, rfl⟩ := θ.surjective x
      have e2 := SchrTransport.dRho_coords (trP F κ) θ φ₀ hp hq (locV (d.e u).1, locV (d.e u).2) (Φ T) (toE (Φ T))
        (by rw [← htoV, hVE]) y
      rw [← hφu u c hu hc] at e2
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [← e2, e1, htoE, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact (hD u hu (Φ T)).2 y
    have e3 := GlobalTheory.T.fockToSchwartz_intertwines_metaplecticQuadratic GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic _ _ P Q R S φ hφ _ hΨ Y hYu Z hZφ T
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at e3
    simp only [hρ']
    refine hd.congr_deriv ?_
    rw [e3, sumPl_add_smul]
    simp only [ContinuousLinearMap.comp_apply, hVE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, smul_eq_mul, Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.ArchRep

end
end
