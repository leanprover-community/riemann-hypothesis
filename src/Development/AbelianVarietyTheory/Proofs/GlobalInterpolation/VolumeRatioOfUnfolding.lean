import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IsometryTransportFrames
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeComplements
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLattStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_adelicAddChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  first | exact @GlobalTheory.LocalComponentChar.exists_localChar | exact GlobalTheory.LocalComponentChar.exists_localChar | (intros; apply GlobalTheory.LocalComponentChar.exists_localChar <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.DualIndexPow

theorem nIdx_eq_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  intro F _ _ ψ v c h
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-c))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  have hu : ∀ hx : WithZero.exp (-c) ≠ 0, Multiplicative.toAdd (WithZero.unzero hx) = -c :=
    fun _ => rfl

  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.psiDual F ψ v = GlobalTheory.LocalDensityProduct.colonV v a := by
    ext t
    rw [GlobalTheory.LocalDensityProduct.mem_colonV]
    change (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ _
    rw [h t, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, ha,
      WithZero.exp_neg, mul_inv_le_iff₀ (by simp), one_mul]
  have hi : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.intV F v = GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.intV F v := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.nIdx
  rw [hd, hi, (GlobalTheory.LocalDensityProduct.index_colonV v a ha0).2,
    NumberField.FinitePlace.norm_def, ha,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard]
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hu]
  simp [_root_.zpow_neg]

end GlobalTheory.DualIndexPow
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegersCharacterDualIndex_eq_residue_card_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  atlas_forward_decl GlobalTheory.DualIndexPow.nIdx_eq_zpow
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealAdeleCoord

theorem bijective_place {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {T : Type} (τ : T → (E →+* ℂ))
    (hτ : Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) :
    Function.Bijective fun ρ => InfinitePlace.mk ((τ ρ).comp (algebraMap F E)) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  obtain ⟨δ, h0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  constructor
  · intro i j hij
    apply hτ.1
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' h0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff hij) with e | e
    · simp only [e]
    · simp only [e, InfinitePlace.mk_conjugate_eq]
  · intro w
    obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk (ComplexEmbedding.lift E w.embedding))
    refine ⟨i, ?_⟩
    have := congrArg (fun v : InfinitePlace E => v.comap (algebraMap F E)) hi
    simp only [InfinitePlace.comap_mk, ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding] at this
    exact this

theorem exists_realCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∃ r : Ainf F ≃+* (T → ℝ), Continuous r ∧ Continuous r.symm ∧ (∀ a ρ, ((r a ρ : ℝ) : ℂ) = θ ρ (a ⊗ₜ[F] (1 : E))) ∧ (∀ a, LocalAdditiveCharacterDual.stdInf F a = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * ∑ ρ, r a ρ : ℝ) : ℂ))) ∧ ∀ a, (∀ w, a w ≠ 0) ↔ ∀ ρ, r a ρ ≠ 0 := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ
  haveI hF := h.1
  let u : T ≃ InfinitePlace F := Equiv.ofBijective _ (bijective_place σ h τ hτ)
  let s : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have hs : ∀ w, Continuous (s w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous
  have hs' : ∀ w, Continuous (s w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous
  have hsc : ∀ w x, ((s w x : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w x := fun w x =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) x
  let r : Ainf F ≃+* (T → ℝ) :=
    { toFun := fun a ρ => s (u ρ) (a (u ρ))
      invFun := fun y w => (s w).symm (y (u.symm w))
      left_inv := fun a => funext fun w => by
        obtain ⟨ρ, rfl⟩ := u.surjective w
        show (s (u ρ)).symm (s (u (u.symm (u ρ))) (a (u (u.symm (u ρ))))) = _
        rw [u.symm_apply_apply, RingEquiv.symm_apply_apply]
      right_inv := fun y => funext fun ρ => by
        show s (u ρ) ((s (u ρ)).symm (y (u.symm (u ρ)))) = _
        rw [RingEquiv.apply_symm_apply, u.symm_apply_apply]
      map_mul' := fun a b => funext fun ρ => map_mul (s (u ρ)) (a (u ρ)) (b (u ρ))
      map_add' := fun a b => funext fun ρ => map_add (s (u ρ)) (a (u ρ)) (b (u ρ)) }
  have hr : ∀ a ρ, r a ρ = s (u ρ) (a (u ρ)) := fun _ _ => rfl
  refine ⟨r, continuous_pi fun ρ => (hs _).comp (continuous_apply (u ρ)),
    continuous_pi fun w => (hs' w).comp (continuous_apply (u.symm w)), fun a ρ => ?_, fun a => ?_, fun a => ?_⟩
  · rw [GlobalTheory.InfAdeleCM.hom_tmul _ _ (hθ ρ).1 (hθ ρ).2, map_one, mul_one, hr, hsc]
    rfl
  · unfold LocalAdditiveCharacterDual.stdInf
    rw [← Complex.exp_sum, ← u.sum_comp]
    congr 1
    simp only [← hsc, ← hr, Complex.ofReal_re]
    push_cast
    rw [← Finset.mul_sum]
    ring
  · constructor
    · intro ha ρ
      rw [hr]
      exact (map_ne_zero _).2 (ha _)
    · intro ha w
      obtain ⟨ρ, rfl⟩ := u.surjective w
      exact (map_ne_zero (s (u ρ))).1 (ha ρ)

end GlobalTheory.RealAdeleCoord
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realAdele_coordinates_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∃ r : Ainf F ≃+* (T → ℝ), Continuous r ∧ Continuous r.symm ∧ (∀ a ρ, ((r a ρ : ℝ) : ℂ) = θ ρ (a ⊗ₜ[F] (1 : E))) ∧ (∀ a, LocalAdditiveCharacterDual.stdInf F a = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * ∑ ρ, r a ρ : ℝ) : ℂ))) ∧ ∀ a, (∀ w, a w ≠ 0) ↔ ∀ ρ, r a ρ ≠ 0 := by
  atlas_forward_decl GlobalTheory.RealAdeleCoord.exists_realCoord
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealSpaceCoord

theorem herm_eq_dot {P Q : ℕ} (x y : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm y x = star x ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ y) := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, Fintype.sum_sum_type, dotProduct, fromBlocks_mulVec, neg_mulVec,
    mul_comm]

theorem form_eq {M P Q : ℕ} (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (x y : Fin M → ℂ) :
    ∑ i, ∑ j, star (x i) * (Aᴴ * Formalism.UG.Jpq P Q * A) i j * y j = ActionCoordinates.herm (A *ᵥ y) (A *ᵥ x) := by
  rw [herm_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ M P Q hM J hJ A hA
  obtain ⟨e0, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ T τ θ h hτ hθ
  let B : T → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => by
    have hd : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    simp only [B]
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul]
    rw [hd]
    exact ((map_ne_zero (τ ρ)).2 hJ.2).isUnit
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ =>
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hM])).2 (hBA ρ)
  have he' : ∀ z ρ, θ ρ (e0.symm z) = z ρ := fun z ρ => by rw [← he, e0.apply_symm_apply]
  refine ⟨{ toFun := fun X ρ => A ρ *ᵥ fun i => θ ρ (X 0 i)
            invFun := fun z _ i => e0.symm fun ρ => (B ρ *ᵥ z ρ) i
            left_inv := fun X => ?_
            right_inv := fun z => ?_
            map_add' := fun X Y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ => rfl, fun X Y ρ => ?_⟩
  · funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [mulVec_mulVec, hBA, one_mulVec]
    rw [RingEquiv.symm_apply_eq]
    funext ρ
    rw [he]
  · funext ρ
    simp only [he']
    rw [mulVec_mulVec, hAB, one_mulVec]
  · funext ρ
    refine Eq.trans ?_ (mulVec_add (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    congr 1
    funext i
    simp
  · refine continuous_pi fun ρ => continuous_const.matrix_mulVec (continuous_pi fun i => ?_)
    simp only [← he]
    exact (continuous_apply ρ).comp (hc.comp ((continuous_apply i).comp (continuous_apply 0)))
  · exact continuous_pi fun _ => continuous_pi fun i => hc'.comp (continuous_pi fun ρ =>
      (continuous_apply i).comp (continuous_const.matrix_mulVec (continuous_apply ρ)))
  · refine Eq.trans ?_ (form_eq (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    rw [hA]
    simp only [hR, Formalism.UG.hform, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Mem.VolInfIso.infEmb_sigR σ (τ ρ) (θ ρ) h (hθ ρ)]
    congr 2
    exact (hθ ρ).1 _

end GlobalTheory.RealSpaceCoord
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realAdelicHermitian_signature_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  atlas_forward_decl GlobalTheory.RealSpaceCoord.exists_coord
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.SelfDualProduct

theorem exists_test (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, HasCompactSupport Φ ∧ Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), h1, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem integral_prod_exp {T V : Type} [Fintype T] [MeasurableSpace V] (ε : ℝ) (β : V → V → ℝ)
    (μ₀ : Measure V) [SigmaFinite μ₀] (f : V → ℂ) (y : T → V) :
    ∫ x : T → V, (∏ ρ, f (x ρ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (x ρ) (y ρ) : ℝ) : ℂ))
        ∂(Measure.pi fun _ : T => μ₀) = ∏ ρ, ActionCoordinates.fourierT ε β μ₀ f (y ρ) := by
  unfold ActionCoordinates.fourierT
  rw [← integral_fintype_prod_eq_prod (fun ρ (x : V) => f x *
    Complex.exp (2 * Real.pi * Complex.I * ((ε * β x (y ρ) : ℝ) : ℂ)))]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  rw [Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

theorem map_eq_pi : ∀ (T V W : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : W ≃ₜ+ (T → V)) (ε : ℝ) (β : V → V → ℝ) (μ₀ : Measure V), μ₀.IsAddHaarMeasure → ActionCoordinates.IsSelfDualFor ε β μ₀ → ∀ (μ : Measure W) (χ : W → W → ℂ), (∀ x y, χ x y = Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (e x ρ) (e y ρ) : ℝ) : ℂ))) → SelfDual μ χ → μ.map e = Measure.pi fun _ : T => μ₀ := by
  intro T V W _ _ _ _ _ _ _ _ _ _ e ε β μ₀ hμ₀ hsd μ χ hχ hμ
  haveI : IsTopologicalAddGroup W :=
    Topology.IsInducing.topologicalAddGroup (e : W →+ (T → V)) e.toHomeomorph.isInducing
  haveI := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set ν : Measure (T → V) := Measure.pi fun _ : T => μ₀ with hν
  haveI : ν.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h0 : μ.map e = Measure.addHaarScalarFactor (μ.map e) ν • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set c : NNReal := Measure.addHaarScalarFactor (μ.map e) ν
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hint : ∀ F : (T → V) → ℂ, ∫ x, F (e x) ∂μ = (c : ℂ) * ∫ x, F x ∂ν := fun F => by
    rw [← hemb.integral_map, h0, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hF : ∀ (f : V → ℂ) (y : W), ∫ x, (∏ ρ, f (e x ρ)) * χ x y ∂μ =
      (c : ℂ) * ∏ ρ, ActionCoordinates.fourierT ε β μ₀ f (e y ρ) := fun f y => by
    rw [← integral_prod_exp, ← hint]
    simp only [hχ]
  obtain ⟨φ, hφs, hφ0⟩ := exists_test V
  obtain ⟨-, hI, hinv⟩ := hsd φ
  have hc1 : Continuous fun x : T → V => ∏ ρ, φ (x ρ) :=
    continuous_finset_prod _ fun ρ _ => φ.continuous.comp (continuous_apply ρ)
  have hs1 : HasCompactSupport fun x : T → V => ∏ ρ, φ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun _ : T => hφs.isCompact) fun x hx => ?_
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  have hI1 : Integrable (fun y : T → V => (c : ℂ) * ∏ ρ, ActionCoordinates.fourierT ε β μ₀ φ (y ρ))
      (μ.map e) := by
    rw [h0]
    exact ((Integrable.fintype_prod (f := fun _ : T => ActionCoordinates.fourierT ε β μ₀ φ)
      fun _ => hI).const_mul _).smul_measure_nnreal
  have key := hμ.2 (fun x => ∏ ρ, φ (e x ρ)) (hc1.comp e.continuous)
    (hs1.comp_homeomorph e.toHomeomorph) (by
      simp only [hF]
      exact (hemb.integrable_map_iff).1 hI1) 0
  simp only [hF, mul_assoc] at key
  rw [integral_const_mul, hF] at key
  simp only [hinv, map_zero, neg_zero, Pi.zero_apply, hφ0, Finset.prod_const_one, mul_one] at key
  have h5 : c * c = 1 := by exact_mod_cast key
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [h0, h6, one_smul]

end GlobalTheory.SelfDualProduct
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_sumPairing_map_eq_pi : ∀ (T V W : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : W ≃ₜ+ (T → V)) (ε : ℝ) (β : V → V → ℝ) (μ₀ : Measure V), μ₀.IsAddHaarMeasure → ActionCoordinates.IsSelfDualFor ε β μ₀ → ∀ (μ : Measure W) (χ : W → W → ℂ), (∀ x y, χ x y = Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (e x ρ) (e y ρ) : ℝ) : ℂ))) → SelfDual μ χ → μ.map e = Measure.pi fun _ : T => μ₀ := by
  atlas_forward_decl GlobalTheory.SelfDualProduct.map_eq_pi
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory

theorem isFibreFamily_map_homeomorph : ∀ (V V' X X' : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] (e : V ≃ₜ V') (r : X ≃ₜ X') (μ : Measure V) (ν : Measure X) (f : V → X) (f' : V' → X') (B : Set X) (fib : X → Measure V), (∀ v, f' (e v) = r (f v)) → IsFibreFamily μ f id Set.univ ν B fib → IsFibreFamily (μ.map e) f' id Set.univ (ν.map r) (r '' B) fun b => (fib (r.symm b)).map e := by
  intro V V' X X' _ _ _ _ _ _ _ _ _ _ _ _ e r μ ν f f' B fib hf h
  obtain ⟨h1, h2, h3⟩ := h
  have he : MeasurableEmbedding e := e.measurableEmbedding
  have hr : MeasurableEmbedding r := r.measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [he.map_apply]
    convert h1 (r.symm b) using 2
    ext v
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.inter_univ, Set.mem_singleton_iff, id, hf]
    exact not_congr r.eq_symm_apply.symm
  · have := h2 (fun v => φ (e v)) (hφ.comp he.measurable)
    rw [Measure.restrict_univ] at this ⊢
    rw [he.lintegral_map, hr.lintegral_map, this]
    refine lintegral_congr fun b => ?_
    rw [he.lintegral_map, r.symm_apply_apply]
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [he.integrable_map_iff, r.symm_apply_apply]
      exact h4 b hb
    · have h6 := h5.comp (s := r '' B) r.symm.continuous.continuousOn (by
        rintro _ ⟨b, hb, rfl⟩
        rw [r.symm_apply_apply]
        exact hb)
      refine h6.congr fun b _ => ?_
      simp only [Function.comp]
      rw [he.integral_map]

end GlobalTheory
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreMeasureFamily_map_homeomorph : ∀ (V V' X X' : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] (e : V ≃ₜ V') (r : X ≃ₜ X') (μ : Measure V) (ν : Measure X) (f : V → X) (f' : V' → X') (B : Set X) (fib : X → Measure V), (∀ v, f' (e v) = r (f v)) → IsFibreFamily μ f id Set.univ ν B fib → IsFibreFamily (μ.map e) f' id Set.univ (ν.map r) (r '' B) fun b => (fib (r.symm b)).map e := by
  atlas_forward_decl GlobalTheory.isFibreFamily_map_homeomorph
end

section
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory.FibreProd

theorem le_of_lintegral_ball_eq {X : Type} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G H : X → ℝ≥0∞) (b : X) (hG : ContinuousAt G b) (hH : ContinuousAt H b)
    (h : ∀ r > 0, ∫⁻ x in Metric.ball b r, G x ∂ν = ∫⁻ x in Metric.ball b r, H x ∂ν) :
    H b ≤ G b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨d, hd1, hd2⟩ := exists_between hc2
  have e : ∀ᶠ x in 𝓝 b, G x < c ∧ d < H x :=
    (hG.eventually (gt_mem_nhds hc1)).and (hH.eventually (lt_mem_nhds hd2))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 e
  have h1 : ∫⁻ x in Metric.ball b r, G x ∂ν ≤ c * ν (Metric.ball b r) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).1.le
  have h2 : d * ν (Metric.ball b r) ≤ ∫⁻ x in Metric.ball b r, H x ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).2.le
  have h3 : c * ν (Metric.ball b r) < d * ν (Metric.ball b r) :=
    ENNReal.mul_lt_mul_left (Metric.measure_ball_pos ν b hr).ne' measure_ball_lt_top.ne hd1
  exact absurd (h2.trans ((h r hr).symm.le.trans h1)) h3.not_ge

theorem lintegral_preimage {V X : Type} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → X} {U : Set V} {B : Set X} {fib : X → Measure V}
    (hf : Measurable f) (hU : IsOpen U) (h : IsFibreFamily μ f id U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ U → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  have e1 : ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in U, (f ⁻¹' S).indicator φ v ∂μ := by
    rw [← lintegral_indicator hU.measurableSet]
    congr 1
    funext v
    by_cases hv : v ∈ U
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      exact indicator_apply_eq_zero.2 fun _ => hs v hv
  rw [e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ U := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [hv] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [hv] using hbS) _

theorem lintegral_fibre_prod : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  intro T V _ _ _ _ _ _ μ₀ _ q hq U hU fib hfib B hB Fib hFib b hb φ hφ
  classical
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hΦc : Continuous fun x : T → V => ∏ ρ, φ ρ (x ρ) :=
    continuous_finset_prod _ fun ρ _ => (hφ ρ).1.comp (continuous_apply ρ)
  have hΦs : HasCompactSupport fun x : T → V => ∏ ρ, φ ρ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun ρ => (hφ ρ).2.1) fun x hx => ?_
    rw [mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  obtain ⟨hI, hC⟩ := hFib.2.2 _ hΦc hΦs (subset_univ _)
  have hm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    ENNReal.measurable_ofReal.comp (hφ ρ).1.measurable
  have hGc : ContinuousOn (fun b => ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b)) B := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn hC).congr fun b hb => ?_
    have := ofReal_integral_eq_lintegral_ofReal (hI b hb)
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun ρ _ => (hφ ρ).2.2.2 _)
    simp only [Function.comp_apply]
    rw [this]
    congr 1
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => (hφ ρ).2.2.2 _]
  have hg : ∀ ρ t, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) = ENNReal.ofReal (∫ y, φ ρ y ∂(fib t)) :=
    fun ρ t => (ofReal_integral_eq_lintegral_ofReal
      ((hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 t (mem_univ _))
      (Filter.Eventually.of_forall (hφ ρ).2.2.2)).symm
  have hgc : ∀ ρ, Continuous fun t => ∫ y, φ ρ y ∂(fib t) := fun ρ =>
    continuousOn_univ.1 (hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).2
  have hgm : ∀ ρ, Measurable fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) := fun ρ => by
    simp only [hg]
    exact ENNReal.measurable_ofReal.comp (hgc ρ).measurable
  have hHc : Continuous fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
    have : (fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))) =
        fun b => ENNReal.ofReal (∏ ρ, ∫ y, φ ρ y ∂(fib (b ρ))) := by
      funext b
      rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => integral_nonneg (hφ ρ).2.2.2]
      simp only [hg]
    rw [this]
    exact ENNReal.continuous_ofReal.comp
      (continuous_finset_prod _ fun ρ _ => (hgc ρ).comp (continuous_apply ρ))
  have key : ∀ r > 0, ∫⁻ c in Metric.ball b r, ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib c) =
      ∫⁻ c in Metric.ball b r, ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ)) := by
    intro r hr
    have hQ : Measurable fun (x : T → V) ρ => q (x ρ) :=
      (continuous_pi fun ρ => hq.comp (continuous_apply ρ)).measurable
    rw [← lintegral_preimage hQ isOpen_univ hFib (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)))
      (Finset.measurable_prod _ fun ρ _ => (hm ρ).comp (measurable_pi_apply ρ))
      (fun v hv => absurd (mem_univ v) hv) _ measurableSet_ball,
      ← lintegral_indicator measurableSet_ball, ball_pi b hr]
    have e1 : ∀ x : T → V, ((fun (x : T → V) ρ => q (x ρ)) ⁻¹'
        (Set.pi univ fun ρ => Metric.ball (b ρ) r)).indicator
        (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) x =
        ∏ ρ, (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)) (x ρ) := by
      intro x
      by_cases hx : ∀ ρ, x ρ ∈ q ⁻¹' Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    have e2 : ∀ c : T → ℝ, (Set.pi univ fun ρ => Metric.ball (b ρ) r).indicator
        (fun c => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))) c =
        ∏ ρ, (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)) (c ρ) := by
      intro c
      by_cases hx : ∀ ρ, c ρ ∈ Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    simp only [e1, e2]
    rw [volume_pi, GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)))
        (fun ρ => (hm ρ).indicator (hq.measurable measurableSet_ball)),
      GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)))
        (fun ρ => (hgm ρ).indicator measurableSet_ball)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [lintegral_indicator (s := Metric.ball (b ρ) r) measurableSet_ball]
    refine lintegral_preimage hq.measurable hU hfib _ (hm ρ) (fun v hv => ?_) _ measurableSet_ball
    rw [image_eq_zero_of_notMem_tsupport fun h => hv ((hφ ρ).2.2.1 h), ENNReal.ofReal_zero]
  have hGb := hGc.continuousAt (hB.mem_nhds hb)
  exact le_antisymm
    (le_of_lintegral_ball_eq volume _ _ b hHc.continuousAt hGb fun r hr => (key r hr).symm)
    (le_of_lintegral_ball_eq volume _ _ b hGb hHc.continuousAt key)

end GlobalTheory.FibreProd
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreIntegral_pi_prod_eq_prod_fibreIntegral : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  atlas_forward_decl GlobalTheory.FibreProd.lintegral_fibre_prod
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.PerpFrameOfMatrix

theorem herm_eq_dot {P Q : ℕ} (u v : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm u v = star v ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ u := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    mul_comm, neg_mulVec]

theorem isPerpFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  intro P Q P' Q' hc x hx C h1 h2 ι hι
  have hx' : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0 := by
    rw [← herm_eq_dot, ActionCoordinates.herm_self]; exact_mod_cast hx
  have hperp : ∀ v, star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (C *ᵥ v) = 0 := fun v => by
    have h3 : star x ᵥ* (Formalism.UG.Jpq P Q * C) = 0 := by
      have := congrArg star h2
      rwa [star_mulVec, conjTranspose_mul, conjTranspose_conjTranspose,
        GlobalTheory.UnfoldingCompare.Jpq_conjTranspose, star_zero] at this
    rw [mulVec_mulVec, dotProduct_mulVec, h3, zero_dotProduct]
  refine ⟨fun v w => ?_, fun y => ⟨fun hy => ?_, ?_⟩, fun g => ⟨(hι g).2, fun v => ?_⟩⟩
  · rw [herm_eq_dot, herm_eq_dot, toLin'_apply, toLin'_apply, star_mulVec, mulVec_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, h1]
  · obtain ⟨N, B, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx' h1 h2
    have e : y = C *ᵥ ((N *ᵥ y) ∘ Sum.inl) + (N *ᵥ y) (Sum.inr ()) • x := by
      conv_lhs => rw [← one_mulVec y, ← hN, ← mulVec_mulVec, fromCols_mulVec]
      congr 1
      funext i
      simp [mulVec, dotProduct, mul_comm]
    have ha : (N *ᵥ y) (Sum.inr ()) = 0 := by
      rw [herm_eq_dot, e, mulVec_add, mulVec_smul, dotProduct_add, hperp, zero_add,
        dotProduct_smul, smul_eq_mul] at hy
      exact (mul_eq_zero.1 hy).resolve_right hx'
    refine ⟨(N *ᵥ y) ∘ Sum.inl, ?_⟩
    rw [ha, zero_smul, add_zero] at e
    rw [toLin'_apply, ← e]
  · rintro ⟨v, rfl⟩
    rw [herm_eq_dot, toLin'_apply, hperp]
  · simp only [ActionCoordinates.act, toLin'_apply, mulVec_mulVec, (hι g).1]

end GlobalTheory.PerpFrameOfMatrix
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrthogonalComplementUnitaryFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  atlas_forward_decl GlobalTheory.PerpFrameOfMatrix.isPerpFrame_of_matrix
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabiliserCutoff

variable {P Q : ℕ}

theorem qf_eq (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.qf x = PerpendicularEmbedding.qf x := by
  have h : ActionCoordinates.herm x x = PerpendicularEmbedding.herm x x := by
    simp [ActionCoordinates.herm, PerpendicularEmbedding.herm, ActionCoordinates.sgn, Fintype.sum_sum_type, sub_eq_add_neg]
  rw [ActionCoordinates.qf, h, PerpendicularEmbedding.herm_self, Complex.ofReal_re]

theorem qf_act (g : UpqT P Q) (x : PerpendicularEmbedding.Sp P Q) : PerpendicularEmbedding.qf (ActionCoordinates.act g x) = PerpendicularEmbedding.qf x := by
  have h : (PerpendicularEmbedding.qf (ActionCoordinates.act g x) : ℂ) = PerpendicularEmbedding.qf x := by
    rw [← GlobalTheory.QuadricSection.form_self, ← GlobalTheory.QuadricSection.form_self, ActionCoordinates.act, star_mulVec,
      mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      GlobalTheory.UpqTopology.mat_unitary]
  exact_mod_cast h

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem continuous_act (x : ActionCoordinates.Wsp P Q) : Continuous fun g : UpqT P Q => ActionCoordinates.act g x :=
  GlobalTheory.UpqTopology.continuous_mat.matrix_mulVec continuous_const

theorem eq_zero_of_herm {v : ActionCoordinates.Wsp P Q} (h : ∀ w, ActionCoordinates.herm v w = 0) : v = 0 := by
  funext i
  have := h (Pi.single i 1)
  rcases i with i | i <;>
    simpa [ActionCoordinates.herm, ActionCoordinates.sgn, Pi.single_apply, apply_ite] using this

theorem exists_cutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 →
    ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
    ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} →
    ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧
      ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  intro c P Q P' Q' x₀ h0 j ι hι hr
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  haveI := c.haar P' Q'
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P' Q' _ (c.haar P' Q')
  obtain ⟨s, hsm, hs⟩ := GlobalTheory.QuadricSection.exists_isSection P Q _ x₀ (qf_eq x₀ ▸ h0) rfl
  obtain ⟨L, hL⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 fun v hv =>
    eq_zero_of_herm fun w => by rw [← hι.1, hv]; simp [ActionCoordinates.herm])
  have hL' : ∀ v, L (j v) = v := fun v => LinearMap.congr_fun hL v
  let Φ : UpqT P' Q' → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun h b => ActionCoordinates.act h (Pi.single b 1)
  let π : UpqT P Q → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun g b => L (ActionCoordinates.act g (j (Pi.single b 1)))
  have hΦ : Continuous Φ := continuous_pi fun b => continuous_act _
  have hπ : Continuous π := continuous_pi fun b =>
    L.continuous_of_finiteDimensional.comp (continuous_act _)
  have hΦi : Function.Injective Φ := fun a b hab =>
    GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective (by
      ext x y
      simpa [Φ, ActionCoordinates.act] using congrFun (congrFun hab y) x)
  have hπι : ∀ a b, π (ι a * ι b) = Φ (a * b) := fun a b => by
    funext x
    simp only [π, Φ, act_mul, (hι.2.2 _).2, hL']
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P' Q')
  have hpos : c.cd P' Q' K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK1).ne'
  have hfin : c.cd P' Q' K ≠ ⊤ := hK.measure_lt_top.ne
  have hO : MeasurableSet (Φ '' K) := (hK.image hΦ).isClosed.measurableSet
  let F : ((Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q') → ℝ≥0∞ :=
    (Φ '' K).indicator fun _ => (c.cd P' Q' K)⁻¹
  have hF : Measurable F := measurable_const.indicator hO
  have hFΦ : ∀ h, F (Φ h) = K.indicator (fun _ => (c.cd P' Q' K)⁻¹) h := fun h => by
    by_cases hh : h ∈ K
    · simp only [F, Set.indicator_of_mem hh, Set.indicator_of_mem (Set.mem_image_of_mem Φ hh)]
    · simp only [F, Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (mt hΦi.mem_set_image.1 hh)]
  refine ⟨fun g => F (π (g * s (ActionCoordinates.act g⁻¹ x₀))), ?_, fun g => ?_⟩
  · exact hF.comp (hπ.measurable.comp (measurable_id.mul
      (hsm.comp ((continuous_act x₀).comp continuous_inv).measurable)))
  · obtain ⟨h₀, hh₀⟩ : g * s (ActionCoordinates.act g⁻¹ x₀) ∈ Set.range ι := by
      rw [hr]
      change ActionCoordinates.act (g * s (ActionCoordinates.act g⁻¹ x₀)) x₀ = x₀
      have e : ActionCoordinates.act (s (ActionCoordinates.act g⁻¹ x₀)) x₀ = ActionCoordinates.act g⁻¹ x₀ := hs _ (qf_act _ _)
      rw [act_mul, e, ← act_mul, mul_inv_cancel, act_one]
    have e : ∀ h, F (π (ι h * g * s (ActionCoordinates.act (ι h * g)⁻¹ x₀))) = F (Φ (h * h₀)) := fun h => by
      have e1 : ActionCoordinates.act (ι h)⁻¹ x₀ = x₀ := by
        conv_lhs => rw [← (hι.2.2 h).1, ← act_mul, inv_mul_cancel, act_one]
      rw [_root_.mul_inv_rev, act_mul, e1, mul_assoc, ← hh₀, hπι]
    simp only [e]
    refine ⟨hF.comp (hΦ.measurable.comp (measurable_mul_const h₀)), ?_⟩
    rw [lintegral_mul_right_eq_self (fun h => F (Φ h)) h₀]
    simp only [hFΦ]
    rw [lintegral_indicator_const hK.isClosed.measurableSet, ENNReal.inv_mul_cancel hpos hfin]

end GlobalTheory.StabiliserCutoff
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitarySignatureStabiliserCosetCutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 → ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q), ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} → ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧ ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  atlas_forward_decl GlobalTheory.StabiliserCutoff.exists_cutoff
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealQuotProd

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_mul_inv {a : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (ha : ActionCoordinates.act a x = x) (g : UpqT P Q) :
    ActionCoordinates.act (a * g)⁻¹ x = ActionCoordinates.act g⁻¹ x := by
  have : ActionCoordinates.act a⁻¹ x = x := by
    conv_lhs => rw [← ha]
    rw [← act_mul, inv_mul_cancel, act_one]
  rw [_root_.mul_inv_rev, act_mul, this]

theorem measurable_act_inv (x : ActionCoordinates.Wsp P Q) :
    Measurable fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  exact ((GlobalTheory.UpqTopology.continuous_mat.comp continuous_inv).matrix_mulVec
    continuous_const).measurable

theorem sigmaFinite_cd (c : CDHaar) (P Q : ℕ) : SigmaFinite (c.cd P Q) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI : (c.cd P Q).IsHaarMeasure := c.haar P Q
  infer_instance

theorem one_place (H : ActionCoordinates.QuotientMeasure) (c : CDHaar) {β : ℝ} (hβ : β = 1 ∨ β = -1)
    {x : ActionCoordinates.Wsp P Q} (hx : ActionCoordinates.qf x = β) {k : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q}
    {ι : UpqT P' Q' → UpqT P Q} (hk : ActionCoordinates.IsPerpFrame x k ι) {u : UpqT P Q → ℝ≥0∞}
    (hu : Measurable u) (hu' : ∀ g, Measurable (fun h => u (ι h * g)) ∧
      ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1)
    {fib : ℝ → Measure (ActionCoordinates.Wsp P Q)} (hfib : ActionCoordinates.IsDxDq β fib)
    {φ : ActionCoordinates.Wsp P Q → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ (ActionCoordinates.act g⁻¹ x) * u g ∂(c.cd P Q) =
      (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ y ∂(fib β) := by
  classical
  obtain ⟨h1, -, h3⟩ := H P Q β hβ x hx
  choose! s hs using h1
  have hae : ∀ᵐ y ∂(fib β), ActionCoordinates.qf y = β := by
    obtain ⟨U, B, -, -, -, hF⟩ := hfib
    have h1 : ∀ᵐ y ∂(fib β), y ∈ ActionCoordinates.qf ⁻¹' {id β} ∩ U := hF.1 β
    filter_upwards [h1] with y hy using hy.1
  rw [(h3 P' Q' k ι hk).2 c fib hfib s hs (fun g => φ (ActionCoordinates.act g⁻¹ x) * u g)
    ((hφ.comp (measurable_act_inv x)).mul hu),
    Measure.restrict_eq_self_of_ae_mem (s := {y | ActionCoordinates.qf y = β}) hae]
  congr 1
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  have e : ∀ h, φ (ActionCoordinates.act (ι h * s y)⁻¹ x) = φ y := fun h => by
    rw [act_mul_inv (hk.2.2 h).1, hs y hy]
  simp only [e]
  rw [lintegral_const_mul _ (hu' _).1, (hu' _).2, mul_one]

theorem quot_integral_prod : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  intro H c T _ P Q P' Q' β hβ x hx k ι hk u hu j hj ν hν fib hfib φ hφ
  haveI := sigmaFinite_cd c P Q
  haveI := sigmaFinite_cd c P' Q'
  let f : T → UpqT P Q → ℝ≥0∞ := fun ρ g => φ ρ (ActionCoordinates.act g⁻¹ (x ρ)) * u ρ g
  have hf : ∀ ρ, Measurable (f ρ) := fun ρ =>
    ((hφ ρ).comp (measurable_act_inv (x ρ))).mul (hu ρ).1
  have key := hν (fun g => ∏ ρ, f ρ (g ρ))
    (Finset.measurable_prod _ fun ρ _ => (hf ρ).comp (measurable_pi_apply ρ))
  rw [GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf] at key
  rw [← Finset.prod_congr rfl fun ρ _ =>
    one_place H c hβ (hx ρ) (hk ρ) (hu ρ).1 (hu ρ).2 hfib (hφ ρ)]
  refine Eq.trans (lintegral_congr fun s => ?_) key.symm
  have e : ∀ h : T → UpqT P' Q', ∏ ρ, f ρ ((j h * s.out) ρ) =
      ∏ ρ, (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ)) ρ (h ρ) :=
    fun h => Finset.prod_congr rfl fun ρ _ => by
      simp only [f, Pi.mul_apply, hj]
      rw [act_mul_inv ((hk ρ).2.2 _).1]
  rw [lintegral_congr e, GlobalTheory.SnMass.Push.lintegral_fintype_prod
    (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ))
    (fun ρ => (((hu ρ).2 _).1).const_mul _)]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [lintegral_const_mul _ ((hu ρ).2 _).1, ((hu ρ).2 _).2, mul_one]

end GlobalTheory.RealQuotProd
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientIntegral_prod_over_places : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  atlas_forward_decl GlobalTheory.RealQuotProd.quot_integral_prod
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.FibrePositive

theorem act_mul {P Q : ℕ} (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  have : UpqT.mat (g * h) = UpqT.mat g * UpqT.mat h := rfl
  simp only [ActionCoordinates.act, this, Matrix.mulVec_mulVec]

theorem act_one {P Q : ℕ} (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := by
  have : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  simp only [ActionCoordinates.act, this, Matrix.one_mulVec]

theorem act_inv_of_fix {P Q : ℕ} {g : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (h : ActionCoordinates.act g x = x) :
    ActionCoordinates.act g⁻¹ x = x := by
  conv_lhs => rw [← h]
  rw [← act_mul, inv_mul_cancel, act_one]

theorem fibre_lintegral_ne_zero : ActionCoordinates.QuotientMeasure → CDHaar → ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x₀ = β → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : ActionCoordinates.Wsp P Q → ℝ, Continuous φ → 0 < φ x₀ → ∫⁻ y, ENNReal.ofReal (φ y) ∂(fib β) ≠ 0 := by
  intro hQ c P Q β hβ x₀ hx₀ fib hfib φ hφ hpos h0
  obtain ⟨h1, ⟨P', Q', j, ι, -, -, hfr⟩, h3⟩ := hQ P Q β hβ x₀ hx₀
  obtain ⟨htop, -, -, -, hbor, hcl⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  classical
  choose s0 hs0 using h1
  let s : ActionCoordinates.Wsp P Q → UpqT P Q := fun y => if h : ActionCoordinates.qf y = β then s0 y h else 1
  have hs : ∀ y, ActionCoordinates.qf y = β → ActionCoordinates.act (s y)⁻¹ x₀ = y := by
    intro y hy
    simp only [s, dif_pos hy]
    exact hs0 y hy
  have hc : Continuous fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x₀ :=
    (hcl.continuous.comp continuous_inv).matrix_mulVec continuous_const
  have hfc : Continuous fun g : UpqT P Q => ENNReal.ofReal (φ (ActionCoordinates.act g⁻¹ x₀)) :=
    ENNReal.continuous_ofReal.comp (hφ.comp hc)
  have key := (h3 P' Q' j ι hfr).2 c fib hfib s hs _ hfc.measurable
  have hφm : Measurable fun y => ENNReal.ofReal (φ y) :=
    (ENNReal.continuous_ofReal.comp hφ).measurable
  have hae := (lintegral_eq_zero_iff hφm).1 h0
  have hqm : MeasurableSet {y : ActionCoordinates.Wsp P Q | ActionCoordinates.qf y = β} := by
    have : Continuous (ActionCoordinates.qf : ActionCoordinates.Wsp P Q → ℝ) := by
      unfold ActionCoordinates.qf ActionCoordinates.herm
      fun_prop
    exact (isClosed_eq this continuous_const).measurableSet
  have hR : ∫⁻ y in {y | ActionCoordinates.qf y = β}, (∫⁻ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀))
      ∂(c.cd P' Q')) ∂(fib β) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hqm] with y hy hq
    have : ∀ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀)) = 0 := by
      intro g'
      rw [_root_.mul_inv_rev, act_mul, act_inv_of_fix (hfr.2.2 g').1, hs y hq]
      exact hy
    simp only [this, lintegral_zero, Pi.zero_apply]
  rw [hR, mul_zero] at key
  have := c.haar P Q
  have hz := (hfc.ae_eq_iff_eq (c.cd P Q) continuous_const).1 ((lintegral_eq_zero_iff hfc.measurable).1 key)
  have h1 : ENNReal.ofReal (φ (ActionCoordinates.act (1 : UpqT P Q)⁻¹ x₀)) = 0 := congrFun hz 1
  rw [inv_one, act_one, ENNReal.ofReal_eq_zero] at h1
  linarith

end GlobalTheory.FibrePositive
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianNormFibre_lintegral_ne_zero_of_pos : ActionCoordinates.QuotientMeasure → CDHaar → ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x₀ = β → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : ActionCoordinates.Wsp P Q → ℝ, Continuous φ → 0 < φ x₀ → ∫⁻ y, ENNReal.ofReal (φ y) ∂(fib β) ≠ 0 := by
  atlas_forward_decl GlobalTheory.FibrePositive.fibre_lintegral_ne_zero
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.VolRatioUnfold

section Arch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hR_ratTup (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (y i)) = inclR R (hE σ J x y) := by
  simp [hR, hE, Formalism.UG.hform, JR, sigR, inclR, map_sum, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.tmul_sum]

theorem exists_bump {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {x : V}
    (hx : x ≠ 0) : ∃ φ : V → ℝ, (Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ {y | y ≠ 0} ∧ ∀ y, 0 ≤ φ y) ∧
      0 < φ x := by
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := 0) (s := {y : V | y ≠ 0})
    (isOpen_ne.mem_nhds hx)
  exact ⟨f, ⟨h3.continuous, h2, h1, fun y => (h4 ⟨y, rfl⟩).1⟩, by rw [h5]; exact one_pos⟩

theorem arch (hR3 : ActionCoordinates.RealPlaceMeasures) (c : CDHaar) (hσ : IsCMExt F E σ) {T : Type} [Fintype T]
    {τ : T → (E →+* ℂ)} {θ : T → (Ainf F ⊗[F] E →+* ℂ)}
    (hτ : Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ))
    {M P Q P' Q' : ℕ} (hM : P + Q = M) (hM' : P' + Q' + 1 = P + Q) {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ}
    (hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) (x : Fin M → E) (β : F) (hβ : β = 1 ∨ β = -1)
    (hx : hE σ J x x = algebraMap F E β) (ψ : AddChar (AF F) ℂ) (hψ : ∀ a, psiInf F ψ a = LocalAdditiveCharacterDual.stdInf F a) :
    ∃ (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (a : ℝ≥0∞), Measurable Φi ∧ a ≠ 0 ∧ a ≠ ⊤ ∧
      (∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
          (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)),
        SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
        SelfDual νi (fun s t => psiInf F ψ (s * t)) →
        IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi →
        ∫⁻ X, Φi X ∂(fi (algebraMap F (Ainf F) β)) = a) ∧
      ∀ (C : T → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ)
        (j : (T → UpqT P' Q') →* (T → UpqT P Q)) (o : (T → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E))
        (ν : Measure (LatticeTensorUnfolding.RCosets j)),
        (∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
          ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ (A ρ *ᵥ fun i => τ ρ (x i)) = 0) →
        (∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
          UpqT.mat (j b ρ) *ᵥ (A ρ *ᵥ fun i => τ ρ (x i)) = A ρ *ᵥ fun i => τ ρ (x i)) →
        (∀ g ρ, (A ρ *ᵥ fun i => θ ρ (o g 0 i)) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x i))) →
        LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν →
        ∫⁻ s : LatticeTensorUnfolding.RCosets j, Φi (o s.out) ∂ν = (ActionCoordinates.cM M)⁻¹ ^ Fintype.card T * a := by
  classical
  obtain ⟨hSD, -, hQ⟩ := hR3
  obtain ⟨r, hr1, hr2, hrθ, hrs, hrn⟩ := GlobalTheory.T.exists_realAdele_coordinates_cmType F E σ hσ T τ θ hτ hθ
  obtain ⟨e, he, heh⟩ := GlobalTheory.T.exists_realAdelicHermitian_signature_coordinates F E σ hσ T τ θ hτ hθ M P Q hM J hJ A hA
  haveI : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := (GlobalTheory.ArchUnitaryTop.top_facts F E σ M 1 J).2.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨fib, hfib⟩ := GlobalTheory.RealPlaceCompare.exists_isDxDq P Q

  obtain ⟨b, hb1, hb⟩ : ∃ b : ℝ, (b = 1 ∨ b = -1) ∧ r (algebraMap F (Ainf F) β) = fun _ => b := by
    rcases hβ with rfl | rfl
    · exact ⟨1, Or.inl rfl, by rw [map_one, map_one]; rfl⟩
    · exact ⟨-1, Or.inr rfl, by rw [map_neg, map_one, map_neg, map_one]; rfl⟩
  have hb0 : b ≠ 0 := by rcases hb1 with rfl | rfl <;> norm_num
  have htr : ∀ z ρ, r (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) ρ = 2 * (θ ρ z).re := by
    intro z ρ
    have h := hrθ (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) ρ
    have h0 : Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z ⊗ₜ[F] (1 : E) = z + sigR (Ainf F) σ z :=
      GlobalTheory.SelfDualLatticeCompare.trace_tensor (Ainf F) hσ z
    rw [h0, map_add, GlobalTheory.Mem.VolExists.infEmb_sigR hσ (hθ ρ), Complex.add_conj] at h
    exact_mod_cast h
  have hhalf : ∀ ρ, r (algebraMap F (Ainf F) (1 / 2)) ρ = 1 / 2 := by
    intro ρ
    have h2 : algebraMap F (Ainf F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap F (Ainf F)) 2, ← map_mul]; norm_num
    have h3 := congrFun (congrArg r h2) ρ
    rw [map_mul, map_one, map_ofNat] at h3
    simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.one_apply] at h3
    linarith
  have hq : ∀ X ρ, ActionCoordinates.qf (e X ρ) = r (qR (Ainf F) σ J (X 0)) ρ := by
    intro X ρ
    rw [qR, map_mul, Pi.mul_apply, hhalf, htr, heh, ActionCoordinates.qf]; ring
  set xr : T → ActionCoordinates.Wsp P Q := fun ρ => A ρ *ᵥ fun i => τ ρ (x i) with hxr
  have hxe : ∀ ρ, e (ratTup (Ainf F) fun _ => x) ρ = xr ρ := by
    intro ρ
    rw [he]
    congr 1
    funext i
    exact (hθ ρ).1 (x i)
  have hxq : ∀ ρ, ActionCoordinates.qf (xr ρ) = b := by
    intro ρ
    have h1 := heh (ratTup (Ainf F) fun _ => x) (ratTup (Ainf F) fun _ => x) ρ
    rw [hxe, ActionCoordinates.herm_self] at h1
    have h2 : hR (Ainf F) σ J (ratTup (F := F) (Ainf F) (fun _ : Fin 1 => x) 0) (ratTup (F := F) (Ainf F) (fun _ : Fin 1 => x) 0) =
        algebraMap F (Ainf F) β ⊗ₜ[F] (1 : E) := by
      refine (hR_ratTup (Ainf F) J x x).trans ?_
      rw [hx, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rfl
    rw [h2, ← hrθ, hb] at h1
    exact_mod_cast h1.symm
  have hx0 : ∀ ρ, xr ρ ≠ 0 := by
    intro ρ h
    have := hxq ρ
    rw [h, GlobalTheory.RealPlaceCompare.qf_eq, GlobalTheory.RealPlaceCompare.qf_zero] at this
    exact hb0 this.symm
  choose φ hφ hφx using fun ρ => exists_bump (hx0 ρ)
  have hφm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    (hφ ρ).1.measurable.ennreal_ofReal
  have hΦm : Measurable fun z : T → ActionCoordinates.Wsp P Q => ∏ ρ, ENNReal.ofReal (φ ρ (z ρ)) :=
    Finset.measurable_prod _ fun ρ _ => (hφm ρ).comp (measurable_pi_apply ρ)
  have hem : Measurable e := e.continuous.measurable
  have hfb := GlobalTheory.RealPlaceCompare.isDxDq_local hfib b
  refine ⟨fun X => ∏ ρ, ENNReal.ofReal (φ ρ (e X ρ)), ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib b),
    hΦm.comp hem, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun ρ _ =>
      GlobalTheory.T.hermitianNormFibre_lintegral_ne_zero_of_pos hQ c P Q b hb1 (xr ρ) (hxq ρ) fib hfb (φ ρ) (hφ ρ).1 (hφx ρ)
  · refine ENNReal.prod_ne_top fun ρ _ => ?_
    have hi := (hfib.2.2 (φ ρ) (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 b (Set.mem_univ _)
    exact hi.lintegral_lt_top.ne
  · intro μi νi fi hμ hν hfi
    have hdx : (ActionCoordinates.dx P Q).IsAddHaarMeasure := GlobalTheory.RealPlaceCompare.isAddHaar_dx P Q
    have h1 : μi.map e = Measure.pi fun _ : T => ActionCoordinates.dx P Q := by
      refine GlobalTheory.T.selfDual_sumPairing_map_eq_pi T _ _ e (-1) ActionCoordinates.bil _ hdx
        (((hSD (-1) (Or.inr rfl)).1 P Q _ hdx).2 rfl) μi _ (fun X Y => ?_) hμ
      rw [hψ, hrs]
      congr 4
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [BR, Fin.sum_univ_one, htr, heh, GlobalTheory.RealPlaceCompare.bil_eq, GlobalTheory.RealPlaceCompare.herm_eq,
        ← GlobalTheory.RealPlaceCompare.herm_star (e X ρ)]
      simp
    let r' : Ainf F ≃ₜ+ (T → ℝ) := { r.toAddEquiv with continuous_toFun := hr1, continuous_invFun := hr2 }
    have h2 : νi.map r' = volume := by
      refine GlobalTheory.T.selfDual_sumPairing_map_eq_pi T _ _ r' (-1) (fun t s : ℝ => t * s) volume inferInstance
        (((hSD (-1) (Or.inr rfl)).2 _ inferInstance).2 rfl) νi _ (fun s t => ?_) hν
      rw [hψ, hrs, map_mul]
      rfl
    have h3 := GlobalTheory.T.isFibreMeasureFamily_map_homeomorph _ _ _ _ e.toHomeomorph r'.toHomeomorph μi νi _
      (fun (z : T → ActionCoordinates.Wsp P Q) ρ => ActionCoordinates.qf (z ρ)) _ fi (fun X => funext fun ρ => hq X ρ) hfi
    have h1' : μi.map e.toHomeomorph = Measure.pi fun _ : T => ActionCoordinates.dx P Q := h1
    have h2' : νi.map r'.toHomeomorph = volume := h2
    rw [h1', h2'] at h3
    have hB : r'.toHomeomorph '' {c | ∀ w, c w ≠ 0} = {t | ∀ ρ, t ρ ≠ 0} := by
      ext t
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (hrn a).1 ha
      · intro ht
        refine ⟨r.symm t, (hrn _).2 ?_, r.apply_symm_apply t⟩
        rw [r.apply_symm_apply]; exact ht
    rw [hB] at h3
    have hBo : IsOpen {t : T → ℝ | ∀ ρ, t ρ ≠ 0} := by
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun ρ => isOpen_ne.preimage (continuous_apply ρ)
    have hfib' : IsFibreFamily (ActionCoordinates.dx P Q) ActionCoordinates.qf id {x | x ≠ 0} (volume : Measure ℝ) Set.univ fib := by
      rw [GlobalTheory.RealPlaceCompare.qf_eq]; exact hfib
    have h4 := GlobalTheory.T.fibreIntegral_pi_prod_eq_prod_fibreIntegral T _ (ActionCoordinates.dx P Q) ActionCoordinates.qf
      (by rw [GlobalTheory.RealPlaceCompare.qf_eq]; exact GlobalTheory.RealPlaceCompare.continuous_qf) _ isOpen_ne fib hfib' _ hBo _ h3
      (fun _ => b) (fun _ => hb0) φ hφ
    have h5 : r'.toHomeomorph.symm (fun _ => b) = algebraMap F (Ainf F) β := by
      rw [← hb]; exact r.symm_apply_apply _
    rw [h5] at h4
    exact (lintegral_map hΦm hem).symm.trans h4
  · intro C j o ν hC hj ho hν
    have hne : ∀ ρ, star (xr ρ) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ xr ρ ≠ 0 := by
      intro ρ
      rw [GlobalTheory.QuadricSection.form_self, ← GlobalTheory.RealPlaceCompare.qf_eq, hxq]
      exact_mod_cast hb0
    let ι : T → UpqT P' Q' → UpqT P Q := fun ρ h => j (Pi.mulSingle ρ h) ρ
    have hι : ∀ ρ h, UpqT.mat (ι ρ h) * C ρ = C ρ * UpqT.mat h ∧ UpqT.mat (ι ρ h) *ᵥ xr ρ = xr ρ := by
      intro ρ h
      have := hj (Pi.mulSingle ρ h) ρ
      rwa [Pi.mulSingle_eq_same] at this
    have hjι : ∀ g ρ, j g ρ = ι ρ (g ρ) := fun g ρ =>
      GlobalTheory.UnfoldingCompare.eq_of_frame hM' (hne ρ) (hC ρ).1 (hC ρ).2
        ((hj g ρ).1.trans (hι ρ _).1.symm) ((hj g ρ).2.trans (hι ρ _).2.symm)
    have hfr : ∀ ρ, ActionCoordinates.IsPerpFrame (xr ρ) (Matrix.toLin' (C ρ)) (ι ρ) := fun ρ =>
      GlobalTheory.T.isOrthogonalComplementUnitaryFrame_of_matrix P Q P' Q' hM' (xr ρ) (by rw [hxq]; exact hb0) (C ρ) (hC ρ).1 (hC ρ).2 (ι ρ) (hι ρ)
    choose u hu using fun ρ => GlobalTheory.T.exists_unitarySignatureStabiliserCosetCutoff c P Q P' Q' (xr ρ) (by rw [hxq]; exact hb0) _ (ι ρ) (hfr ρ)
      ((hQ P Q b hb1 (xr ρ) (hxq ρ)).2.2 P' Q' _ _ (hfr ρ)).1
    have h := GlobalTheory.T.unitaryQuotientIntegral_prod_over_places hQ c T P Q P' Q' b hb1 xr hxq _ ι hfr u hu j hjι ν hν fib hfb _ hφm
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hM] at h
    rw [← h]
    refine lintegral_congr fun s => Finset.prod_congr rfl fun ρ _ => ?_
    rw [he, ho]
    rfl

end Arch

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem local_value (hL5 : PlaceSplittingTypes.SelfDualLatticeDensity) (hσ : IsCMExt F E σ) {M : ℕ} (hM : 1 ≤ M)
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (v : HeightOneSpectrum (𝓞 F))
    (hv : SelfDualUnramifiedPlaces.UnramifiedPlace F E v) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (hi : LocalAdditiveCharacterDual.IndexFinite F ψ v)
    (L : Submodule (SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) (hL : SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L)
    (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v))
    (hμ : SelfDual μ fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) (hν : SelfDual ν fun s t => psiV F ψ v (s * t))
    (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hfib : IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib)
    (β : Fv F v) (hβ : Valued.v β = 1) :
    fib β {X | X 0 ∈ L} = ENNReal.ofReal (LocalAdditiveCharacterDual.locDens F E ψ M v) := by
  obtain ⟨χ, hχ, hχψ⟩ := GlobalTheory.T.exists_localComponent_adelicAddChar F ψ hψ v hi
  have hχ' : (χ : Fv F v → ℂ) = psiV F ψ v := funext hχψ
  obtain ⟨η, hη⟩ := GlobalTheory.LocalDensityCompare.exists_eta F E v
  have hEta := (GlobalTheory.LocalDensityCompare.isEtaAt_iff F E v hσ.2.2.1 η).2 ⟨hv, hη⟩
  obtain ⟨⟨c, hc⟩, h⟩ := hL5 F E σ hσ M J hM hJ v η hEta χ hχ
  have h1 := ((h c hc L ((GlobalTheory.LocalDensityCompare.isSelfDualLattice_iff v σ J L).1 hL) μ
    (by rw [SdW, hχ']; exact hμ) ν (by rw [SdR, hχ']; exact hν)).2.2 β hβ).1 Set.univ {c | c ≠ 0} fib
    (Set.subset_univ _) subset_rfl hfib
  refine h1.1.trans (congrArg _ ?_)
  have h2 := GlobalTheory.T.adicIntegersCharacterDualIndex_eq_residue_card_zpow F ψ v c (by simpa only [PlaceSplittingTypes.IsDualExp, hχψ] using hc)
  rw [LocalAdditiveCharacterDual.locDens, h2, PlaceSplittingTypes.densityValue, PlaceSplittingTypes.dualIndex, LocalAdditiveCharacterDual.eulerInv, hη]
  rfl

theorem tprod_ofReal {ι : Type} {f : ι → ℝ} (h0 : ∀ i, 0 ≤ f i) (hf : Multipliable f) :
    ∏' i, ENNReal.ofReal (f i) = ENNReal.ofReal (∏' i, f i) := by
  refine HasProd.tprod_eq ?_
  have h := (ENNReal.continuous_ofReal.tendsto _).comp hf.hasProd
  refine h.congr fun s => ?_
  exact ENNReal.ofReal_prod_of_nonneg fun i _ => h0 i

end Fin

theorem ratio_of_eq {V V' c p : ℝ} (hV : 0 < V) (hV' : 0 < V') (hc : 0 < c) (hp : 0 < p) {f : ℕ} {a : ℝ≥0∞}
    (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (h : (ENNReal.ofReal V)⁻¹ * (ENNReal.ofReal V' * ((ENNReal.ofReal c)⁻¹ ^ f * a)) = a * ENNReal.ofReal p) :
    V' / V = c ^ f * p := by
  have h1 := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal hV.le,
    ENNReal.toReal_ofReal hV'.le, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal hp.le] at h1
  have ha0 : 0 < a.toReal := ENNReal.toReal_pos ha ha'
  have hcf : 0 < c ^ f := pow_pos hc f
  rw [inv_pow] at h1
  field_simp at h1 ⊢
  linarith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hE_coords (D : D7) (W : HSpace D.host.E) (x y : W.V) :
    hE D.sp.cm.sig W.gram (fun i => W.frame.repr x i) (fun i => W.frame.repr y i) = W.hT x y := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]; rfl

theorem tsum_coords (D : D7) (W : HSpace D.host.E) (s : Bool) (β : D.host.F)
    (hβE : algebraMap D.host.F D.host.E β = if s then 1 else -1) (G : (Fin 1 → Fin W.rank → D.host.E) → ℝ≥0∞) :
    ∑' y : {y : Fin 1 → Fin W.rank → D.host.E | y 0 ≠ 0 ∧
        hE D.sp.cm.sig W.gram (y 0) (y 0) = algebraMap D.host.F D.host.E β}, G y =
      ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)}, G (LatticeTensorUnfolding.coords W x'.1) := by
  let eq : {x' : W.V // W.hT x' x' = (if s then 1 else -1)} ≃
      {y : Fin 1 → Fin W.rank → D.host.E | y 0 ≠ 0 ∧
        hE D.sp.cm.sig W.gram (y 0) (y 0) = algebraMap D.host.F D.host.E β} :=
    Equiv.subtypeEquiv (W.frame.equivFun.toEquiv.trans (Equiv.funUnique (Fin 1) _).symm) fun y => by
      have e1 : hE D.sp.cm.sig W.gram (W.frame.equivFun y) (W.frame.equivFun y) = W.hT y y := hE_coords D W y y
      change _ ↔ W.frame.equivFun y ≠ 0 ∧ hE D.sp.cm.sig W.gram (W.frame.equivFun y) (W.frame.equivFun y) = _
      rw [e1, hβE]
      refine ⟨fun h => ⟨fun h0 => ?_, h⟩, fun h => h.2⟩
      rw [LinearEquiv.map_eq_zero_iff] at h0
      rw [h0] at h
      cases s <;> simp at h
  rw [← eq.tsum_eq]; rfl

set_option maxHeartbeats 1000000 in

theorem ratio_of_setting (hL5 : PlaceSplittingTypes.SelfDualLatticeDensity) (hR3 : ActionCoordinates.RealPlaceMeasures)
    (hEu : LocalAdditiveCharacterDual.EulerProductOfDensities)
    (hSW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J)
    (D : D7) (hU : LatticeTensorUnfolding.Unfolding D) (hV : VolTie D) (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool)
    (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V) (hS : LatticeTensorUnfolding.HidaSetting W W' P Q P' Q' s x ι)
    (hL : ∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0) :
    D.vol W' / D.vol W =
      ((2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ)) ^ D.R.f *
        ((2 * D.host.v) ^ D.R.f) ^ ((1 : ℝ) / 2 - W.rank) / Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank := by
  classical
  have hun := hU W W' P Q P' Q' s x ι hS hL
  obtain ⟨hW, hsig, hr, hstep, hx, -, -, -, hW', hsig'⟩ := hS
  have hσ := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm W
  obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hM : P + Q = W.rank := by simpa [hsig τ₀] using sig_sum W hW τ₀
  have hM' : P' + Q' + 1 = P + Q := by cases s <;> simp at hstep <;> omega
  obtain ⟨⟨μ, hμ⟩, h1⟩ := hV W P Q hW hsig
  obtain ⟨⟨𝓕, h𝓕⟩, h2⟩ := h1 μ hμ
  have hvol := h2 𝓕 h𝓕
  obtain ⟨⟨μ', hμ'⟩, h1'⟩ := hV W' P' Q' hW' hsig'
  obtain ⟨⟨𝓕', h𝓕'⟩, h2'⟩ := h1' μ' hμ'
  have hvol' := h2' 𝓕' h𝓕'
  obtain ⟨⟨θ, hθ⟩, h3⟩ := hμ.2
  obtain ⟨A, hA⟩ := (h3 θ hθ).1
  obtain ⟨⟨⟨ψ, hψ, hψi⟩, -⟩, -, -, hEP⟩ := hEu D.host.F D.host.E D.sp.cm.sig hσ D.sp.cm.cmUnram
  obtain ⟨hfin, hpos, -, hmul, hppos, hval⟩ := ((hEP W.rank (by omega)).2 ψ hψ).2 1 (fun a => by simp [hψi])
  set β : D.host.F := if s then 1 else -1 with hβ
  have hβ1 : β = 1 ∨ β = -1 := by cases s <;> simp [hβ]
  have hβE : algebraMap D.host.F D.host.E β = if s then 1 else -1 := by cases s <;> simp [hβ]
  have hβ0 : β ≠ 0 := by rcases hβ1 with h | h <;> simp [h]
  obtain ⟨Φi, a, hΦi, ha0, hat, hfibre, hquot⟩ := arch hR3 D.cd hσ (GlobalTheory.VolRatioCheck.place_bijective D) hθ hM hM' hJ hA
    (fun i => W.frame.repr x i) β hβ1 (by rw [hE_coords, hx, hβE]) ψ hψi
  obtain ⟨I, hI, hunf⟩ := hun μ μ' hμ hμ' 𝓕 𝓕' h𝓕 h𝓕' (by rw [hvol]; exact ENNReal.ofReal_lt_top)
    (by rw [hvol']; exact ENNReal.ofReal_lt_top) Φi hΦi
  have hIa : I = (ActionCoordinates.cM W.rank)⁻¹ ^ Fintype.card D.what₂.Tau * a := by
    obtain ⟨⟨C, hC⟩, h4⟩ := (hI.2 θ hθ).2 A hA
    obtain ⟨⟨j, hj⟩, h5⟩ := h4 C hC
    obtain ⟨⟨o, ho⟩, h6⟩ := h5 j hj
    obtain ⟨⟨ν, hν⟩, h7⟩ := h6 o ho
    rw [← h7 ν hν]
    exact hquot C j o ν hC hj ho hν
  have hcard : Fintype.card D.what₂.Tau = D.R.f := by
    rw [Fintype.card_of_bijective (GlobalTheory.VolRatioCheck.place_bijective D)]; exact fDeg_host D

  have hlat := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat W
  have hsd := (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ.2 hlat).1
    (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm W)
  haveI : FiniteDimensional D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)
  let b := Module.finBasis D.host.F D.host.E
  let Φv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin 1 → Fin W.rank → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ :=
    fun v => {X | X 0 ∈ GlobalTheory.AdelicU.latLoc D.host.F (GlobalTheory.AdelicU.frameLat W) v}.indicator 1
  let Φf : (Fin 1 → Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
    {X | X 0 ∈ latHat D.host.F D.host.E (GlobalTheory.AdelicU.frameLat W : Set (Fin W.rank → D.host.E))}.indicator 1
  have hpure : IsPureFin b Φf Φv :=
    ⟨GlobalTheory.T.isSchwartzBruhat_indicator_localLatticeCompletion _ _ _ _ hlat, (GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice _ _ _ _ b _ hlat).mono fun v hv => by simp only [Φv, hv],
      GlobalTheory.T.indicator_completedLattice_eq_finprod_local _ _ _ _ hlat⟩
  have hsw := hSW _ _ _ hσ _ _ hJ hr β hβ0 _ b (LatticeTensorUnfolding.latTensor (L0c D W) Φi) Φi Φf Φv hΦi hpure
    (fun v Y => by by_cases h : Y 0 ∈ GlobalTheory.AdelicU.latLoc D.host.F (GlobalTheory.AdelicU.frameLat W) v <;> simp [Φv, h])
    (fun X => by
      rw [LatticeTensorUnfolding.latTensor, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice, mul_comm]
      by_cases h : projFin X 0 ∈ latHat D.host.F D.host.E (GlobalTheory.AdelicU.frameLat W : Set (Fin W.rank → D.host.E)) <;>
        simp [Φf, h])
  obtain ⟨⟨μi, hμi⟩, ⟨νi, hνi⟩, ⟨μv, hμv⟩, ⟨νv, hνv⟩, h8⟩ := (((hsw.2 ψ hψ).2 μ hμ.1).2 𝓕 h𝓕)
  obtain ⟨⟨fi, hfi⟩, ⟨fv, hfv⟩, h9⟩ := h8 μi νi μv νv hμi hνi hμv hνv
  have hmean := (h9 fi fv hfi hfv).2
  have hloc : ∀ v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap D.host.F (Fv D.host.F v) β)) =
      ENNReal.ofReal (LocalAdditiveCharacterDual.locDens D.host.F D.host.E ψ W.rank v) := by
    intro v
    obtain ⟨Lv, hLv, hmem⟩ := GlobalTheory.T.exists_selfDualLattice_completion_maxOrder _ _ _ _ _ _ hJ hlat hsd v
    have hop := (GlobalTheory.LocalDensityCompare.lattice_compact_open v D.sp.cm.sig hσ Lv hLv.1 hLv.2.1).2
    have hlc := GlobalTheory.LocalDensityCompare.lcs (F := D.host.F) (E := D.host.E) v
    haveI := hlc.2.1
    haveI : BorelSpace (Fv D.host.F v ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have hms : MeasurableSet {X : Fin 1 → Fin W.rank → Fv D.host.F v ⊗[D.host.F] D.host.E | X 0 ∈ Lv} :=
      hop.measurableSet
    rw [← local_value hL5 hσ (by omega) hJ v
      (fun w _ => GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm w) hψ (hfin v) Lv hLv _ _ (hμv v) (hνv v) _ (hfv v)
      (algebraMap D.host.F (Fv D.host.F v) β) (by rcases hβ1 with h | h <;> simp [h]),
      ← lintegral_indicator_one hms]
    refine lintegral_congr fun X => ?_
    by_cases h : X 0 ∈ Lv
    · have h' := (hmem _).1 h
      simp [Φv, h, h']
    · have h' := mt (hmem _).2 h
      simp [Φv, h, h']
  simp only [hloc] at hmean
  rw [tprod_ofReal (fun v => (hpos v).le) hmul, hfibre μi νi fi hμi hνi hfi, meanL] at hmean
  have hsum := (lintegral_congr fun h => tsum_coords D W s β hβE
    (LatticeTensorUnfolding.atInv D.sp.cm.sig W.gram (LatticeTensorUnfolding.latTensor (L0c D W) Φi) h)).trans hunf
  replace hmean := (congrArg ((μ 𝓕)⁻¹ * ·) hsum).symm.trans hmean
  simp only [hIa, hvol, hvol', hcard, ActionCoordinates.cM] at hmean
  have hc : 0 < (2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ) := by have := Real.pi_pos; positivity
  rw [ratio_of_eq (D.vol_pos W) (D.vol_pos W') hc hppos ha0 hat hmean, mul_div_assoc]
  congr 1
  simpa [LocalAdditiveCharacterDual.absInf, LocalAdditiveCharacterDual.dF, vInv_host, fDeg_host] using hval

theorem volumeRatio_of_unfolding (hL5 : PlaceSplittingTypes.SelfDualLatticeDensity) (hR3 : ActionCoordinates.RealPlaceMeasures)
    (hEu : LocalAdditiveCharacterDual.EulerProductOfDensities) (hInd : ∀ D, IsometryTransportFrames.VolIndep D) (hPerp : ∀ D, SelfDualLatticeComplements.UnitVectorPerp D)
    (hUnf : ∀ D, LatticeTensorUnfolding.Unfolding D)
    (hSW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J) :
    ∀ D : D7, VolTie D → VolumeRatio₂ D := by
  intro D hV W P Q hW hsig hr s hs
  obtain ⟨x, hx, L, W', ι, hL, hxL, ⟨hW', -, hsig'⟩, hiso, hrange, hlat, -⟩ :=
    hPerp D W W.rank P Q ⟨hW, rfl, hsig⟩ hr (if s then 1 else -1) (if s then P - 1 else P) (if s then Q else Q - 1)
      (by cases s <;> simp_all [SelfDualLatticeComplements.Step])
  refine ⟨x, hx, W', ι, hiso, hrange, hW', fun τ => by rw [hsig' τ]; cases s <;> rfl, ?_⟩
  let W₁ := IsometryTransportFrames.withLat W L hL.1 hL.2
  have hvol : D.vol W = D.vol W₁ :=
    (hInd D).2.2 hV W W₁ P Q ⟨hW, hsig⟩ ⟨hW, hsig⟩ (LinearEquiv.refl _ _) fun _ _ => rfl
  rw [hvol]
  refine ratio_of_setting hL5 hR3 hEu hSW D (hUnf D) hV W₁ W' P Q _ _ s x ι
    ⟨hW, hsig, hr, ?_, hx, hxL, hiso, hrange, hW', hsig'⟩ fun y => ?_
  · cases s <;> simp at hs ⊢ <;> omega
  · have hinj := SelfDualLatticeComplements.injective_of_isIsomEmb hiso
    constructor
    · intro hy
      have : ι y ∈ W'.L0.map (ι.restrictScalars (𝓞 D.host.E)) := ⟨y, hy, rfl⟩
      rw [hlat] at this
      exact this.1
    · intro hy
      have hp : ι y ∈ SelfDualLatticeComplements.perp W x := by rw [← hrange]; exact ⟨y, rfl⟩
      have : ι y ∈ W'.L0.map (ι.restrictScalars (𝓞 D.host.E)) := by rw [hlat]; exact ⟨hy, hp⟩
      obtain ⟨z, hz, e⟩ := this
      rwa [← hinj e]

end GlobalTheory.VolRatioUnfold
end
end
