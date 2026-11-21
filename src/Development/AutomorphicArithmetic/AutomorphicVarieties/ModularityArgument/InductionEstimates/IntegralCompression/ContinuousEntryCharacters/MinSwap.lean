import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ContinuousEntCSymm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section

open PositivityTheory.Rg.Tf.Geo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem gal_infEmb (σ : E ≃ₐ[F] E) (n : ℕ) (a : archGroup E n) :
    Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a) =
      infEmb E n (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) := by
  apply (AdelicGLn.prodEquiv E n).injective
  rw [prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · have h1 : UpperTheory.ConvolutionTheory.T4.pI E n (infEmb E n a) = (archEquiv E n).symm a := congrArg Prod.fst (prodEquiv_infEmb a)
    rw [← UpperTheory.ConvolutionTheory.K.galAdEq F E σ, ← h1]
    exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).1 _
  · have h2 : (AdelicGLn.prodEquiv E n (infEmb E n a)).2 = 1 := congrArg Prod.snd (prodEquiv_infEmb a)
    have h3 : (AdelicGLn.prodEquiv E n
        (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a))).2 =
        mapGL n (Formalism.L2.Host.CT.finMap σ.toRingEquiv) (AdelicGLn.prodEquiv E n (infEmb E n a)).2 :=
      Units.ext (Matrix.ext fun _ _ => rfl)
    rw [h3, h2, map_one]

private theorem compA_shift {σ : E ≃ₐ[F] E} {m : ℕ} (D : InfD σ m) (n : ℕ) (a : archGroup E n) (i : Fin (m + 1)) :
    compA D n i (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) = compA D n (i + 1) a := by
  have e : ∀ j x, compA D n j x = archEquiv F n (D.comp n j ((archEquiv E n).symm x)) := fun _ _ => rfl
  rw [e, e, ContinuousMulEquiv.symm_apply_apply]
  congr 1
  exact Units.ext (Matrix.ext fun p q => D.map_shift _ i)

private theorem single_shift {ι G : Type} [One G] (s i : Fin 2) (u v : ι) (m : G) :
    (Pi.mulSingle (s, u) m : Fin 2 × ι → G) (i + 1, v) = (Pi.mulSingle (s + 1, u) m : Fin 2 × ι → G) (i, v) := by
  have h : i + 1 = s ↔ i = s + 1 := by revert i s; decide
  simp only [Pi.mulSingle_apply, Prod.mk.injEq, h]

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ s u m, θ.e (CE.un (s, u) m) = CE.un (s + 1, u) m := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ s u m
  apply Subtype.ext
  rw [hθ]
  simp only [Co.un, arc1, archimedeanProjection_maximalCompact]
  rw [gal_infEmb]
  congr 1
  apply (CE.Ψ 2).injective
  funext ⟨i, v⟩
  rw [hC, compA_shift, ← hC]
  apply Units.ext
  rw [← CE.Φ_val, ← CE.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  congr 1
  convert single_shift s i u v m
end

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.minSwap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ τ₁ τ₂ : Submodule ℂ (LL μ),
        τ₁.map (θ.U : LL μ →ₗ[ℂ] LL μ) = τ₂ → ∀ s u n q, CE.MinAt μ τ₁ (s, u) n q → CE.MinAt μ τ₂ (s + 1, u) n q := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ τ₁ τ₂ hτ s u n q hmin
  obtain ⟨hnorm, -, hint⟩ := UpperTheory.ConvolutionTheory.Dp.twUnitary E 2 μ θ
  have htw := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw F E σ D CF CE hC μ θ hθ
  let L : LL μ →ₗᵢ[ℂ] LL μ := ⟨(θ.U : LL μ →ₗ[ℂ] LL μ), hnorm⟩
  have hL : ∀ v, L v = θ.U v := fun _ => rfl
  have key : ∀ n' q' v, θ.U (CE.Pi μ (s, u) n' q' v) = CE.Pi μ (s + 1, u) n' q' (θ.U v) := by
    intro n' q' v
    unfold Co.Pi
    rw [← hL, ← L.integral_comp_comm]
    congr 1
    funext m
    rw [map_smul, hL, hint, htw]
  subst hτ
  obtain ⟨⟨v, hv, hne⟩, hz⟩ := hmin
  refine ⟨⟨θ.U v, Submodule.mem_map_of_mem hv, fun h => hne ?_⟩, ?_⟩
  · rw [← key] at h
    rw [← norm_eq_zero, ← hnorm, h, norm_zero]
  · rintro n' q' hn _ ⟨w, hw, rfl⟩
    have := key n' q' w
    rw [hz n' q' hn w hw, map_zero] at this
    exact this.symm
end
