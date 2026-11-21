import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.twCls :
    UpperTheory.ConvolutionTheory.Dp.TwCls := by
  intro K _ _ n μ _ θ φ hφ ψ hψ
  have hmemS : ∀ g, θ.e.symm g ∈ rationalGLOne K n ↔ g ∈ rationalGLOne K n := fun g => by
    have h := θ.mem_gam (θ.e.symm g)
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h.symm
  have hpresS : MeasurePreserving θ.e.symm μ μ :=
    MeasurePreserving.symm θ.e.toHomeomorph.toMeasurableEquiv θ.pres
  obtain ⟨hmk, hT⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (rationalGLOne K n) μ θ.e.symm hmemS hpresS
  let T : RightCosetSpace (rationalGLOne K n) → RightCosetSpace (rationalGLOne K n) :=
    fun y => mk _ (θ.e.symm (Quotient.out y))
  have hTmk : ∀ x, T (mk _ x) = mk _ (θ.e.symm x) := hmk
  have hTc : Continuous T := by
    refine (isOpenQuotientMap_mk (rationalGLOne K n)).isQuotientMap.continuous_iff.2 ?_
    have h : T ∘ mk _ = mk _ ∘ θ.e.symm := funext hTmk
    rw [h]
    exact (continuous_mk _).comp θ.e.symm.continuous
  let Φ := cuspQuot φ.2.1.isLeftInvariant
  let Ψ := cuspQuot ψ.2.1.isLeftInvariant
  have hΦc : Continuous Φ := continuous_cuspQuot _ φ.2.1.continuous
  have hΨc : Continuous Ψ := continuous_cuspQuot _ ψ.2.1.continuous
  have hb := (UpperTheory.ConvolutionTheory.Dp.clsBasic K n μ).2.2.2
  have hout : ∀ (χ : cuspForms K n) (y : RightCosetSpace (rationalGLOne K n)),
      χ.1 ((Quotient.out y : normOneGL K n) : AdelicGLn.AdelicGL K n) =
        cuspQuot χ.2.1.isLeftInvariant y := fun χ y => by
    have h : mk (rationalGLOne K n) (Quotient.out y) = y := Quotient.out_eq y
    conv_rhs => rw [← h]
    rw [cuspQuot_mk]
  have hφa : (clsL μ φ : RightCosetSpace (rationalGLOne K n) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne K n) μ] Φ :=
    (hb φ hφ).trans (Filter.Eventually.of_forall (hout φ))
  have hψa : (clsL μ ψ : RightCosetSpace (rationalGLOne K n) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne K n) μ] Ψ :=
    (hb ψ hψ).trans (Filter.Eventually.of_forall (hout ψ))
  have hU : (θ.U (clsL μ ψ) : RightCosetSpace (rationalGLOne K n) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne K n) μ] Ψ ∘ T :=
    (θ.U_spec _).trans (hT.quasiMeasurePreserving.ae_eq_comp hψa)
  constructor
  · intro h x
    have h1 : Ψ ∘ T =ᵐ[quotientMeasure (rationalGLOne K n) μ] Φ := by
      rw [h] at hU
      exact hU.symm.trans hφa
    have h2 : Ψ ∘ T = Φ := (Continuous.ae_eq_iff_eq _ (hΨc.comp hTc) hΦc).1 h1
    have h3 := congrFun h2 (mk _ (θ.e x))
    simp only [Function.comp_apply, hTmk, ContinuousMulEquiv.symm_apply_apply] at h3
    simpa only [Ψ, Φ, cuspQuot_mk] using h3
  · intro h
    have h2 : Ψ ∘ T = Φ := by
      funext y
      obtain ⟨x, rfl⟩ := mk_surjective _ y
      simp only [Function.comp_apply, hTmk, Ψ, Φ, cuspQuot_mk]
      rw [h, ContinuousMulEquiv.apply_symm_apply]
    rw [h2] at hU
    exact Lp.ext (hU.trans hφa.symm)
end

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem galAd_eq_adm {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (σ : E ≃+* E)
    (s : Ad E ≃+* Ad E) (h : UpperTheory.CBC.IsGalAd σ s) : s.toRingHom = UpperTheory.V.FieldIso.adm σ :=
  (UpperTheory.ConvolutionTheory.K.adUnique E σ s.toRingHom h.1 h.2.1).trans
    (UpperTheory.ConvolutionTheory.K.adUnique E σ (UpperTheory.V.FieldIso.adm σ) (UpperTheory.V.FieldIso.continuous_adm σ)
      (UpperTheory.V.FieldIso.adm_algebraMap σ)).symm

open Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep in
private theorem cinf_real {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (σ : E ≃+* E) (c : ℝ) :
    UpperTheory.V.FieldIso.cinf σ (fun _ => (c : ℂ)) = fun _ => (c : ℂ) := by
  funext u
  change coord _ _ = _
  unfold coord
  split_ifs <;> simp

private theorem map_splitCentre {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (σ : E ≃+* E) (a : ℕ)
    (t : ℝ) : UpperTheory.V.FieldIso.gaMap a σ (GlobalTheory.UnitaryBC.splitCentre E a t) = GlobalTheory.UnitaryBC.splitCentre E a t := by
  unfold GlobalTheory.UnitaryBC.splitCentre
  rw [UpperTheory.V.FieldIso.gaMap_infGL]
  congr 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  change UpperTheory.V.FieldIso.cinf σ (Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j) =
    Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, ← Complex.ofReal_exp]
    exact cinf_real σ _
  · rw [Matrix.diagonal_apply_ne _ h]
    exact map_zero _

theorem UpperTheory.ConvolutionTheory.Dp.galCentral :
    UpperTheory.ConvolutionTheory.Dp.GalCentral := by
  intro E _ _ _ n σ s h
  refine ⟨fun s' h' => RingEquiv.ext fun x => ?_, fun t => ?_⟩
  · have e := (galAd_eq_adm σ s' h').trans (galAd_eq_adm σ s h).symm
    exact congrArg (fun f : Ad E →+* Ad E => f x) e
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Units.ext (Matrix.ext fun i => i.elim0)
    · have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have ht : t = ⟨Real.exp (n * Module.finrank ℚ E * (Real.log t / (n * Module.finrank ℚ E))), Real.exp_pos _⟩ := by
        refine Subtype.ext ?_
        change (t : ℝ) = Real.exp _
        rw [mul_div_cancel₀ _ (mul_ne_zero hn' hd), Real.exp_log t.2]
      rw [ht, ← UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n, galAd_eq_adm σ s h]
      exact map_splitCentre σ n _
end

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem map_closure {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H)
    (hU : ∀ v, ‖U v‖ = ‖v‖) (A V : Submodule ℂ H) :
    V = A.topologicalClosure ↔ V.map U.toLinearMap = (A.map U.toLinearMap).topologicalClosure := by
  have hi : Isometry U := AddMonoidHomClass.isometry_of_norm U hU
  have e : (A.map U.toLinearMap).topologicalClosure = A.topologicalClosure.map U.toLinearMap := SetLike.coe_injective (by
    rw [Submodule.topologicalClosure_coe, Submodule.map_coe, Submodule.map_coe, Submodule.topologicalClosure_coe]
    exact hi.isClosedEmbedding.closure_image_eq _)
  rw [e]
  exact (Submodule.map_injective_of_injective (f := U.toLinearMap) hi.injective).eq_iff.symm

theorem UpperTheory.ConvolutionTheory.Dp.conjCarries :
    UpperTheory.ConvolutionTheory.Dp.ConjCarries := by
  intro E _ _ _ n μ _ θ σ s hs hθ π π' V' hsp
  set m : GA E n →* GA E n := Matrix.GeneralLinearGroup.map s.toRingHom with hm
  have hsurj : Function.Surjective m := fun g => ⟨Matrix.GeneralLinearGroup.map s.symm.toRingHom g, by
    ext i j : 2
    exact s.apply_symm_apply _⟩
  have hcen : ∀ t, m (centralSection E n t) = centralSection E n t := (galCentral E n σ s hs).2
  have hmem : ∀ (ρ : CuspSub E n) (f : GA E n → ℂ), f ∈ (UpperTheory.CBC.Cusp.cx ρ).space ↔ ∃ φ ∈ Cm.carrier ρ, f = φ.1 := fun ρ f => by
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [← Cm.map_carrier] at hφ
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      exact ⟨ψ, hψ, rfl⟩
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨_, hφ, rfl⟩
  have h1 : ∀ ψ ∈ Cm.carrier π', ∃ φ ∈ Cm.carrier π, ∀ g, ψ.1 g = φ.1 (m g) := fun ψ hψ => by
    have h := (hmem π' _).2 ⟨ψ, hψ, rfl⟩
    rw [hsp] at h
    obtain ⟨f, hf, e⟩ := h
    obtain ⟨φ, hφ, rfl⟩ := (hmem π f).1 hf
    exact ⟨φ, hφ, fun g => (congrFun e g).symm⟩
  have h2 : ∀ φ ∈ Cm.carrier π, ∃ ψ ∈ Cm.carrier π', ∀ g, ψ.1 g = φ.1 (m g) := fun φ hφ => by
    have h : (fun g => φ.1 (m g)) ∈ (UpperTheory.CBC.Cusp.cx π').space := by
      rw [hsp]
      exact ⟨φ.1, (hmem π _).2 ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := (hmem π' _).1 h
    exact ⟨ψ, hψ, fun g => (congrFun e g).symm⟩
  have hc : Cm.carrier π' ≤ centralCuspForms E n ↔ Cm.carrier π ≤ centralCuspForms E n := by
    constructor
    · intro h φ hφ t x
      obtain ⟨ψ, hψ, e⟩ := h2 φ hφ
      obtain ⟨y, rfl⟩ := hsurj x
      have h3 := h hψ t y
      rwa [e, e, map_mul, hcen] at h3
    · intro h ψ hψ t x
      obtain ⟨φ, hφ, e⟩ := h1 ψ hψ
      have h3 := h hφ t (m x)
      show ψ.1 (centralSection E n t * x) = ψ.1 x
      rw [e, e, map_mul, hcen]
      exact h3
  rw [exSummand E n μ π' V', exSummand E n μ π, hc]
  refine and_congr_right fun h => ?_
  have hU : ∀ φ ∈ Cm.carrier π, ∀ ψ ∈ Cm.carrier π', (∀ g, ψ.1 g = φ.1 (m g)) → θ.U (clsL μ ψ) = clsL μ φ := fun φ hφ ψ hψ e =>
    (twCls E n μ θ φ (h hφ) ψ (hc.2 h hψ)).2 fun x => (e x).trans (congrArg φ.1 (hθ x).symm)
  have e : (Cm.carrier π).map (clsL μ) = ((Cm.carrier π').map (clsL μ)).map θ.U.toLinearMap := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => ?_)
      (Submodule.map_le_iff_le_comap.2 (Submodule.map_le_iff_le_comap.2 fun ψ hψ => ?_))
    · obtain ⟨ψ, hψ, e⟩ := h2 φ hφ
      exact Submodule.mem_map.2 ⟨_, Submodule.mem_map_of_mem hψ, hU φ hφ ψ hψ e⟩
    · obtain ⟨φ, hφ, e⟩ := h1 ψ hψ
      exact Submodule.mem_map.2 ⟨φ, hφ, (hU φ hφ ψ hψ e).symm⟩
  rw [e]
  exact map_closure θ.U (twUnitary E n μ θ).1 _ _
end
