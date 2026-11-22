module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesOrthonormalJStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApplyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOperStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAcStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurEquivariantIsometryScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqScalarCharacterOfDoubleCoverUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadraticStatement

@[expose] public section

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
      refine continuous_finsetSum _ fun a _ => Continuous.smul (Complex.continuous_ofReal.comp ?_) (ih _)
      exact (continuous_apply a).comp
        (((continuous_const.matrix_mul hm.matrix_transpose).matrix_mul continuous_const).neg.matrix_mulVec continuous_const)
    · intro f
      simp only [ContinuousLinearMap.zero_apply]
      exact continuous_const
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
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

end GlobalTheory.ArchRep

end
