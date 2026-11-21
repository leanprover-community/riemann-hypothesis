import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IsClosedOfCoheight
import Mathlib
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFUnitNeZero
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfKnownTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TotalDegreeLinSubstLe
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FormHeightGen
import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormOfIntegralVersion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanEqMahler
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeClosedPoint
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartResidueDegreeAlgClosedClosed

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.Points

namespace ChowFormHeightComparison₂.CF

namespace ModelEmbedding

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω} {m : ℕ}
  {σ : Fin m → H.Sec} {t : Fin m → Ω}

theorem emb (hM : M.IsCl t) (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hs : ⨆ k, nonzeroLocus (σ k) = ⊤) : Emb M.s σ := by
  refine ⟨hH, hs, fun i => ?_⟩
  have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
    have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
    subst this
    infer_instance
  have key' := mem_nonzeroLocus_iff_div hH hd hv (PositivityTheory.UnitarySelfGeneration.UnitProductCombination.exists_unit hd hv hs) i
  generalize nonzeroLocus (σ i) = W at key' ⊢
  by_cases hi : t i = 0
  · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
    subst hW
    refine ⟨isAffineOpen_bot _, fun _ => 0, fun f => ⟨0, Subsingleton.elim _ _⟩, fun j l => ?_⟩
    have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
    exact Subsingleton.elim _ _
  · obtain ⟨U, hUa, hUe, hR⟩ := hM.2 i hi
    have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
    subst hWU
    have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
    have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
      (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
    choose r hr using hr
    refine ⟨hUa, r, fun f => ?_, fun j l => ?_⟩
    · have h1 : valF M.pt W f ∈ M.ringOn W := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
      rw [hR, Algebra.adjoin_range_eq_range_aeval] at h1
      obtain ⟨q, hq⟩ := h1
      have e : (M.res W hne).comp (eval₂Hom (algX M.s W) r) =
          (aeval (R := o) fun j => t j / t i).toRingHom :=
        MvPolynomial.ringHom_ext (fun a => by
          simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
          exact (M.res_apply W hne _).trans (M.valF_constFn hne a)) fun j => by
          simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
          exact (M.res_apply W hne _).trans (hr j)
      exact ⟨q, M.res_injective W hne ((RingHom.congr_fun e q).trans (hq.trans (M.res_apply W hne f).symm))⟩
    · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
      · have hl' : (H.U l : Set M.Z).Nonempty := hl.mono fun z hz => hz.2
        apply M.res_injective _ hl
        rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
          hv j l hl', hv i l hl', hr]
        have hdl := hd.ne l
        field_simp
      · have := hempty _ hl
        exact Subsingleton.elim _ _

theorem desc_eval (U : M.Z.Opens) (hV : M.pt (IsLocalRing.closedPoint Ω) ∈ U) (f : Γ(M.Z, U)) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt)).hom
      ((M.Z.evaluation U _ hV).hom f) = valF M.pt U f := by
  rw [valF_eq_valR, valR_eq M.pt U (M.top_le_preimage_pt ⟨_, hV⟩), ← germ_stalkClosedPointTo_eq_valMap,
    ← CommRingCat.comp_apply, ← Scheme.germ_residue, Category.assoc, Scheme.residue_descResidueField]

end ModelEmbedding

open ModelEmbedding

attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem stModel : StModel := by
  intro K Ω _ _ _ _ m t Z hZ H hH e he s hv hs _
  refine ⟨emb hZ hH he hv hs, ?_⟩
  have key : ∀ (i : H.ι) (h : Z.pt (IsLocalRing.closedPoint Ω) ∈ H.U i),
      RingHom.ker (coneHom Z.s s _ i h) =
        (GlobalTheory.CompHt.coneIdeal K t).comap (MvPolynomial.map (algebraMap (𝓞 K) K)) := fun i h => by
    have hne : (H.U i : Set Z.Z).Nonempty := ⟨_, h⟩
    have e1 : (Polynomial.mapRingHom (Scheme.descResidueField
        (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Z.pt)).hom).comp (coneHom Z.s s _ i h) =
        (GlobalTheory.CompHt.coneMap K ((e i)⁻¹ • t)).toRingHom.comp (MvPolynomial.map (algebraMap (𝓞 K) K)) :=
      MvPolynomial.ringHom_ext (fun a => by
        simp only [coneHom, GlobalTheory.CompHt.coneMap, eval₂Hom_C, RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_C, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, Polynomial.algebraMap_apply]
        exact congrArg Polynomial.C ((desc_eval _ h _).trans ((Z.valF_constFn hne a).trans
          (IsScalarTower.algebraMap_apply (𝓞 K) K Ω a)))) fun k => by
        simp only [coneHom, GlobalTheory.CompHt.coneMap, eval₂Hom_X', RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          aeval_X]
        exact congrArg (fun c => Polynomial.X * Polynomial.C c) ((desc_eval _ h _).trans ((hv k i hne).trans
          (div_eq_inv_mul _ _)))
    rw [← GlobalTheory.CompHt.coneIdeal_smul (inv_ne_zero (he.ne i))]
    have hinj : Function.Injective (Polynomial.mapRingHom (Scheme.descResidueField
        (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Z.pt)).hom) :=
      Polynomial.map_injective _ (RingHom.injective _)
    exact (RingHom.ker_comp_of_injective (coneHom Z.s s _ i h) hinj).symm.trans
      ((congrArg RingHom.ker e1).trans (RingHom.comap_ker _ _).symm)
  have h2 : ptIdeal Z.s s (genericPoint Z.Z) =
      (GlobalTheory.CompHt.coneIdeal K t).comap (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    rw [← Z.pt_apply (IsLocalRing.closedPoint Ω)]
    have hm : Z.pt (IsLocalRing.closedPoint Ω) ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hl⟩ := Opens.mem_iSup.1 hm
    exact le_antisymm ((iInf₂_le l hl).trans (key l hl).le) (le_iInf₂ fun i h => (key i h).ge)
  rw [genIdeal, h2]
  exact IsLocalization.map_comap ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin m))) (MvPolynomial (Fin m) K) _

end ChowFormHeightComparison₂.CF
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts
open GroundTheory.Heights₂.Heights (HermNorm ArchData)

namespace ChowFormHeightComparison₂.CF

theorem sum_normSq_eq {m : ℕ} (w : Fin m → ℂ) : ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_normSq_unitary {m : ℕ} {V : Matrix (Fin m) (Fin m) ℂ} (h : star V * V = 1) (x : Fin m → ℂ) :
    ∑ i, ‖(V *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_normSq_eq, sum_normSq_eq, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, h, Matrix.vecMul_one]

def normOf {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (h : M.det ≠ 0) : HermNorm m :=
  ⟨M⁻¹, Matrix.isUnit_nonsing_inv_det M h.isUnit⟩

theorem dualNorm_normOf {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (h : M.det ≠ 0) (y : Fin m → ℂ) :
    (normOf M h).dualNorm y = √(∑ a, ‖∑ k, M k a * y k‖ ^ 2) := by
  have hT : IsUnit Mᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit
  simp only [HermNorm.dualNorm, normOf]
  rw [Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hT]
  congr 1

theorem norm_normOf_conj {m : ℕ} {M M' U : Matrix (Fin m) (Fin m) ℂ} (h : M.det ≠ 0) (h' : M'.det ≠ 0)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (e : M' = M.map (starRingEnd ℂ) * U) (u : Fin m → ℂ) :
    (normOf M' h').norm (star u) = (normOf M h).norm u := by
  subst e
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hinvU : U⁻¹ = star U := Matrix.inv_eq_left_inv hU1
  have hmap : (M.map (starRingEnd ℂ))⁻¹ = (M⁻¹).map (starRingEnd ℂ) := by
    have h1 : M.map (starRingEnd ℂ) = (Mᴴ)ᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have h2 : (M⁻¹).map (starRingEnd ℂ) = ((M⁻¹)ᴴ)ᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [h1, h2, ← Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv]
  have hv : (M⁻¹).map (starRingEnd ℂ) *ᵥ star u = star (M⁻¹ *ᵥ u) := by
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  have key : (M.map (starRingEnd ℂ) * U)⁻¹ *ᵥ star u = star U *ᵥ star (M⁻¹ *ᵥ u) := by
    rw [Matrix.mul_inv_rev, hinvU, hmap, ← Matrix.mulVec_mulVec, hv]
  simp only [HermNorm.norm, normOf]
  rw [key]
  congr 1
  have hV : star (star U) * star U = 1 := by rw [star_star]; exact hU2
  rw [sum_normSq_unitary hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.star_apply]

theorem glue : StMain → StModel → StForm → GlobalTheory.Published.ArExists → PositivityTheory.UnitarySelfGeneration.ChowFormHeight := by
  intro hMain hModel hForm hAr
  intro K Ω _ _ _ _ d N m δ g A hg hA _ y Z hcl hvar Φ hΦ H hH e hgen s hval hs Mt hdet hc harch
  haveI := Z.integral
  obtain ⟨hEmb, hgenI⟩ := hModel K Ω m (fun k => ∑ j, algebraMap K Ω (g j k) * y j) Z hcl H hH e hgen s hval hs
    hvar.charZero
  let D : ArchData K m := ⟨fun σ => normOf (Mt (σ.comp (algebraMap (𝓞 K) K))) (hdet _), fun σ u => by
      obtain ⟨U, hU, hUe⟩ := hc (σ.comp (algebraMap (𝓞 K) K))
      exact norm_normOf_conj (hdet _) (hdet _) hU hUe u⟩
  have hdual : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ),
      (D.normAt σ).dualNorm (fun k => ∑ j, σ (g j k) * x j) = Adelic.archSize (A σ) x := by
    intro σ x
    show (normOf (Mt (σ.comp (algebraMap (𝓞 K) K))) (hdet _)).dualNorm _ = _
    rw [dualNorm_normOf, harch σ x]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  obtain ⟨hCF, hMH, hFH⟩ := hForm K Ω d N m δ g A hg hA y Φ hΦ D hdual
  obtain ⟨h0, hh0⟩ := (hAr (𝓞 K) Z.Z Z.s d hvar).1 (HermLB.fs Z.s hH s hs Mt hdet hc)
  have hSI : (HermLB.fs Z.s hH s hs Mt hdet hc).IsSelfInter (h0 (genericPoint _)) := ⟨h0, hh0, rfl⟩
  have hFS : ∀ σ : K →+* ℂ,
      IsFS ((HermLB.fs Z.s hH s hs Mt hdet hc).φ (σ.comp (algebraMap (𝓞 K) K))) s (D.normAt σ) := by
    intro σ i z _
    refine (Weight.fsBasis_φ (p := Z.s) (σ := σ.comp (algebraMap (𝓞 K) K)) hH s hs _ (hdet _) i z).trans ?_
    show _ = Real.log (((normOf (Mt (σ.comp (algebraMap (𝓞 K) K))) (hdet _)).dualNorm _) ^ 2)
    rw [dualNorm_normOf, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    rfl
  have hEq := hMain K m D d Z.Z Z.s (HermLB.fs Z.s hH s hs Mt hdet hc) s hvar hEmb hFS δ
    (ChowHt.linSubst g Φ) (hgenI ▸ hCF) hMH _ hSI
  rw [hFH, ← hEq]
  exact hSI

end ChowFormHeightComparison₂.CF
end
end

section
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Matrix GlobalTheory.ChowHt GroundTheory.Heights₂.Heights

namespace ChowFormHeightComparison₂.CF.D

theorem gaussAbs_eq {K : Type} [Field K] [NumberField K] {ι : Type} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (f : MvPolynomial ι K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.equivHeightOneSpectrum.symm v) f = gaussNorm v f := by
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs gaussNorm
  congr 2
  funext s
  apply NNReal.eq
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply]
  show ((‖(FinitePlace.embedding v) (coeff s f)‖).toNNReal : ℝ) = HeightOneSpectrum.adicAbv K v (coeff s f)
  rw [FinitePlace.norm_embedding]
  exact Real.coe_toNNReal _ (AbsoluteValue.nonneg _ _)

theorem mean_eq_mahler {m k : ℕ} (hm : 1 ≤ m) (h : HermNorm m) {f : MvPolynomial (Fin k × Fin m) ℂ} (hf : f ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst h.mat⁻¹ f) = mahler h k f := by
  have hB : (h.mat * h.mat⁻¹)ᴴ * (h.mat * h.mat⁻¹) = 1 := by
    rw [Matrix.mul_nonsing_inv _ h.isUnit_det]
    simp
  rw [← GlobalTheory.CompanionTheory.Ar.HS.SphereMean.sphere_mean_eq_mahler m k h h.mat⁻¹ f hm hf hB]
  have hP : ∀ n, ReciprocityTheory.MultiplicativeHeights.sphereProb n = GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP n := by
    intro n
    unfold ReciprocityTheory.MultiplicativeHeights.sphereProb GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP
    rw [ProbabilityTheory.cond, MeasureTheory.Measure.restrict_univ]
  have hE : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere k m,
      eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (linSubst h.mat⁻¹ f) =
        eval (fun p : Fin k × Fin m => (h.mat⁻¹ *ᵥ fun a => (↑(z p.1) : EuclideanSpace ℂ (Fin m)).ofLp a) p.2) f := by
    intro z
    unfold linSubst
    rw [MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    erw [MvPolynomial.aeval_bind₁]
    refine congrArg (fun g => MvPolynomial.aeval g f) ?_
    funext p
    simp [ReciprocityTheory.MultiplicativeHeights.blockPoint, ReciprocityTheory.MultiplicativeHeights.spherePoint, Matrix.mulVec, dotProduct, mul_comm]
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  simp only [hP, hE]

theorem formHeight_one_eq {K : Type} [Field K] [NumberField K] {m k : ℕ} (hm : 1 ≤ m) (H : ArchData K m) (δ : ℕ)
    {f : MvPolynomial (Fin k × Fin m) K} (hf : f ≠ 0) :
    formHeight δ (1 : Matrix (Fin m) (Fin m) K) (fun σ => (H.normAt σ).mat⁻¹) f = chowHt H k δ f := by
  unfold formHeight chowHt
  rw [GlobalTheory.HeightUnique.linSubst_one, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  have e (σ : K →+* ℂ) : ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst (H.normAt σ).mat⁻¹ (MvPolynomial.map σ f)) =
      mahler (H.normAt σ) k (MvPolynomial.map σ f) :=
    mean_eq_mahler hm _ fun h0 => hf (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  simp only [gaussAbs_eq, e]
  ring

end ChowFormHeightComparison₂.CF.D

private theorem coneMap_comp_coordSubst {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N N' : ℕ}
    (M : Matrix (Fin N) (Fin N') K) (y : Fin N → Ω) :
    (GlobalTheory.CompHt.coneMap K y).comp (GlobalTheory.CompHt.coordSubst M) =
      GlobalTheory.CompHt.coneMap K (fun k => ∑ j, algebraMap K Ω (M j k) * y j) := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [AlgHom.comp_apply, GlobalTheory.CompHt.coordSubst, GlobalTheory.CompHt.coneMap, MvPolynomial.aeval_X, map_sum,
    map_mul, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem aeval_linSubst {K L : Type} [Field K] [CommRing L] [Algebra K L] {B N n : ℕ}
    (M : Matrix (Fin N) (Fin n) K) (f : MvPolynomial (Fin B × Fin N) K) (u : Fin B × Fin n → L) :
    MvPolynomial.aeval u (linSubst M f) =
      MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, algebraMap K L (M p.2 k) * u (p.1, k)) f := by
  unfold linSubst
  rw [MvPolynomial.aeval_eq_bind₁]
  erw [MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g f) ?_
  funext p
  simp [MvPolynomial.aeval_X, MvPolynomial.aeval_C]

private theorem isChowForm_of_isChowFormInt {k : Type} [Field k] {N : ℕ} {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (hf : IsChowFormInt I e dl f) :
    GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  refine ⟨hf.ne_zero, fun p => ⟨fun hp => hf.dvd_of_forall_aeval_eq_zero
    (fun u hu => hp u ((hf.zero_iff u).1 hu)), ?_⟩⟩
  rintro ⟨q, rfl⟩ u hu
  rw [map_mul, (hf.zero_iff u).2 hu, zero_mul]

private theorem sum_algebraMap_mul_sum_eq_matrix_mul {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b c : ℕ}
    (M : Matrix (Fin a) (Fin b) K) (P : Matrix (Fin b) (Fin c) K) (z : Fin a → L) (k : Fin c) :
    ∑ j : Fin b, algebraMap K L (P j k) * ∑ i : Fin a, algebraMap K L (M i j) * z i =
      ∑ i, algebraMap K L ((M * P) i k) * z i := by
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem sum_sum_algebraMap_mul_comm {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b : ℕ}
    (g : Matrix (Fin a) (Fin b) K) (v : Fin b → L) (z : Fin a → L) :
    ∑ j, (∑ k, algebraMap K L (g j k) * v k) * z j = ∑ k, v k * ∑ j, algebraMap K L (g j k) * z j := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

private theorem exists_right_inverse_of_span_col_eq_top {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) : ∃ P : Matrix (Fin m) (Fin N) K, g * P = 1 := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective g.mulVecLin
    (by rw [Matrix.range_mulVecLin, hg])
  refine ⟨LinearMap.toMatrix' r, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hr
  have h2 : LinearMap.toMatrix' g.mulVecLin = g := LinearMap.toMatrix'_toLin' g
  rw [LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id] at h1
  exact h1

private theorem isMultiHomog_of_isMultiHomogeneous_const {K : Type} [Field K] {B n δ : ℕ} (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f) : GroundTheory.Heights₂.Heights.IsMultiHomog δ f := by
  intro s hs
  funext b
  have hb : ∑ j : Fin n, s (b, j) = δ := hf s (MvPolynomial.mem_support_iff.2 hs) b
  rw [← hb, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [GroundTheory.Heights₂.Heights.groupWeight, Pi.single_apply]

open ChowFormHeightComparison₂.CF.D in

theorem ChowFormHeightComparison₂.CF.stForm : ChowFormHeightComparison₂.CF.StForm := by
  intro K Ω _ _ _ _ d N m δ g A hspan hA y Φ hΦ H hH
  obtain ⟨P, hgP⟩ := exists_right_inverse_of_span_col_eq_top g hspan
  have hne : Φ ≠ 0 := hΦ.ne_zero
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      exfalso
      have hirr := hΦ.irred
      have hC := MvPolynomial.eq_C_of_isEmpty Φ
      have hc : MvPolynomial.coeff 0 Φ ≠ 0 := fun h => hne (by rw [hC, h, map_zero])
      rw [hC] at hirr
      exact hirr.not_isUnit ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C)
    · exact h0
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exfalso
      have := congrFun (congrFun hgP ⟨0, hN⟩) ⟨0, hN⟩
      simp [Matrix.mul_apply] at this
    · exact h0
  refine ⟨isChowForm_of_isChowFormInt (dl := δ) ?_, isMultiHomog_of_isMultiHomogeneous_const _ (GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog), ?_⟩
  · refine ⟨GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog, PositivityTheory.UnitarySelfGeneration.UnitProductCombination.irreducible_linSubst hgP hΦ.irred, ?_⟩
    intro u
    rw [aeval_linSubst, hΦ.zero_iff]
    constructor
    · rintro ⟨z, hz0, hzI, hzu⟩
      refine ⟨fun k => ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j, ?_, ?_, ?_⟩
      · intro hx
        apply hz0
        have hx' : ∀ k, ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j = 0 := fun k => congrFun hx k
        funext i
        have h2 := sum_algebraMap_mul_sum_eq_matrix_mul g P z i
        simp only [hx', mul_zero, Finset.sum_const_zero, hgP, Matrix.one_apply] at h2
        simpa using h2.symm
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hzI
        show GlobalTheory.CompHt.coneMap K y (GlobalTheory.CompHt.coordSubst g h) = 0
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst]
        exact hh
      · intro i
        exact (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) z).symm.trans (hzu i)
    · rintro ⟨x, hx0, hxI, hxu⟩
      have hxz : ∀ k, x k = ∑ j, algebraMap K (AlgebraicClosure K) (g j k) *
          ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' := by
        intro k
        have hl : (MvPolynomial.X k - GlobalTheory.CompHt.coordSubst (P * g) (MvPolynomial.X k)) ∈
            GlobalTheory.CompHt.coneIdeal K (fun k => ∑ j, algebraMap K Ω (g j k) * y j) := by
          show GlobalTheory.CompHt.coneMap K _ _ = 0
          have e : (fun k => ∑ j, algebraMap K Ω ((P * g) j k) * ∑ i, algebraMap K Ω (g i j) * y i) =
              fun k => ∑ i, algebraMap K Ω (g i k) * y i := by
            funext k
            rw [sum_algebraMap_mul_sum_eq_matrix_mul, ← Matrix.mul_assoc, hgP, Matrix.one_mul]
          rw [map_sub, ← AlgHom.comp_apply, coneMap_comp_coordSubst, e, sub_self]
        have h3 := hxI _ hl
        rw [map_sub, GlobalTheory.CompHt.aeval_coordSubst, MvPolynomial.aeval_X, MvPolynomial.aeval_X, sub_eq_zero] at h3
        rw [h3]
        exact (sum_algebraMap_mul_sum_eq_matrix_mul P g x k).symm
      refine ⟨fun j => ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k', ?_, ?_, ?_⟩
      · intro hz
        apply hx0
        have hz' : ∀ j, ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' = 0 := fun j => congrFun hz j
        funext k
        rw [hxz k]
        simp [hz']
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hxI
        show GlobalTheory.CompHt.coneMap K _ (GlobalTheory.CompHt.coordSubst P h) = 0
        have e : (fun k => ∑ j, algebraMap K Ω (P j k) * ∑ i, algebraMap K Ω (g i j) * y i) = y := by
          funext k
          rw [sum_algebraMap_mul_sum_eq_matrix_mul, hgP]
          simp [Matrix.one_apply]
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst, e]
        exact hh
      · intro i
        refine (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) _).trans ?_
        simp only [← hxz]
        exact hxu i
  · rw [← PositivityTheory.UnitarySelfGeneration.UnitProductCombination.formHeight_gen hN g hspan A hA (fun σ => (H.normAt σ).mat⁻¹) ?_ hne hΦ.homog,
      formHeight_one_eq hm H δ (GlobalTheory.HeightUnique.linSubst_ne_zero hgP hne)]
    intro σ x
    have h1 := hH σ x
    unfold GroundTheory.Heights₂.Heights.HermNorm.dualNorm at h1
    rw [← h1, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Matrix.mulVec, dotProduct, ← Matrix.transpose_nonsing_inv]
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.Cartier

namespace ChowFormHeightComparison₂.CF.H

variable {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {m : ℕ} {p : Z ⟶ Sp R} {s : Fin m → B.Sec}

theorem eval₂_coords_eq_zero (hB : B.IsLB) {σ : R →+* ℂ} (y : CxPts p σ) {q : MvPolynomial (Fin m) R}
    (hq : q ∈ ptIdeal p s (under y)) : eval₂ σ (coords p σ hB s y) q = 0 := by
  have hy0 : y ∈ ptsIn p σ (B.U (pick hB y)) := mem_pick hB y
  have hz : under y ∈ B.U (pick hB y) := mem_ptsIn.mp hy0
  let ψ := Z.descResidueField (Scheme.stalkClosedPointTo (y : Sp ℂ ⟶ Z))
  have hev : ∀ f : Γ(Z, B.U (pick hB y)),
      ψ.hom ((Z.evaluation (B.U (pick hB y)) (under y) hz).hom f) = ev p σ (B.U (pick hB y)) f y := by
    intro f
    have hv := congrArg (fun g => g.hom f)
      (Points.germ_stalkClosedPointTo_eq_valMap (C := ℂ) (y : Sp ℂ ⟶ Z) (B.U (pick hB y)) hy0)
    rw [ev_eq hy0, evHom]
    refine Eq.trans ?_ hv
    rfl
  have hmem : q ∈ RingHom.ker (coneHom p s (under y) (pick hB y) hz) := by
    have h := hq
    simp only [ptIdeal, Submodule.mem_iInf] at h
    exact h _ hz
  have hΦ : eval₂Hom σ (coords p σ hB s y) = (Polynomial.evalRingHom 1).comp
      ((Polynomial.mapRingHom ψ.hom).comp (coneHom p s (under y) (pick hB y) hz)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [coneHom, RingHom.comp_apply, eval₂Hom_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
      erw [hev, ev_algX hy0]
    · intro k
      simp only [coneHom, RingHom.comp_apply, eval₂Hom_X', Polynomial.coe_mapRingHom, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, one_mul]
      erw [hev]
      rfl
  have he : eval₂ σ (coords p σ hB s y) q = eval₂Hom σ (coords p σ hB s y) q := rfl
  rw [he, hΦ, RingHom.comp_apply, RingHom.comp_apply, RingHom.mem_ker.mp hmem, map_zero, map_zero]

theorem exists_form (h1 : StPts) [IsIntegral Z] [NoetherianSpace Z] (hE : Emb p s) (U : Z.Opens)
    (hU : genericPoint Z ∈ U) : ∃ (n : ℕ) (q : MvPolynomial (Fin m) R), q.IsHomogeneous n ∧
      q ∉ ptIdeal p s (genericPoint Z) ∧ ∀ z, z ∉ U → q ∈ ptIdeal p s z := by
  obtain ⟨hprime, hspec, -, -⟩ := h1 R Z p B m s hE
  let C : Closeds Z := ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩
  obtain ⟨S, hirr, hSC⟩ := NoetherianSpace.exists_finset_irreducible C
  have hg0 : ∀ k : S, ∃ g : Z, IsGenericPoint g (k : Set Z) := fun k => QuasiSober.sober (hirr k) k.1.isClosed
  choose g hg using hg0
  have hr0 : ∀ k : S, ∃ (d : ℕ) (r : MvPolynomial (Fin m) R), r.IsHomogeneous d ∧ r ∈ ptIdeal p s (g k) ∧
      r ∉ ptIdeal p s (genericPoint Z) := by
    intro k
    have hk : (k : Set Z) ⊆ (U : Set Z)ᶜ := by
      intro z hz
      have h' : z ∈ (C : Set Z) := by
        rw [hSC]
        exact (Finset.le_sup (f := id) k.2) hz
      exact h'
    have hnot : ¬ ptIdeal p s (g k) ≤ ptIdeal p s (genericPoint Z) := by
      intro hle
      have hm : genericPoint Z ∈ closure ({g k} : Set Z) := specializes_iff_mem_closure.mp ((hspec _ _).mpr hle)
      have hcl : closure ({g k} : Set Z) = (k : Set Z) := hg k
      rw [hcl] at hm
      exact hk hm hU
    obtain ⟨f, hf, hfn⟩ := Set.not_subset.mp hnot
    have hex : ∃ d, homogeneousComponent d f ∉ ptIdeal p s (genericPoint Z) := by
      by_contra hcon
      push_neg at hcon
      apply hfn
      rw [← MvPolynomial.sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => hcon d
    obtain ⟨d, hd⟩ := hex
    exact ⟨d, _, homogeneousComponent_isHomogeneous d f, (hprime (g k)).isHomog f hf d, hd⟩
  choose d r hr using hr0
  refine ⟨∑ k, d k, ∏ k, r k, IsHomogeneous.prod _ _ _ fun k _ => (hr k).1, ?_, ?_⟩
  · intro hmem
    obtain ⟨k, -, hk⟩ := ((hprime _).isPrime.prod_mem_iff).mp hmem
    exact (hr k).2.2 hk
  · intro z hz
    have hzC : z ∈ (C : Set Z) := hz
    rw [hSC, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hzC
    simp only [Set.mem_iUnion] at hzC
    obtain ⟨k, hkS, hzk⟩ := hzC
    have hle := (hspec (g ⟨k, hkS⟩) z).mp ((hg ⟨k, hkS⟩).specializes hzk)
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) (hle (hr ⟨k, hkS⟩).2.1)

end ChowFormHeightComparison₂.CF.H

open ChowFormHeightComparison₂.CF.H in

theorem ChowFormHeightComparison₂.CF.stCharts (h1 : ChowFormHeightComparison₂.CF.StPts) : ChowFormHeightComparison₂.CF.StCharts := by
  intro K _ _ Z _ p B m s e hE hX
  have := hX.isNoetherian
  obtain ⟨U, x, hU, hg, hx⟩ := GlobalTheory.GenericEtale.exists_etale_coords hX
  obtain ⟨n, q, h₁, h₂, h₃⟩ := exists_form h1 hE U hg
  refine ⟨n, q, h₁, h₂, fun σ y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ U := mem_ptsIn.2 (by_contra fun h => hy (eval₂_coords_eq_zero hE.isLB y (h₃ _ h)))
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx hy'
  exact ⟨c, hc⟩
end
end

section
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.VB

namespace ChowFormHeightComparison₂.CF.V

section Stalk

variable {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (G : Y.Modules)

def pushStalk (y : Y) :
    (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) →+ (G.presheaf.stalk y :) :=
  (TopCat.Presheaf.stalkPushforward Ab.{0} i.base G.presheaf y).hom

omit [IsClosedImmersion i] in
theorem pushStalk_germ (y : Y) (U : X.Opens) (h : i y ∈ U) (s : Γ((Scheme.Modules.pushforward i).obj G, U)) :
    pushStalk i G y (((Scheme.Modules.pushforward i).obj G).presheaf.germ U (i y) h s) =
      G.presheaf.germ (i ⁻¹ᵁ U) y h s :=
  TopCat.Presheaf.stalkPushforward_germ_apply Ab.{0} i.base G.presheaf U y h s

theorem pushStalk_bijective (y : Y) : Function.Bijective (pushStalk i G y) :=
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{0} (f := i.base)
    i.isClosedEmbedding.isInducing G.presheaf y
  ConcreteCategory.bijective_of_isIso (TopCat.Presheaf.stalkPushforward Ab.{0} i.base G.presheaf y)

omit [IsClosedImmersion i] in
theorem pushStalk_smul (y : Y) (r : X.presheaf.stalk (i y))
    (t : (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :)) :
    pushStalk i G y (r • t) = i.stalkMap y r • pushStalk i G y t := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hV, s, rfl⟩ := Twist.exists_germ_eq_of_mem hU t
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) (i y) hV a, ← QCoh.germ_smul, pushStalk_germ, pushStalk_germ,
    Scheme.Hom.germ_stalkMap_apply]
  exact QCoh.germ_smul (F := G) (U := i ⁻¹ᵁ V) y hV _ s

theorem length_push (y : Y) :
    Module.length (X.presheaf.stalk (i y)) (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (G.presheaf.stalk y :) := by
  letI := (i.stalkMap y).hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (G.presheaf.stalk y :) := Module.compHom _ (i.stalkMap y).hom
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (G.presheaf.stalk y :) :=
    .of_algebraMap_smul fun _ _ => rfl
  let l : (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) →ₗ[X.presheaf.stalk (i y)]
      (G.presheaf.stalk y :) :=
    { toFun := pushStalk i G y, map_add' := map_add _, map_smul' := pushStalk_smul i G y }
  rw [(LinearEquiv.ofBijective l (pushStalk_bijective i G y)).length_eq]
  exact Module.length_eq_of_surjective (S := X.presheaf.stalk (i y)) (i.stalkMap_surjective y)

theorem mem_support_push (y : Y) :
    i y ∈ support ((Scheme.Modules.pushforward i).obj G) ↔ y ∈ support G :=
  (Equiv.ofBijective _ (pushStalk_bijective i G y)).nontrivial_congr

theorem range_of_mem_support_push {x : X} (hx : x ∈ support ((Scheme.Modules.pushforward i).obj G)) :
    x ∈ Set.range i := by
  by_contra hr
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hx
  refine hx (subsingleton_of_forall_eq 0 fun t => ?_)
  let W : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨V, hVW, hV, s, rfl⟩ := Twist.exists_germ_eq_of_mem (U := W) hr t
  have h0 : s = 0 := section_eq_zero_of_germ (F := G) _ fun z hz => absurd ⟨z, rfl⟩ (hVW hz)
  rw [h0, map_zero]

end Stalk

variable {κ : Type} [Field κ]

theorem interNum_of_genRank_eq {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)] (hp : IsProjOver (strHom κ Z))
    {d : ℕ} (hd : topologicalKrullDim Z ≤ d) {P : Fin d → LB Z} (hL : ∀ j, (P j).IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (GlobalTheory.structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 := topologicalKrullDim_add_one_le (QCoh.isClosed_support G) isClosed_univ
      fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
    have h2 : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z :=
      (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq
    have : QCoh.suppDim G < Fintype.card (Fin d) := by
      rw [Fintype.card_fin]
      by_contra hc
      rw [not_lt] at hc
      have h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ d := (add_le_add_left hc 1).trans (h0.trans (h2.le.trans hd))
      have h4 : d + 1 ≤ d := by exact_mod_cast h3
      omega
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := d) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

theorem interNum_eq_sum {X : Scheme.{0}} [Algebra κ Γ(X, ⊤)] (hp : IsProjOver (strHom κ X)) {d : ℕ}
    {P : Fin d → LB X} (hL : ∀ j, (P j).IsLB) (S : Set X) (T : Finset X) (deg : X → ℤ)
    (hT : ∀ z ∈ T, topologicalKrullDim (closure {z} : Set X) = d)
    (hS : ∀ z ∈ S, z ∉ T → topologicalKrullDim (closure {z} : Set X) < d)
    (hdeg : ∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y] [Algebra κ Γ(Y, ⊤)],
      (∀ r : κ, i.appTop (algebraMap κ Γ(X, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) → i (genericPoint Y) ∈ T →
      interNum κ (GlobalTheory.structureModule Y) (fun j => (P j).pull i) = deg (i (genericPoint Y)))
    (F : X.Modules) (hF : IsFiniteQC F) (hFS : support F ⊆ S) :
    (∀ z ∈ T, Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :) ≠ ⊤) ∧
      interNum κ F P = ∑ z ∈ T, ((Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :)).toNat : ℤ) * deg z := by
  classical
  have := isNoetherian_of_isProjOver hp
  have hf := algebraMap_eq_strHom κ X
  have hz : ∀ (E : X.Modules) (z : X), z ∉ support E →
      Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0 := fun E z h =>
    have := notMem_support_iff.1 h
    Module.length_eq_zero
  revert hFS
  refine QCoh.devissage X (fun F => support F ⊆ S →
    (∀ z ∈ T, Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :) ≠ ⊤) ∧
      interNum κ F P = ∑ z ∈ T, ((Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :)).toNat : ℤ) * deg z)
    (fun E hE _ => ?_) (fun C hC h₁ h₃ p₁ p₃ hs => ?_) (fun Z hZ ih G hG hs => ?_) F hF
  · have h0 : ∀ z, Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0 := fun z =>
      hz E z (by rw [support_eq_empty_iff.2 hE]; exact Set.notMem_empty _)
    refine ⟨fun z _ => by rw [h0]; simp, ?_⟩
    rw [interNum_eq_zero_of_isZero κ hE hL]
    simp [h0]
  · rw [support_eq_union_of_shortExact hC] at hs
    obtain ⟨a₁, b₁⟩ := p₁ (Set.subset_union_left.trans hs)
    obtain ⟨a₃, b₃⟩ := p₃ (Set.subset_union_right.trans hs)
    have := hC.mono_f
    have := hC.epi_g
    have hl (z : X) := Module.length_eq_add_of_exact (stalkLinear C.f z) (stalkLinear C.g z)
      (stalkLinear_injective _ z) (stalkLinear_surjective _ z) ((exact_iff_stalkLinear C).1 hC.exact z)
    refine ⟨fun z h => by rw [hl]; exact WithTop.add_ne_top.2 ⟨a₁ z h, a₃ z h⟩ , ?_⟩
    rw [interNum_shortExact hC hL (finiteCohTwists_of_isProjOver hf _ hp) (finiteCohTwists_of_isProjOver hf _ hp),
      b₁, b₃, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z h => ?_
    rw [hl, ENat.toNat_add (a₁ z h) (a₃ z h)]
    push_cast
    ring
  · have := isIntegral_red hZ
    letI := algebraΓAlong κ (redι Z)
    have hi := appTop_algebraMap_along κ (redι Z)
    have hpZ : IsProjOver (strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hsub : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ Z := fun x hx =>
      range_redι Z ▸ range_of_mem_support_push _ G hx
    set ξ := redι Z (genericPoint _) with hξ
    have hcl : closure {ξ} = (Z : Set X) := by
      have h₁ := (genericPoint_spec _).image (redι Z).continuous
      rw [Set.image_univ, range_redι, Z.isClosed.closure_eq] at h₁
      exact h₁.def
    by_cases hr : genRank G = 0
    · have hFQ : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
        ⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward (redι Z) _ hV
          (hF := QCoh.finite_sections G (hV.preimage (redι Z)))⟩
      refine ih _ hFQ ⟨hsub, fun hle => ?_⟩ hs
      exact genRank_eq_zero_iff.1 hr ((mem_support_push _ G _).1 (hle (hcl ▸ subset_closure rfl)))
    have hξS : ξ ∈ S := hs ((mem_support_push _ G _).2 (by_contra fun h => hr (genRank_eq_zero_iff.2 h)))
    have hdZ := topologicalKrullDim_red Z
    have hPZ : ∀ j, ((P j).pull (redι Z)).IsLB := fun j => LB.isLB_pull (hL j) _
    have hle : topologicalKrullDim (Z : Set X) ≤ d := by
      by_cases h : ξ ∈ T
      · exact (hcl ▸ hT ξ h).le
      · exact (hcl ▸ hS ξ hξS h).le
    have hoff : ∀ z ∈ T, z ≠ ξ → z ∉ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
      intro z hzT hne hzs
      have hzZ := hsub hzs
      have hsp : ξ ⤳ z := specializes_iff_mem_closure.2 (hcl ▸ hzZ)
      have h1 := topologicalKrullDim_add_one_le (s := closure {z}) isClosed_closure Z.isClosed fun x hx =>
        ⟨ξ, hcl ▸ subset_closure rfl, fun h => hne (hsp.antisymm (specializes_iff_mem_closure.2 h)).eq.symm,
          hsp.trans (specializes_iff_mem_closure.2 hx)⟩
      rw [hT z hzT] at h1
      have h4 : d + 1 ≤ d := by exact_mod_cast h1.trans hle
      omega
    have hlen : Module.length (X.presheaf.stalk ξ) (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk ξ :) =
        genRank G := (length_push _ G _).trans (Module.length_eq_finrank _ _)
    rw [interNum_pushforward_of_isClosedImmersion hi G hL]
    refine ⟨fun z h => ?_, ?_⟩
    · by_cases e : z = ξ
      · subst e; rw [hlen]; exact ENat.coe_ne_top _
      · rw [hz _ z (hoff z h e)]; simp
    · by_cases h : ξ ∈ T
      · rw [Finset.sum_eq_single ξ (fun z hzT e => by rw [hz _ z (hoff z hzT e)]; simp) (fun h' => absurd h h'),
          hlen, interNum_of_genRank_eq hpZ (hdZ.le.trans hle) hPZ _ G rfl, hdeg _ (redι Z) hi h, ENat.toNat_coe]
      · rw [Finset.sum_eq_zero fun z hzT => by rw [hz _ z (hoff z hzT fun e => h (e ▸ hzT))]; simp]
        refine interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ _) G hpZ ?_ hPZ
        rw [Fintype.card_fin]
        exact (QCoh.suppDim_le G).trans_lt (hdZ.trans_lt (hcl ▸ hS ξ hξS h))

end ChowFormHeightComparison₂.CF.V
end
end

section
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

section Alg

variable {κ Ω : Type} [Field κ] [Field Ω] [Algebra κ Ω] {m : ℕ}

theorem ker_aeval_eq (τ : Fin m → Ω) (k : Fin m) (hk : τ k = 1) :
    RingHom.ker (aeval τ : MvPolynomial (Fin m) κ →ₐ[κ] Ω) = GlobalTheory.CompHt.coneIdeal κ τ ⊔ Ideal.span {X k - 1} := by
  have hcomp : ∀ g : MvPolynomial (Fin m) κ, aeval τ g =
      ∑ d ∈ Finset.range (g.totalDegree + 1), aeval τ (homogeneousComponent d g) := by
    intro g
    conv_lhs => rw [← sum_homogeneousComponent g]
    rw [map_sum]
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    set N := g.totalDegree
    set h := ∑ d ∈ Finset.range (N + 1), X k ^ (N - d) * homogeneousComponent d g with hh
    have hhom : h.IsHomogeneous N := by
      apply IsHomogeneous.sum
      intro d hd
      have hdN : N - d + d = N := by
        have := Finset.mem_range.mp hd
        omega
      have := (isHomogeneous_X_pow (R := κ) k (N - d)).mul (homogeneousComponent_isHomogeneous d g)
      rwa [hdN] at this
    have hh0 : aeval τ h = 0 := by
      simp only [hh, map_sum, map_mul, map_pow, aeval_X, hk, one_pow, one_mul]
      rw [← hcomp]
      exact hg
    have hdiff : g - h ∈ Ideal.span {X k - 1} := by
      have hg' : g = ∑ d ∈ Finset.range (N + 1), homogeneousComponent d g :=
        (sum_homogeneousComponent g).symm
      have : g - h = ∑ d ∈ Finset.range (N + 1), (1 - X k ^ (N - d)) * homogeneousComponent d g := by
        rw [hh, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
        conv_lhs => rw [hg']
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
      rw [this]
      refine Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_
      rw [Ideal.mem_span_singleton]
      have := sub_dvd_pow_sub_pow (X k : MvPolynomial (Fin m) κ) 1 (N - d)
      rw [one_pow] at this
      rw [← neg_sub (X k ^ (N - d)) (1 : MvPolynomial (Fin m) κ)]
      exact dvd_neg.mpr this
    have hcone : h ∈ GlobalTheory.CompHt.coneIdeal κ τ :=
      (GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous τ hhom).mpr hh0
    have : g = h + (g - h) := by ring
    rw [this]
    exact Submodule.add_mem_sup hcone hdiff
  · refine sup_le ?_ ?_
    · intro g hg
      rw [GlobalTheory.CompHt.mem_coneIdeal_iff] at hg
      rw [RingHom.mem_ker, hcomp]
      exact Finset.sum_eq_zero fun d _ => hg d
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show _ ∈ RingHom.ker _
      rw [RingHom.mem_ker]
      simp [hk]

theorem le_ker_constantCoeff {P : Ideal (MvPolynomial (Fin m) κ)} (h : IsProjPrime P) :
    P ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := by
  intro f hf
  rw [RingHom.mem_ker]
  by_contra hne
  have h0 := h.isHomog f hf 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact h.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hne).map C))

end Alg

variable {Z : Scheme.{0}} {B : LB Z} {m : ℕ}

theorem evaluation_resG {U V : Z.Opens} (h : V ≤ U) (z : Z) (hz : z ∈ V) (a : Γ(Z, U)) :
    Z.evaluation V z hz (resG Z h a) = Z.evaluation U z (h hz) a := by
  simp only [resG, ← Scheme.germ_residue, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply (Z.presheaf.map (homOfLE h).op), TopCat.Presheaf.germ_res]

theorem evaluation_algX {R : Type} [CommRing R] (p : Z ⟶ Sp R) {U : Z.Opens} (z : Z) (hz : z ∈ U) (r : R) :
    Z.evaluation U z hz (algX p U r) = Z.evaluation ⊤ z trivial (algX p ⊤ r) := by
  rw [← TopForm.resG_comp_algX p (le_top : U ≤ ⊤), RingHom.comp_apply, evaluation_resG]

variable {κ : Type} [Field κ] {p : Z ⟶ Sp κ} {s : Fin m → B.Sec}

theorem ptIdeal_eq_coneIdeal (hB : B.IsLB) {k : Fin m} (t : Fin m → Γ(Z, nonzeroLocus (s k)))
    (ht : ∀ j i, resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s j).f i) =
      resG Z (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) (t j) *
        resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s k).f i))
    (z : Z) (hz : z ∈ nonzeroLocus (s k)) :
    letI := ((Z.evaluation ⊤ z trivial).hom.comp (algX p ⊤)).toAlgebra
    ptIdeal p s z = GlobalTheory.CompHt.coneIdeal κ (fun j => Z.evaluation _ z hz (t j)) ∧ Z.evaluation _ z hz (t k) = 1 := by
  letI alg : Algebra κ (Z.residueField z) := ((Z.evaluation ⊤ z trivial).hom.comp (algX p ⊤)).toAlgebra
  set y : Fin m → Z.residueField z := fun j => Z.evaluation _ z hz (t j) with hy
  have key : ∀ i (hi : z ∈ B.U i) j, Z.evaluation (B.U i) z hi ((s j).f i) =
      y j * Z.evaluation (B.U i) z hi ((s k).f i) := by
    intro i hi j
    have := congrArg (fun x => Z.evaluation (nonzeroLocus (s k) ⊓ B.U i) z ⟨hz, hi⟩ x) (ht j i)
    dsimp only at this
    rw [map_mul] at this
    have e1 := evaluation_resG (Z := Z) (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) z ⟨hz, hi⟩ ((s j).f i)
    have e2 := evaluation_resG (Z := Z) (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) z
      ⟨hz, hi⟩ (t j)
    have e3 := evaluation_resG (Z := Z) (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) z ⟨hz, hi⟩ ((s k).f i)
    simp only [hy]
    rw [← e1, ← e2, ← e3]
    exact this
  have hcone : ∀ i (hi : z ∈ B.U i), coneHom p s z i hi =
      (Polynomial.aeval (Polynomial.C (Z.evaluation (B.U i) z hi ((s k).f i)) * Polynomial.X)).toRingHom.comp
        (GlobalTheory.CompHt.coneMap κ y).toRingHom := by
    intro i hi
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneHom, GlobalTheory.CompHt.coneMap, evaluation_algX, Polynomial.algebraMap_apply,
        RingHom.algebraMap_toAlgebra]
    · intro j
      simp [coneHom, GlobalTheory.CompHt.coneMap, key i hi j]
      ring
  have hz' := hz
  simp only [nonzeroLocus, Opens.mem_iSup] at hz'
  obtain ⟨i₀, hb⟩ := hz'
  have hi₀ : z ∈ B.U i₀ := Z.basicOpen_le _ hb
  have ha : Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) ≠ 0 :=
    by
    rw [Ne, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]
    exact hb
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro g hg
    have hg' := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hg i₀) hi₀
    rw [RingHom.mem_ker, hcone i₀ hi₀] at hg'
    show g ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at hg'
    rw [← Polynomial.comp_eq_aeval, Polynomial.comp_eq_zero_iff] at hg'
    rcases hg' with h | ⟨_, h⟩
    · exact h
    · exfalso
      have := congrArg (fun q => Polynomial.coeff q 1) h
      simp at this
      exact this hb
  · intro g hg
    have hg0 : GlobalTheory.CompHt.coneMap κ y g = 0 := hg
    simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker]
    intro i hi
    rw [hcone i hi]
    simp [hg0]
  · have := key i₀ hi₀ k
    have h1 : (1 : Z.residueField z) * Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) =
        y k * Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) := by
      rw [one_mul]
      exact this
    exact (mul_right_cancel₀ ha h1).symm

theorem isComb_single {R : Type} [CommRing R] (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (k : Fin m) :
    IsComb p s (Pi.single k 1) (s k) := by
  intro i
  simp [Pi.single_apply, apply_ite, ite_mul]

theorem linForm_single {R : Type} [CommRing R] (k : Fin m) :
    GroundTheory.Heights₂.Heights.linForm (Pi.single k (1 : R)) = X k := by
  simp [GroundTheory.Heights₂.Heights.linForm, Pi.single_apply]

variable [IsIntegral Z]

theorem dim_add_one_le (h1 : StPts) (hE : Emb p s) :
    topologicalKrullDim Z + 1 ≤ ringKrullDim (MvPolynomial (Fin m) κ ⧸ ptIdeal p s (genericPoint Z)) := by
  classical
  set I := ptIdeal p s (genericPoint Z) with hIdef
  obtain ⟨hprime, hspec, -, -⟩ := h1 κ Z p B m s hE
  let gen : IrreducibleCloseds Z → Z := fun S => S.isIrreducible.genericPoint
  have hgen : ∀ S : IrreducibleCloseds Z, closure {gen S} = (S : Set Z) := by
    intro S
    have := S.isIrreducible.isGenericPoint_genericPoint_closure
    rw [S.isClosed.closure_eq] at this
    exact this
  have hle : ∀ S T : IrreducibleCloseds Z,
      (T : Set Z) ⊆ S ↔ ptIdeal p s (gen S) ≤ ptIdeal p s (gen T) := by
    intro S T
    rw [← hspec (gen S) (gen T), specializes_iff_closure_subset, hgen, hgen]
  have hI : ∀ S : IrreducibleCloseds Z, I ≤ ptIdeal p s (gen S) := fun S =>
    (hspec _ _).mp ((genericPoint_spec Z).specializes (Set.mem_univ _))
  have hM : ∀ S : IrreducibleCloseds Z,
      ptIdeal p s (gen S) < RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := by
    intro S
    refine lt_of_le_of_ne (le_ker_constantCoeff (hprime _)) fun h => ?_
    obtain ⟨j, hj⟩ := (hprime (gen S)).isRelevant
    apply hj
    rw [h, RingHom.mem_ker, constantCoeff_X]
  have hMI : I ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) :=
    le_ker_constantCoeff (hprime _)
  haveI : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
  let g : WithTop (IrreducibleCloseds Z)ᵒᵈ →
      PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin m) κ) (I : Set (MvPolynomial (Fin m) κ)) :=
    fun x => WithTop.recTopCoe
      ⟨⟨RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ), RingHom.ker_isPrime _⟩,
        (PrimeSpectrum.mem_zeroLocus _ _).mpr hMI⟩
      (fun S => ⟨⟨ptIdeal p s (gen (OrderDual.ofDual S)), (hprime _).isPrime⟩,
        (PrimeSpectrum.mem_zeroLocus _ _).mpr (hI _)⟩) x
  have hg : StrictMono g := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe S =>
      induction b using WithTop.recTopCoe with
      | top =>
        show (⟨ptIdeal p s (gen (OrderDual.ofDual S)), _⟩ : PrimeSpectrum _) <
          ⟨RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ), _⟩
        exact hM _
      | coe T =>
        rw [WithTop.coe_lt_coe] at hab
        have hab' : OrderDual.ofDual T < OrderDual.ofDual S := hab
        show (⟨ptIdeal p s (gen (OrderDual.ofDual S)), _⟩ : PrimeSpectrum _) <
          ⟨ptIdeal p s (gen (OrderDual.ofDual T)), _⟩
        refine lt_of_le_not_ge ((hle _ _).mp hab'.le) fun h => ?_
        exact hab'.not_ge ((hle _ _).mpr h)
  calc topologicalKrullDim Z + 1 = Order.krullDim (WithTop (IrreducibleCloseds Z)ᵒᵈ) := by
        rw [Order.krullDim_WithTop, Order.krullDim_orderDual]
        rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin m) κ) (I : Set _)) :=
        Order.krullDim_le_of_strictMono g hg
    _ = ringKrullDim (MvPolynomial (Fin m) κ ⧸ I) := (ringKrullDim_quotient I).symm

private theorem algX_strHom_top {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] :
    algX (strHom κ Z) ⊤ = algebraMap κ Γ(Z, ⊤) := by
  ext r
  rw [algebraMap_eq_strHom]
  simp [algX, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

private theorem evaluation_genericPoint_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    Z.evaluation U (genericPoint Z) hU a = 0 ↔ a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  constructor
  · intro h
    by_contra ha
    apply h
    have hne : Z.basicOpen a ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    show genericPoint Z ∈ (Z.basicOpen a : Set Z)
    rw [(genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen, Set.univ_inter]
    rwa [Ne, ← Opens.not_nonempty_iff_eq_bot, not_not] at hne
  · rintro rfl
    simp

private theorem resG_bijective_of_eq_top {Z : Scheme.{0}} {V : Z.Opens} (hV : V = ⊤) :
    Function.Bijective (resG Z (le_top : V ≤ ⊤)) := by
  subst hV
  have : (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  simp only [resG, this, op_id, CategoryTheory.Functor.map_id]
  exact Function.bijective_id

theorem finrank_eq_of_dim_zero [Algebra κ Γ(Z, ⊤)] {s : Fin m → B.Sec} (hE : Emb (strHom κ Z) s)
    (hd : topologicalKrullDim Z ≤ 0) {k : Fin m} (hk : genericPoint Z ∈ nonzeroLocus (s k)) :
    Module.finrank κ (MvPolynomial (Fin m) κ ⧸ (ptIdeal (strHom κ Z) s (genericPoint Z) ⊔ Ideal.span {X k - 1})) =
      Module.finrank κ Γ(Z, ⊤) := by
  classical
  set η := genericPoint Z
  have hall : ∀ z : Z, z = η := by
    intro z
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hd
    let Sz : IrreducibleCloseds Z := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let U : IrreducibleCloseds Z := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have h1 : Sz = U := (hmax Sz).eq_of_le (show (Sz : Set Z) ⊆ U from Set.subset_univ _)
    have h2 : IsGenericPoint z Set.univ := by
      have := congrArg (fun S : IrreducibleCloseds Z => (S : Set Z)) h1
      exact this
    exact h2.eq (genericPoint_spec Z)
  have hW : nonzeroLocus (s k) = ⊤ := eq_top_iff.mpr fun z _ => (hall z) ▸ hk
  obtain ⟨-, t, hsurj, ht⟩ := hE.chart k
  obtain ⟨hJ, htk⟩ := ptIdeal_eq_coneIdeal (p := strHom κ Z) hE.isLB t ht η hk
  letI alg : Algebra κ (Z.residueField η) :=
    ((Z.evaluation ⊤ η trivial).hom.comp (algX (strHom κ Z) ⊤)).toAlgebra
  have hinj : Function.Injective (Z.evaluation (nonzeroLocus (s k)) η hk).hom :=
    (injective_iff_map_eq_zero _).mpr fun a ha => (evaluation_genericPoint_eq_zero_iff hk a).mp ha
  have hker : RingHom.ker (eval₂Hom (algX (strHom κ Z) (nonzeroLocus (s k))) t) =
      ptIdeal (strHom κ Z) s η ⊔ Ideal.span {X k - 1} := by
    rw [hJ, ← ker_aeval_eq _ k htk]
    have hcomp : (Z.evaluation (nonzeroLocus (s k)) η hk).hom.comp (eval₂Hom (algX (strHom κ Z) (nonzeroLocus (s k))) t) =
        (aeval (fun j => Z.evaluation (nonzeroLocus (s k)) η hk (t j)) :
          MvPolynomial (Fin m) κ →ₐ[κ] Z.residueField η).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [evaluation_algX, RingHom.algebraMap_toAlgebra]
      · intro j
        simp
    rw [← RingHom.ker_comp_of_injective _ hinj, hcomp]
    rfl
  let ρ : Γ(Z, ⊤) ≃+* Γ(Z, nonzeroLocus (s k)) :=
    RingEquiv.ofBijective (resG Z (le_top : nonzeroLocus (s k) ≤ ⊤)) (resG_bijective_of_eq_top hW)
  let φ : (MvPolynomial (Fin m) κ ⧸ (ptIdeal (strHom κ Z) s η ⊔ Ideal.span {X k - 1})) ≃+* Γ(Z, ⊤) :=
    (Ideal.quotEquivOfEq hker.symm).trans ((RingHom.quotientKerEquivOfSurjective hsurj).trans ρ.symm)
  have hφ : ∀ c : κ, φ (algebraMap κ _ c) = algebraMap κ Γ(Z, ⊤) c := by
    intro c
    rw [← algX_strHom_top]
    simp only [φ, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp only [ρ, RingEquiv.ofBijective_apply, MvPolynomial.algebraMap_eq, eval₂Hom_C]
    rw [← TopForm.resG_comp_algX (strHom κ Z) (le_top : nonzeroLocus (s k) ≤ ⊤), RingHom.comp_apply]
  exact (AlgEquiv.ofRingEquiv (f := φ) hφ).toLinearEquiv.finrank_eq

end ChowFormHeightComparison₂.CF.V
end
end

section
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

open GroundTheory.Heights₂.Heights.ObjectsChow (ChowDegreeSection.Statement ChowDegreeClosedPoint.Statement)

theorem dim_closure_add_one_le {Z : Scheme.{0}} {z z' : Z} (h : z' ⤳ z) (hne : z ≠ z') :
    topologicalKrullDim (closure {z} : Set Z) + 1 ≤ topologicalKrullDim (closure {z'} : Set Z) :=
  topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun x hx =>
    ⟨z', subset_closure rfl, fun h' => hne (h.antisymm (specializes_iff_mem_closure.2 h')).eq.symm,
      h.trans (specializes_iff_mem_closure.2 hx)⟩

theorem dim_closure_eq {Y Z : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ Z) [IsClosedImmersion i] :
    topologicalKrullDim (closure {i (genericPoint Y)} : Set Z) = topologicalKrullDim Y := by
  have h₁ := (genericPoint_spec Y).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  exact topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm

theorem length_cut {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] {B : LB Z} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint Z ∈ nonzeroLocus s) {z : Z} (hz : (divOfSec hB s hs).mult z ≠ 0) :
    ((Module.length (Z.presheaf.stalk z) ((cut (GlobalTheory.structureModule Z) hB s).presheaf.stalk z :)).toNat : ℤ) =
      (divOfSec hB s hs).mult z := by
  obtain ⟨i, hi⟩ := LB.mem_of_cover hB z
  obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv (GlobalTheory.structureModule Z) hB s i hi
  rw [mult_divOfSec (CartierDiv.coheight_eq_one_of_mult_ne_zero hz) hi, ← q.length_eq]
  refine congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (Submodule.Quotient.equiv _ _ (QCoh.structureModuleStalkEquiv z) ?_).length_eq
  rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range, ← Submodule.ideal_span_singleton_smul,
    smul_eq_mul, Ideal.mul_top]

variable {κ : Type} [Field κ] {m : ℕ}

theorem isRelevant_of_dim {W : Ideal (MvPolynomial (Fin m) κ)}
    (hW : W ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ))
    (hd : ringKrullDim (MvPolynomial (Fin m) κ ⧸ W) ≠ 0) : IsRelevant W := by
  by_contra h
  have hX : ∀ j, X j ∈ W := fun j => by_contra fun hj => h ⟨j, hj⟩
  have key (g : MvPolynomial (Fin m) κ) : g - C (constantCoeff g) ∈ W := by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add a b ha hb =>
      have := W.add_mem ha hb
      rwa [sub_add_sub_comm, ← map_add, ← map_add] at this
    | mul_X a j _ => simpa using W.mul_mem_left a (hX j)
  have e : W = RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := le_antisymm hW fun g hg => by
    have := key g
    rwa [(RingHom.mem_ker).1 hg, map_zero, sub_zero] at this
  have : W.IsMaximal := e ▸ RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩
  exact hd (ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient W).1 this))

theorem field_case (h1 : StPts) (h2 : StPull) (h3 : StDiv) (hS : ChowDegreeSection.Statement)
    (hP : ChowDegreeClosedPoint.Statement) [PerfectField κ] (e : ℕ) :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)] (B : LB Z) (s : Fin m → B.Sec),
      IsProjOver (strHom κ Z) → Emb (strHom κ Z) s →
      ringKrullDim (MvPolynomial (Fin m) κ ⧸ ptIdeal (strHom κ Z) s (genericPoint Z)) = (e + 1 : ℕ) →
      topologicalKrullDim Z = e ∧
        topSelfIntersection κ B e = chowDegree (ptIdeal (strHom κ Z) s (genericPoint Z)) (e + 1) := by
  classical
  have hC := GroundTheory.Heights₂.Heights.ConeDimComponent.proof_closed
  induction e with
  | zero =>
    intro Z _ _ B s hp hE hd
    have := isNoetherian_of_isProjOver hp
    obtain ⟨a, b, c, d⟩ := h1 κ Z _ B m s hE
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hE.cover.ge (Opens.mem_top (genericPoint Z)))
    have hX := (d _ _ (isComb_single _ s k) _).1 hk
    rw [linForm_single] at hX
    have h0 : topologicalKrullDim Z ≤ 0 := ENat.WithBot.add_le_add_one_right_iff.1
      ((dim_add_one_le h1 hE).trans (hd.trans (by simp)).le)
    have : Nonempty (IrreducibleCloseds Z) := ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
    refine ⟨le_antisymm h0 Order.krullDim_nonneg, ?_⟩
    rw [hP κ m _ k (a _) hd hX, finrank_eq_of_dim_zero hE h0 hk, topSelf_def, interNum_of_isEmpty,
      chi_eq_hdim_zero_of_suppDim_le_zero κ (QCoh.suppDim_structureModule.trans_le h0),
      ← ((coh.zeroUnitEquiv Z).restrictScalars κ).finrank_eq]
    rfl
  | succ e ih =>
    intro Z _ _ B s hp hE hd
    have := isNoetherian_of_isProjOver hp
    obtain ⟨a, b, c, d⟩ := h1 κ Z _ B m s hE
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hE.cover.ge (Opens.mem_top (genericPoint Z)))
    have hu := isComb_single (strHom κ Z) s k
    have hX := (d _ _ hu _).1 hk
    obtain ⟨d₁, d₂⟩ := h3 κ Z _ B m s hE _ _ hu hk
    have hsec := hS κ m e _ _ (a _) hd hX
    have hcomp := fun W => hC κ m (e + 1) _ W _ (a _) hd hX
    generalize (Pi.single k 1 : Fin m → κ) = u at *
    set P := ptIdeal (strHom κ Z) s with hPdef
    set J := P (genericPoint Z) ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u} with hJ
    let T := (divOfSec hE.isLB (s k) hk).finite_support_mult.toFinset
    have hT (z : Z) : z ∈ T ↔ (divOfSec hE.isLB (s k) hk).mult z ≠ 0 := Set.Finite.mem_toFinset _
    have inj {z z' : Z} (h : P z = P z') : z = z' := (((b _ _).2 h.le).antisymm ((b _ _).2 h.ge)).eq
    have hex (W) (hW : W ∈ relComps J) : ∃ z ∈ T, P z = W := by
      obtain ⟨z, rfl⟩ := c W (hcomp W hW).1 (le_sup_left.trans hW.1.1.2)
      exact ⟨z, (hT z).2 ((d₁ z).2 hW), rfl⟩
    have key : ∀ (Y : Scheme.{0}) (i : Y ⟶ Z) [IsClosedImmersion i] [IsIntegral Y] [Algebra κ Γ(Y, ⊤)],
        (∀ r : κ, i.appTop (algebraMap κ Γ(Z, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) → i (genericPoint Y) ∈ T →
        topologicalKrullDim Y = e ∧ topSelfIntersection κ (B.pull i) e = chowDegree (P (i (genericPoint Y))) (e + 1) := by
      intro Y i _ _ _ hi hz
      obtain ⟨E', pt', -⟩ := h2 κ Z Y _ B m s i hE
      have hp' := ProjSpace.isProjOver_comp_of_isClosedImmersion i hp
      rw [comp_strHom hi] at E' pt' hp'
      have := ih Y _ _ hp' E' (by rw [pt']; exact (hcomp _ ((d₁ _).1 ((hT _).1 hz))).2)
      rwa [pt'] at this
    have hTd : ∀ z ∈ T, topologicalKrullDim (closure {z} : Set Z) = e := fun z hz => by
      obtain ⟨Y, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      letI := algebraΓAlong κ i
      exact (dim_closure_eq i).trans (key Y i (appTop_algebraMap_along κ i) hz).1
    have hmem (z : Z) (hz : z ∉ nonzeroLocus (s k)) : J ≤ P z :=
      sup_le ((b _ _).1 (genericPoint_specializes z))
        ((Ideal.span_singleton_le_iff_mem _).2 (by_contra fun h => hz ((d _ _ hu z).2 h)))
    have hSd : ∀ z ∈ ((nonzeroLocus (s k) : Set Z)ᶜ), z ∉ T → topologicalKrullDim (closure {z} : Set Z) < e := by
      intro z hz hzT
      have := (a z).isPrime
      obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (hmem z hz)
      obtain ⟨j, hj⟩ := (a z).isRelevant
      obtain ⟨z', hz', rfl⟩ := hex W ⟨hW, j, fun h => hj (hle h)⟩
      have h4 := dim_closure_add_one_le ((b _ _).2 hle) fun h => hzT (h ▸ hz')
      rw [hTd z' hz'] at h4
      by_contra hc
      rw [not_lt] at hc
      have h5 : e + 1 ≤ e := by exact_mod_cast (add_le_add_left hc 1).trans h4
      omega
    refine ⟨le_antisymm (ENat.WithBot.add_le_add_one_right_iff.1
      ((dim_add_one_le h1 hE).trans (hd.trans (Nat.cast_succ _)).le)) ?_, ?_⟩
    · have hm : J ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) :=
        sup_le (le_ker_constantCoeff (a _)) ((Ideal.span_singleton_le_iff_mem _).2 (by
          simp [RingHom.mem_ker, GroundTheory.Heights₂.Heights.linForm]))
      have := RingHom.ker_isPrime (constantCoeff : MvPolynomial (Fin m) κ →+* κ)
      have := (a (genericPoint Z)).isPrime
      obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hm
      have h4 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup κ hX hW
      obtain ⟨z, hz, rfl⟩ := hex W ⟨hW, isRelevant_of_dim hle fun h0 => by
        rw [h0, hd] at h4
        have h5 : 0 + 1 = e + 1 + 1 := by exact_mod_cast h4
        omega⟩
      have h5 := dim_closure_add_one_le (genericPoint_specializes z) fun h =>
        hX (h ▸ hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
      rw [hTd z hz] at h5
      exact (Nat.cast_succ e).le.trans (h5.trans (topologicalKrullDim_subspace_le Z _))
    · have hf := algebraMap_eq_strHom κ Z
      have := (mono_cutHom_structureModule_iff hE.isLB (s k)).2 hk
      have e₁ : (fun _ : Fin (e + 1) => B) = (Fin.cons B (fun _ => B) : Fin (e + 1) → LB Z) :=
        funext (Fin.cases rfl fun _ => rfl)
      have e₂ := (interNum_eq_sum hp (P := fun _ : Fin e => B) (fun _ => hE.isLB) _ T
        (fun z => chowDegree (P z) (e + 1)) hTd hSd (fun Y i _ _ _ hi hz => (key Y i hi hz).2)
        (cut (GlobalTheory.structureModule Z) hE.isLB (s k)) inferInstance
        (by rw [support_cut]; exact fun x hx => hx.2)).2
      rw [topSelf_def, e₁, interNum_cons_eq_interNum_cut hE.isLB (s k) (fun _ => hE.isLB)
        (finiteCohTwists_of_isProjOver hf _ hp), e₂]
      show _ = ((chowDegree _ (e + 2) : ℕ) : ℤ)
      rw [hsec, Finsupp.sum, Nat.cast_sum]
      have hval (z : Z) (hz : z ∈ T) : ((divCycle (P (genericPoint Z)) u (P z) : ℕ) : ℤ) =
          (divOfSec hE.isLB (s k) hk).mult z := by
        rw [d₂ z ((hT z).1 hz), divCycle, GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply,
          if_pos ((d₁ z).1 ((hT z).1 hz))]
      refine Finset.sum_bij (fun z _ => P z) (fun z hz => ?_) (fun _ _ _ _ h => inj h) (fun W hW => ?_)
        fun z hz => ?_
      · rw [Finsupp.mem_support_iff, ← Nat.cast_ne_zero (R := ℤ), hval z hz]
        exact (hT z).1 hz
      · obtain ⟨z, hz, rfl⟩ := hex W (by
          by_contra h
          rw [Finsupp.mem_support_iff, divCycle, GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply,
            if_neg h] at hW
          exact hW rfl)
        exact ⟨z, hz, rfl⟩
      · rw [length_cut hE.isLB (s k) hk ((hT z).1 hz), Nat.cast_mul, hval z hz]

end ChowFormHeightComparison₂.CF.V
end
end

section
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Short.ChowClosing in
theorem chowDegreeSection : ObjectsChow.ChowDegreeSection.Statement :=
  ObjectsChow.ChowDegreeSection.proof
    (chowFormSectionPerfect_of
      (chowFormSectionAlgClosed_of
        (SectionOrderAlgClosed.proof IncIdealBelow.full SpecFirstMemIncIdeal.full
          chartChoiceAlgClosed_closed Vertical.SpecFirstNeField.full
          LocalizationPrimeDVR.full EmultiplicityOrd.full ChartFinite.full ChartLocDomain.full
          GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartNormAlgClosed
          chartLengthAlgClosed_closed LengthQuotientDet.full))
      sectionCycleReduced_closed MinimalPrimeComap.proof
      (FundCycleBaseChange.proof MinimalPrimeComap.proof))

theorem algX_strHom {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] :
    algX (strHom κ Z) ⊤ = algebraMap κ Γ(Z, ⊤) := by
  ext r
  rw [algebraMap_eq_strHom]
  simp [algX, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

section Base

variable {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}} {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S}
  {B : LB Z} {m : ℕ} {s : Fin m → B.Sec}

theorem algX_eq_comp (h : algX p ⊤ = (algX q ⊤).comp π) (U : Z.Opens) : algX p U = (algX q U).comp π := by
  rw [← TopForm.resG_comp_algX p (le_top : U ≤ ⊤), h, ← RingHom.comp_assoc, TopForm.resG_comp_algX]

private theorem eq_of_algX_top_eq {R : Type} [CommRing R] {Z : Scheme.{0}} {f g : Z ⟶ Sp R}
    (h : algX f ⊤ = algX g ⊤) : f = g := by
  have hf : ∀ φ : Z ⟶ Sp R,
      algX φ ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ.appTop).hom := by
    intro φ
    ext r
    simp [algX, Scheme.Hom.appLE, Scheme.Hom.appTop]
    rfl
  rw [hf, hf] at h
  have e : f.appTop = g.appTop := by
    simpa using CommRingCat.hom_ext h
  haveI : Mono (Sp R).toSpecΓ := by
    rw [← SpecMap_ΓSpecIso_hom]
    infer_instance
  rw [← cancel_mono (Sp R).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

theorem eq_comp_spMap (h : algX p ⊤ = (algX q ⊤).comp π) : q ≫ spMap π = p := by
  apply eq_of_algX_top_eq
  rw [h]
  ext r
  have key := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  simp only [algX, Scheme.Hom.appLE, spMap, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply,
    RingHom.coe_comp, Function.comp_apply]
  rw [key]
  rfl

theorem emb_base (h : algX p ⊤ = (algX q ⊤).comp π) (hE : Emb p s) : Emb q s := by
  obtain ⟨hLB, hcov, hch⟩ := hE
  refine ⟨hLB, hcov, fun k => ?_⟩
  obtain ⟨ha, t, hs, hr⟩ := hch k
  refine ⟨ha, t, fun x => ?_, hr⟩
  obtain ⟨P, rfl⟩ := hs x
  refine ⟨MvPolynomial.map π P, ?_⟩
  rw [algX_eq_comp h]
  simp [MvPolynomial.eval₂_map]

theorem ptIdeal_base (h : algX p ⊤ = (algX q ⊤).comp π) (z : Z) :
    ptIdeal p s z = (ptIdeal q s z).comap (MvPolynomial.map π) := by
  simp only [ptIdeal, Ideal.comap_iInf, RingHom.comap_ker]
  refine iInf_congr fun i => iInf_congr fun hi => congrArg _ ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_
  · simp [coneHom, algX_eq_comp h]
  · simp [coneHom]

end Base

end ChowFormHeightComparison₂.CF.V

namespace ChowFormHeightComparison₂.CF

private theorem evaluation_genericPoint_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    Z.evaluation U (genericPoint Z) hU a = 0 ↔ a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  constructor
  · intro h
    by_contra ha
    apply h
    have hne : Z.basicOpen a ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    show genericPoint Z ∈ (Z.basicOpen a : Set Z)
    rw [(genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen, Set.univ_inter]
    rwa [Ne, ← Opens.not_nonempty_iff_eq_bot, not_not] at hne
  · rintro rfl
    simp

private theorem C_mem_ptIdeal_genericPoint_iff {R : Type} [CommRing R] {Z : Scheme.{0}} [IsIntegral Z] {B : LB Z} {m : ℕ}
    (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (hB : B.IsLB) (r : R) :
    MvPolynomial.C r ∈ ptIdeal p s (genericPoint Z) ↔ algX p ⊤ r = 0 := by
  have hη : genericPoint Z ∈ ⨆ i, B.U i := by
    rw [hB.cover]
    trivial
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.mp hη
  simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker, coneHom, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Polynomial.C_eq_zero]
  constructor
  · intro h
    have := h i₀ hi₀
    rw [V.evaluation_algX] at this
    exact (evaluation_genericPoint_eq_zero_iff _ _).mp this
  · intro h i hi
    rw [V.evaluation_algX, h]
    simp

private theorem isProjOver_of_surjective_base {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}}
    {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S} (hπ : Function.Surjective π)
    (hq : q ≫ spMap π = p) (hP : IsProjOver p) : IsProjOver q := by
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  let ι : Z ⟶ Limits.pullback p (spMap π) := Limits.pullback.lift (𝟙 Z) q (by simp [hq])
  have h1 : ι ≫ Limits.pullback.fst p (spMap π) = 𝟙 Z := Limits.pullback.lift_fst _ _ _
  have h2 : ι ≫ Limits.pullback.snd p (spMap π) = q := Limits.pullback.lift_snd _ _ _
  haveI : IsIso ι := ⟨⟨Limits.pullback.fst p (spMap π), h1, by
    rw [← cancel_mono (Limits.pullback.fst p (spMap π)), Category.assoc, h1]
    simp⟩⟩
  rw [← h2]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion ι (ProjSpace.isProjOver_pullback_snd π hP)

open V in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem stVert (h1 : StPts) (h2 : StPull) (h3 : StDiv) : StVert := by
  intro K _ _ Z _ p B m s v d hP hE hv hd
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set κ := v.asIdeal.ResidueField
  have hB := hE.isLB
  have hker : ∀ r, algX p ⊤ r = 0 ↔ r ∈ v.asIdeal := by
    intro r
    rw [← C_mem_ptIdeal_genericPoint_iff p s hB r, ← hv, Ideal.mem_comap]
  let e : (𝓞 K ⧸ v.asIdeal) ≃+* κ :=
    RingEquiv.ofBijective _ v.asIdeal.bijective_algebraMap_quotient_residueField
  let φ : κ →+* Γ(Z, ⊤) :=
    (Ideal.Quotient.lift v.asIdeal (algX p ⊤) fun r hr => (hker r).mpr hr).comp e.symm.toRingHom
  letI inst : Algebra κ Γ(Z, ⊤) := φ.toAlgebra
  refine ⟨inst, ?_⟩
  have hπ : algX p ⊤ = (algX (strHom κ Z) ⊤).comp (algebraMap (𝓞 K) κ) := by
    rw [V.algX_strHom]
    ext r
    show algX p ⊤ r = φ (algebraMap (𝓞 K) κ r)
    have hr : e.symm (algebraMap (𝓞 K) κ r) = Ideal.Quotient.mk v.asIdeal r := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hr,
      Ideal.Quotient.lift_mk]
  have hsurj : Function.Surjective (algebraMap (𝓞 K) κ) :=
    v.asIdeal.algebraMap_residueField_surjective
  have hEκ : Emb (strHom κ Z) s := V.emb_base hπ hE
  have hPκ : IsProjOver (strHom κ Z) := isProjOver_of_surjective_base hsurj (V.eq_comp_spMap hπ) hP
  have hred : reduceMod v (ptIdeal p s (genericPoint Z)) = ptIdeal (strHom κ Z) s (genericPoint Z) := by
    rw [V.ptIdeal_base hπ]
    exact Ideal.map_comap_of_surjective _ (MvPolynomial.map_surjective _ hsurj) _
  rw [hred]
  set J := ptIdeal (strHom κ Z) s (genericPoint Z)
  have hdimle : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) ≤ m := by
    refine (ringKrullDim_quotient_le J).trans ?_
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hdimge : ((d : WithBot ℕ∞) + 1) ≤ ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) := by
    have := V.dim_add_one_le h1 hEκ
    rwa [hd] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = n := by
    revert hdimle hdimge
    generalize ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = x
    intro hdimle hdimge
    induction x using WithBot.recBotCoe with
    | bot => simp at hdimge
    | coe y =>
      induction y using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞) := hdimle
        rw [WithBot.coe_le_coe, top_le_iff] at h'
        exact ENat.coe_ne_top m h'
      | coe n => exact ⟨n, rfl⟩
  have hnd : d + 1 ≤ n := by
    rw [hn] at hdimge
    exact_mod_cast hdimge
  have hn' : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = ↑(n - 1 + 1) := by
    rw [hn]
    congr 1
    omega
  obtain ⟨hZ, hdeg⟩ := V.field_case h1 h2 h3 V.chowDegreeSection
    GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ObjectsChow_ChowDegreeClosedPoint (n - 1) Z B s hPκ hEκ hn'
  have hnd' : n - 1 = d := by
    rw [hd] at hZ
    exact_mod_cast hZ.symm
  rw [← hnd']
  exact hdeg

end ChowFormHeightComparison₂.CF
end
end

section
namespace ChowFormHeightComparison₂.CF

open GroundTheory.Heights₂.Heights in
theorem chowFormHeight_of_arch (hA : StArch) (hM : MahlerSection.Statement) (hE : GlobalTheory.Published.ArExists) :
    PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  glue (stMain_of (stVert stPts stPull stDiv) hA
    (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full hM ChowFormBaseChange.full BaseChangeAvoid.full)
    ChowFormSection.full ChowHeightMul.full ProjPrimeHasPoint.full) stModel stForm hE

end ChowFormHeightComparison₂.CF
end
