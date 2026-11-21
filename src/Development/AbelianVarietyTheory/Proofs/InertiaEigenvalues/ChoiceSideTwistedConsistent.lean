import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTuple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLvlOp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftTwistLevelFormEqUnitMulClassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometriesObj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingCompatAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateFunctionAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixBaseOfFixingFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsConjugateTwistsConjugateExpansions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitCardResidueFieldOffExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalRowSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingOkClassAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRing
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormMemMtLatIff
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsFockFormEqOfMemMtLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralForms

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceSmall

section BaseChange

variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}

theorem map_mem_nabAtr (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsLattice E M) {x : VV K₀ lam} (hx : x ∈ nabAtr emb lam M) :
    (⟨MvPolynomial.map f x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam _ x.2⟩ : VV K lam) ∈
      nabAtr (fun τ => f.comp (emb τ)) lam M := by
  classical
  unfold nabAtr nabK at hx ⊢
  rw [Submodule.mem_comap] at hx ⊢
  change MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)
  change x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx
  refine GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    GlobalTheory.NabBC.isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  have hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) :=
    GlobalTheory.NabBC.mem_localization_of_mem' _ hx
  rw [L0] at hx0
  obtain ⟨g, ⟨s, hs, hsg⟩, hg⟩ := hx0
  rw [L1]
  refine ⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩
  · refine (congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_
    have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
    have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
    have h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) :=
      Submodule.subset_span ⟨_, hsg, rfl⟩
    rw [h1, ← h2] at h3
    have h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n)) := by
      ext y
      simp [MvPolynomial.map_id]
    rw [h4, Submodule.span_eq] at h3
    exact h3
  · change actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1
    rw [← GlobalTheory.ValCmp.use₂]
    exact congrArg (MvPolynomial.map f) hg

end BaseChange

theorem harmLat_le {D : D7} {m n : ℕ} {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K)
    (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O : Subring ℂ) (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsLattice D.host.E M) :
    harmLat (σ.comp f) emb O m w B M ≤ harmLat σ (fun τ => f.comp (emb τ)) O m w B M := by
  refine inf_le_inf_left _ (Submodule.comap_mono (Submodule.span_mono ?_))
  rintro _ ⟨F, hF, rfl⟩
  refine ⟨_, map_mem_nabAtr f emb w.lam M hM hF, funext fun y => ?_⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]

theorem coefLat_eq_small : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ O : Subring ℂ, intLL D ≤ O → ∀ h, B.coefLat D.what₂.embLL (labLL D) O h = B.coefLat (embLL0 D) (labLL0 D) O h := by
  intro D S T B hB O hO h
  have hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hM := GlobalTheory.SmallSpan.isLattice_latAt hB.frame h
  refine le_antisymm (fun P hP => ?_)
    (harmLat_le D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O B.w B.F.BS hM)
  have h1 := GlobalTheory.SmallSpan.harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O (fun a => hO ⟨a, rfl⟩)
    B.w B.F.BS hB.wt hm hM hP
  rw [Submodule.span_eq] at h1
  exact h1

end GlobalTheory.PlaceSmall

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_lattice_eq_small_coefficient_field : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ O : Subring ℂ, intLL D ≤ O → ∀ h, B.coefLat D.what₂.embLL (labLL D) O h = B.coefLat (embLL0 D) (labLL0 D) O h := by
  atlas_forward_decl GlobalTheory.PlaceSmall.coefLat_eq_small
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem tensor_exists_basis_expansion {O K L M ι : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [AddCommGroup M] [Module O M] [Module K M] [IsScalarTower O K M] [Fintype ι]
    (hinj : ∀ d : O, d ≠ 0 → algebraMap O L d ≠ 0) (v : Module.Basis ι K M) (x : L ⊗[O] M) :
    ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, e⟩ := hx
    obtain ⟨c', e'⟩ := hy
    refine ⟨c + c', ?_⟩
    rw [e, e']
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    have e : (d : O) • (a ⊗ₜ[O] f) = ∑ c, (y c • a) ⊗ₜ[O] v c := by
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul K (y c), hy, smul_assoc]
    have h0 := hinj d (nonZeroDivisors.coe_ne_zero d)
    refine ⟨fun c => (algebraMap O L d)⁻¹ • y c • a, ?_⟩
    rw [← algebraMap_smul L (d : O)] at e
    rw [← inv_smul_smul₀ h0 (a ⊗ₜ[O] f), e, Finset.smul_sum]
    simp only [TensorProduct.smul_tmul']

private theorem tensor_scalar_relation {O L M N ι : Type*} [CommRing O] [Field L] [Algebra O L] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] (ε : L →+* ℂ) (v : ι → M) (r : M → N) (R : L ⊗[O] M →ₛₗ[ε] N)
    (hR : ∀ a f, R (a ⊗ₜ f) = ε a • r f) (hli : LinearIndependent ℂ fun c => r (v c))
    (hsp : ∀ x : L ⊗[O] M, ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a) (A B : L ⊗[O] M) (z : ℂ) (h : R A = z • R B) :
    (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : L, ε t = z ∧ A = t • B) := by
  obtain ⟨α, rfl⟩ := hsp A
  have hind := Fintype.linearIndependent_iff.1 hli
  constructor
  · rintro rfl
    rw [map_zero, smul_zero, map_sum] at h
    simp only [hR] at h
    have h2 : ∀ a, α a = 0 := fun a => ε.injective ((hind _ h a).trans (map_zero _).symm)
    simp [h2]
  · obtain ⟨β, rfl⟩ := hsp B
    intro hB
    rw [map_sum, map_sum] at h
    simp only [hR] at h
    have h1 : ∀ a, ε (α a) - z * ε (β a) = 0 := hind (fun a => ε (α a) - z * ε (β a)) (by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self])
    have h2 : ∃ a, β a ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hB (by simp [hc])
    obtain ⟨a0, ha0⟩ := h2
    have h3 : ε (β a0) ≠ 0 := (map_ne_zero ε).2 ha0
    have ht : ε (α a0 / β a0) = z := by
      rw [map_div₀, sub_eq_zero.1 (h1 a0), mul_div_cancel_right₀ _ h3]
    refine ⟨α a0 / β a0, ht, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    apply ε.injective
    rw [map_mul, ht, sub_eq_zero.1 (h1 a)]

theorem _root_.GlobalTheory.T.chosenField_forms_proportional_of_readings : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)), Faithful rd → ∀ (ε : KE c w →+* ℂ) (hε : Extends ρ ε) (A B : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) (z : ℂ),
  rdF rd hρ hε A = z • rdF rd hρ hε B → (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : KE c w, ε t = z ∧ A = t • B) := by
  intro D c w ρ hρ j rd hF ε hε A B z h
  let v := Module.finBasis (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w))
  have hinj : ∀ d : D.ntw.O (c.twI w), d ≠ 0 → algebraMap _ (KE c w) d ≠ 0 := fun d hd h0 => by
    have h1 := congrArg ε h0
    rw [IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply, hρ.ek_e, map_zero] at h1
    exact hd (ρ.eO_injective (c.twI w) (c.sd w) (h1.trans (map_zero _).symm))
  exact tensor_scalar_relation ε v rd (rdF rd hρ hε) (rdF_tmul hρ hε) (hF _ v v.linearIndependent) (tensor_exists_basis_expansion hinj v) A B z h
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.ClassSumRat

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)

theorem add_mem_range {k : ℕ} {x y : GA D (Wc D j) → ℂ} (hx : x ∈ Set.range (rdK rd hρ k)) (hy : y ∈ Set.range (rdK rd hρ k)) :
    x + y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact ⟨x + y, map_add _ _ _⟩

theorem zero_mem_range {k : ℕ} : (0 : GA D (Wc D j) → ℂ) ∈ Set.range (rdK rd hρ k) := ⟨0, map_zero _⟩

theorem e_smul_mem_range {k : ℕ} (c : FractionRing (D.ntw.O i)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.e i b c • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem_range hρ rd
  | add x y hx hy => rw [map_add, smul_add]; exact add_mem_range hρ rd hx hy
  | tmul a f => exact ⟨a ⊗ₜ (c • f), by rw [rdK_tmul, rdK_tmul, LinearMap.map_smulₛₗ, smul_comm]⟩

theorem ek_smul_mem_range {k : ℕ} (a : FractionRing (D.ntw.Ok i k)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.ek i b k a • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨p, d, hd, e⟩ := D.ntw.Ok_gen i k a
  generalize Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p = u at e
  have h1 : ρ.ek i b k a * ρ.eO i b d = ρ.eOk i b k u := by
    rw [← hρ.ek_e i b k d]
    exact (map_mul (ρ.ek i b k) _ _).symm.trans (congrArg (ρ.ek i b k) e)
  have hd0 : ρ.eO i b d ≠ 0 := fun h => hd (ρ.eO_injective i b (h.trans (map_zero _).symm))
  have h2 : ρ.ek i b k a = ρ.e i b (algebraMap (D.ntw.O i) _ d)⁻¹ * ρ.eOk i b k u := by
    rw [map_inv₀, ← h1, mul_comm (ρ.ek i b k a)]
    exact (inv_mul_cancel_left₀ hd0 _).symm
  obtain ⟨x, rfl⟩ := hy
  rw [h2, mul_smul]
  exact e_smul_mem_range hρ rd _ ⟨u • x, LinearMap.map_smulₛₗ _ _ _⟩

include hρ in

theorem exists_rep (t : Twist D Circle) (h : GA D (Vc D j)) : ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j))
    (κ : (ρ.B i j b).levJ t), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧
      SuppAt (idem s) (Vc D j) h' ∧
      finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (κ : Bridge.Gf (Vc D j)) := by
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS ((ρ.B i j b).levS t)
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ t :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

theorem series_datum (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {s h P}
    (hd : ρ.IsDatum i j b s h P) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h P ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have h1 := hR k Q ψ hψ hQ s h P hd ⟨1, GlobalTheory.SplitLinear.suppAt_one _ _, rfl⟩
  rw [mul_one, GlobalTheory.TwTraceCx.gen_eq_smul (hρ.base i j b) ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)] at h1
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) h)
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi h : Circle) : ℂ) = ρ.ek i b k (algebraMap (D.ntw.Ok i k) _ u) := hu
  have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u)⁻¹ h1
  rwa [map_inv₀, ← hc, inv_smul_smul₀ (Circle.coe_ne_zero _)] at h2

theorem term_mem (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {F} (hF : F ∈ ρ.mt i j b k Q ψ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h (F (finPt _ h)) ∈
      Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hB := hρ.base i j b
  obtain ⟨hF1, hF2⟩ := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
  obtain ⟨γ, s, h', κ, hs, hoff, hh', hsupp, e⟩ := exists_rep hρ (i := i) (b := b) (ρ.tw i b k Q ψ) h
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF1).2 γ (finPt _ h') κ
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e, hlaw, LinearMap.map_smul, GlobalTheory.BaseClassSum.series_move hB (D.sp.V_sig _) ht hadm (hρ.weil i j b _ ht) hh hh' γ κ e, hinv,
    smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hspan : F (finPt _ h') ∈ Submodule.span (ρ.eOk i b k).range
      (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) :=
    GlobalTheory.SmallSpan.harmLat_le_span (RingHom.id _) (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.eOk i b k).range
      (hρ.isCoefRing_k i b k).int _ _ hB.wt (GlobalTheory.CoefLatConj.pq_le hB) (GlobalTheory.SmallSpan.isLattice_latAt hB.frame _) (hF2 _)
  generalize F (finPt _ h') = P at hspan
  induction hspan using Submodule.span_induction with
  | mem P hP => exact series_datum hρ rd hR hψ hQ ⟨hs, hoff, hh', hsupp, hP⟩
  | zero => rw [map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx =>
    obtain ⟨_, u, rfl⟩ := a
    have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u) hx
    rw [← map_smul] at h2
    exact h2

theorem sum_mem_range : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  intro D ρ hρ i j b rd T hR _ k Q ψ hψ hQ f
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hc := hρ.classes i j b _ ht hadm
  have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok i k)) (D.nexp.MtLat i ((j : ℕ) + 1) b k Q ψ : Set (D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ)) := by
    rw [D.nexp.MtLat_span]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    have hF := (T.mtLat_iff k Q ψ hψ _).2 ⟨f, hf, rfl⟩
    rw [Setup.sum, Base.classSum_apply]
    refine Finset.sum_induction _ (· ∈ Set.range (rdK rd hρ k)) (fun _ _ => add_mem_range hρ rd) (zero_mem_range hρ rd) fun c _ => ?_
    rw [← map_natCast (ρ.ek i b k), ← map_inv₀]
    exact ek_smul_mem_range hρ rd _ (term_mem hρ rd hR hψ hQ hF (hc.fin c))
  | zero => rw [map_zero, map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul]; exact ek_smul_mem_range hρ rd a hx

end GlobalTheory.ClassSumRat

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sums_twisted_definite_forms_rational : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  atlas_forward_decl GlobalTheory.ClassSumRat.sum_mem_range
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceLift

theorem eMt_fix (D : D7) (μ : D.what₂.Tup) (j : ℕ) (x : D.what₂.MtL μ j) (hx : x ∈ Idx.TjV D μ j) :
    D.what₂.eMt μ j (D.what₂.jMt μ j x) = D.what₂.jMt μ j x := by
  have hL : ∀ y ∈ Idx.TjL D μ j, D.what₂.eMt μ j (D.what₂.jMt μ j y) = D.what₂.jMt μ j y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, -, hv⟩ := hz
      rw [← hv]
      exact LinearMap.congr_fun (D.what₂.eMt_idem μ j) _
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, map_smul, ha]
  induction hx using Submodule.span_induction with
  | mem z hz => exact hL z hz
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, map_smul, ha]

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

theorem extV_formOf_eMt (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c) :
    X.R.toRealDat.extV j (Y.tupT (Y.tup t)) (formOf Y hμ j (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c))) =
      X.R.toRealDat.extV j t (X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) :=
  (extV_formOf Y hμ j _).trans (Y.mtRead j t hμ c)

theorem idem_fix (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c)
    (hc : D.what₂.eMt (Y.tup t) (j.1 + 1) (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) :
    X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c) =
      X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) := by
  have e2 := GlobalTheory.CenTranslate.liftForm_lvlOp (A3 := X.A3) (F := X.F.lv2) hH.ok.ok2 j t (idemOf X.A3.A.X)
    (fun b => idemOf_central X.A3.A.X hH.ok.ok2.irr b) c
  have e1 := (Y.formsL j t).op_eq c
  have e3 : D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t ((lE D X.A3.A X.F.P0 X.F.ψ0 j t).mulVec c)) := hc.symm.trans e1
  refine Y.hinj j t ?_
  refine (Y.mtRead j t hμ c).symm.trans ?_
  refine (congrArg (fun y => (Y.IL.jMt (Y.tup t) hμ j y).1) e3).trans ?_
  refine (Y.mtRead j t hμ _).trans ?_
  exact congrArg (fun v => X.R.toRealDat.extV j t (X.R.jV j t v)) e2

theorem isAlgV_self (j : Fin D.R.m) (t : X.T) (u : (X.A3.A.fam.L j t).S.Forms)
    (hu : X.R.jV j t u = X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u))
    (κ : X.Γ → (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).Q) (hκ : ∀ g, GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsLiftV X.R.toRealDat j t g (κ g)) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsAlgV X.R.toRealDat j t (RealDat.eC (A := X.A3.A) (sg0 D X.A3.A)) κ (X.R.jV j t u) (X.R.jV j t u) := by
  have hs : sg0 D X.A3.A = D.what₂.embLL := sgAt_mk _ X.R.hv0
  refine (congrArg (X.R.HV j t).e hu).trans ?_
  have e3 := map_sum (X.R.jV j t) (fun g => (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u) Finset.univ
  have e4 := map_sum (X.R.HV j t).e (fun g => (X.R.jV j t) ((idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u)) Finset.univ
  refine ((congrArg (X.R.HV j t).e e3).trans e4).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (X.R.jV j t) ((idemOf X.A3.A.X).coeff g) ((X.A3.A.fam.L j t).r g u)
  have e6 := LinearMap.map_smul (X.R.HV j t).e (D.what₂.embLL ((idemOf X.A3.A.X).coeff g)) (X.R.jV j t ((X.A3.A.fam.L j t).r g u))
  refine ((congrArg (X.R.HV j t).e e5).trans e6).trans ?_
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V X.R.toRealDat X.char.grp.red_L X.char.models.jV j t g u
  have e7 : (X.R.HV j t).e (X.R.jV j t ((X.A3.A.fam.L j t).r g u)) =
      Bridge.g0Act (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).ch (κ g) ((X.R.HV j t).e (X.R.jV j t u)) :=
    funext fun h => hT.2 (κ g) (hκ g) h
  have e8 : D.what₂.embLL ((idemOf X.A3.A.X).coeff g) = RealDat.eC (A := X.A3.A) (sg0 D X.A3.A) g := by
    rw [RealDat.eC, hs]
  rw [e7, e8]

theorem lift_read (hP : GlobalTheory.Mem.R3.Pins X.R X.F X.cG) (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (μ : D.what₂.Tup) (hμ : Used0 D μ)
    (x : D.what₂.MtL μ (j.1 + 1)) (hx : x ∈ Idx.TjV D μ (j.1 + 1)) (v : (X.R.MW j (sg0 D X.A3.A)).Vec) :
    (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP μ (j.1 + 1) (D.what₂.jMt μ (j.1 + 1) x))) v =
      X.R.thF j (Y.tupT μ) (formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) x)) v := by
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨c, rfl⟩ := (Y.eMt j t).surjective x
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  choose κ hκ using GlobalTheory.ProjLiftLaw.liftV_exists_core hC j t
  have h1 := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.F X.cG X0 Y hP hH j t c
  have h2 := GlobalTheory.ProjLiftLaw.thG_apply_eq hC j t κ hκ _ _
    (isAlgV_self j t _ (idem_fix Y hH j t hμ c (eMt_fix D _ _ _ hx)) κ hκ) v
  have h3 := GlobalTheory.Mem.ThetaRead3.thF_congr X.R.toRealDat Y.hinj j t (Y.tupT (Y.tup t)) (Y.tupT_tup t) _ _ (extV_formOf_eMt Y j t hμ c)
  exact ((congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y v) h1).trans h2).trans (congrArg (fun U => U v) h3).symm

theorem lift_read_at : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1),
  (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) (X.geo.v₀ j (sg0 D X.A3.A)) =
    X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) (X.geo.v₀ j (sg0 D X.A3.A)) :=
  fun _ _ _ Y _ _ _ _ _ j H x hx => lift_read Y H.pins H.intersectionNumber_baseChange j _ (used_of_tw H.tw) x hx _

end GlobalTheory.PlaceLift

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftForm_at_evaluationVector_eq_realisationLift : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1),
  (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) (X.geo.v₀ j (sg0 D X.A3.A)) =
    X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) (X.geo.v₀ j (sg0 D X.A3.A)) := by
  atlas_forward_decl GlobalTheory.PlaceLift.lift_read_at
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.CentralTranslate

open GlobalTheory.FreeBlockTwist Matrix
open GlobalTheory.StdFrames (cpt)

variable {D : D7} {S T : HSp D}

theorem exists_pow_latAt {B : Base S T} (hF : B.F.Good) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ}
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ h : Bridge.Gf S, ∀ x ∈ B.latAt h,
      ((N ^ l : ℕ) : 𝓞 D.host.E) • x ∈ B.latAt (h * (finPt S k)⁻¹) := by
  classical
  have hβ := hF.frS
  choose m hm using fun ij : Fin S.rank × Fin S.rank =>
    GlobalTheory.StdFrames.exists_pow_mul_mem (N := N)
      (((B.F.βS⁻¹).1 * (Formalism.L2.Theta.mt S k).map (toEAf D) * B.F.βS.1) ij.1 ij.2) fun PP hPP =>
      conj_entry (toEAf D) B.F.βS hk (cpt PP) (ha PP hPP) (PP.adicCompletionIntegers D.host.E) (zero_mem _) (one_mem _) ij.1 ij.2
  refine ⟨Finset.univ.sup m, fun l hl h x hx => ?_⟩
  have hx' : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => eToEAf D (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS := hx
  have h3 := (hβ _).1 hx'
  have h4 := (hβ _).2 (conj_mulVec _ B.F.βS _ (fun i j => hm (i, j) l ((Finset.le_sup (Finset.mem_univ _)).trans hl)) h3)
  change ((Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹).1 *ᵥ (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS
  have e1 : (Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹ =
      Formalism.UG.bc (Lev.swapAE D) (finPt S k).1 * (Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.map_mul, MonoidHom.map_inv, _root_.mul_inv_rev, inv_inv]
  have e2 : (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) = (N ^ l) • fun i => eToEAf D (x i) := by
    funext i
    rw [Nat.cast_smul_eq_nsmul, Pi.smul_apply, Pi.smul_apply, map_nsmul]
  rw [e1, e2, Units.val_mul, mulVec_nsmul]
  convert h4 using 1
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul]
  rfl

theorem coefLatFn_le {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    {n : ℕ} (lam : D.what₂.Tau → DomWeight n) {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O) (hM : Submodule.IsLattice D.host.E M) (h1 : ∀ x ∈ M, (N : 𝓞 D.host.E) • x ∈ M')
    (h2 : ∀ x ∈ M', (N : 𝓞 D.host.E) • x ∈ M) : coefLatFn σ emb O lam M ≤ coefLatFn σ emb O lam M' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have h3 : coefFn σ lam (((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F : VV K lam) : Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O lam M' :=
    Submodule.subset_span ⟨_, nabAtr_scale emb lam N hM h1 h2 F hF, rfl⟩
  have h4 := Submodule.smul_mem _ ((⟨_, hO⟩ : O) ^ GlobalTheory.NabScale.scaleExp lam) h3
  have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [SetLike.mem_coe]
  convert h4 using 1
  funext x
  change _ = ((N : ℂ)⁻¹) ^ GlobalTheory.NabScale.scaleExp lam * coefFn σ lam ((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F.1) x
  rw [coefFn, coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_pow, map_natCast, inv_pow]
  field_simp

theorem coefLat_mul {B : Base S T} (hF : B.F.Good) {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O)
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) (h : Bridge.Gf S) :
    B.coefLat σ emb O (h * finPt S k) = B.coefLat σ emb O h := by
  obtain ⟨m₁, h₁⟩ := exists_pow_latAt hF hk ha
  obtain ⟨m₂, h₂⟩ := exists_pow_latAt hF (GlobalTheory.SplitLinear.suppAt_inv hk) ha
  have e1 := h₁ (m₁ + m₂) (Nat.le_add_right _ _) (h * finPt S k)
  have e2 := h₂ (m₁ + m₂) (Nat.le_add_left _ _) h
  rw [mul_inv_cancel_right] at e1
  rw [show finPt S k⁻¹ = (finPt S k)⁻¹ from MonoidHom.map_inv _ k, inv_inv] at e2
  have hL : ∀ y : Bridge.Gf S, Submodule.IsLattice D.host.E (B.latAt y) := fun y =>
    Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hF.sdS.1.span_eq_top _
  have hO' : ((N ^ (m₁ + m₂) : ℕ) : ℂ)⁻¹ ∈ O := by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem hO _
  have e := le_antisymm (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e1 e2)
    (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e2 e1)
  unfold Base.coefLat harmLat
  rw [e]

theorem translate_mem_formsC {B : Base S T} {ψ : Twist D Circle} {c : Bridge.Gf S} (hc : ∀ g, g * c = c * g)
    {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC ψ) : (fun h => f (h * c)) ∈ B.formsC ψ := by
  rw [Base.mem_formsC] at hf ⊢
  refine ⟨fun h => hf.1 _, fun γ h k => ?_⟩
  have := hf.2 γ (h * c) k
  rw [← mul_assoc, mul_assoc _ c, ← hc, ← mul_assoc] at this
  exact this

theorem mem_mtLat_iff_translate : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ (ψ : Twist D Circle) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O →
  ∀ (Q : Finset (Pl D.host.E)) (z : GA D (Vc D j)), IsCentAt j Q z → ∀ N : ℕ, N ≠ 0 → (∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ P.asIdeal) → (N : ℂ)⁻¹ ∈ O →
  ∀ F : Amb D j, F ∈ B.mtLat σ emb O ψ ↔ (fun h => F (h * finPt (Vc D j) z)) ∈ B.mtLat σ emb O ψ := by
  intro D j B hB ψ K _ _ σ emb O _ Q z hz N hN hQ hO F
  obtain ⟨hzc, -, e, he, hsupp⟩ := hz
  have ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (e + cA D e)) = 0 := fun PP hPP => by
    rw [RingHom.map_add, RingHom.map_add, (cpt_sum he PP).2 fun h => hPP (hQ PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum he _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hQ _ h)))
  have hc : ∀ g : Bridge.Gf (Vc D j), g * finPt (Vc D j) z = finPt (Vc D j) z * g := fun g => by
    obtain ⟨y, rfl⟩ := (finHom (Vc D j)).rangeRestrict_surjective g
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul, Subgroup.mem_center_iff.1 hzc y]
  have hc' : ∀ g : Bridge.Gf (Vc D j), g * (finPt (Vc D j) z)⁻¹ = (finPt (Vc D j) z)⁻¹ * g := fun g =>
    (Commute.inv_right (hc g)).eq
  have hl := coefLat_mul hB.frame σ emb O hsupp hN hO ha
  rw [Base.mem_mtLat, Base.mem_mtLat]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨translate_mem_formsC hc h1, fun h => hl h ▸ h2 _⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h => ?_⟩
    · have := translate_mem_formsC hc' h1
      simp only [inv_mul_cancel_right] at this
      exact this
    · have := h2 (h * (finPt (Vc D j) z)⁻¹)
      rw [← hl] at this
      simp only [inv_mul_cancel_right] at this
      exact this

end GlobalTheory.CentralTranslate

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_forms_central_translate_iff : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ (ψ : Twist D Circle) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O →
  ∀ (Q : Finset (Pl D.host.E)) (z : GA D (Vc D j)), IsCentAt j Q z → ∀ N : ℕ, N ≠ 0 → (∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ P.asIdeal) → (N : ℂ)⁻¹ ∈ O →
  ∀ F : Amb D j, F ∈ B.mtLat σ emb O ψ ↔ (fun h => F (h * finPt (Vc D j) z)) ∈ B.mtLat σ emb O ψ := by
  atlas_forward_decl GlobalTheory.CentralTranslate.mem_mtLat_iff_translate
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceConj

theorem conj_lat : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → B.w.lam = lamV D j → ∀ (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) →
  (∀ x : VsV D j ℂ, harmFn (Wc D j).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ →
  ∃ C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j, (∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) ∧ (C F = 0 → F = 0)) ∧
    ∀ O : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → C '' (B.mtLat (embLL0 D) (labLL0 D) O ψ : Set (Amb D j)) = (B.mtLat (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) ψ' : Set (Amb D j)) := by
  intro D j B hB hlam Φ κ hκ0 hval hκ τ hτ ψ ψ' hψ hψ' hcc hf
  have huq := GlobalTheory.CoefLatConj.existsUnique_eq Φ hB hlam hκ0 hval hκ
  have hinj : Function.Injective Φ := fun x y hxy => (huq (Φ x) (hval x)).unique rfl hxy
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hinj)
  have hπx : ∀ x, π (Φ x) = x := fun x => LinearMap.congr_fun hπ x
  have hπv : ∀ P ∈ B.valSpace, Φ (π P) = P := fun P hP => by
    obtain ⟨x, rfl, -⟩ := huq P hP
    rw [hπx]
  let C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j :=
    { toFun := fun F h => Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)))
      map_add' := fun F G => by
        funext h
        simp only [Pi.add_apply, map_add, smul_add]
      map_smul' := fun a F => by
        funext h
        simp only [Pi.smul_apply, map_smul, map_smulₛₗ, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hC : ∀ F h, C F h = Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h))) := fun _ _ => rfl
  have hconjAt : ∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) := fun F hF h =>
    ⟨π (F h), GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)), rfl, (hπv _ (hF h)).symm, hC F h⟩
  refine ⟨C, fun F hF => ⟨hconjAt F hF, fun h0 => ?_⟩, fun O hO => ?_⟩
  · funext h
    have e := congrFun h0 h
    rw [hC, Pi.zero_apply, ← map_zero Φ] at e
    have e1 := hinj e
    have hc : τ κ / κ ≠ 0 := div_ne_zero ((map_ne_zero _).2 hκ0) hκ0
    rw [smul_eq_zero] at e1
    have e2 : π (F h) = 0 := by
      rcases e1 with e1 | e1
      · exact absurd e1 hc
      · have := congrArg (GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j)) e1
        rwa [GlobalTheory.CoefLatConj.mapVV_symm_mapVV, map_zero] at this
    rw [Pi.zero_apply, ← hπv _ (hF h), e2, map_zero]
  · have hτ' : ∀ a, τ.symm (embLL0 D a) = embLL0 D a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hO' : IsCoefRing (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) :=
      ⟨hO.emb, fun a => Subring.mem_map.2 ⟨_, hO.int a, hτ _⟩⟩
    have hOO : (O.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = O := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    ext F'
    constructor
    · rintro ⟨F, hF, rfl⟩
      have hFv : ∀ h, F h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF).1).1
      exact GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) O hO τ hτ ψ ψ' hψ hψ' hcc hf
        F (C F) (hconjAt F hFv) hF
    · intro hF'
      have hF'v : ∀ h, F' h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF').1).1
      let F : Amb D j := fun h => Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))
      have hFm : F ∈ B.mtLat (embLL0 D) (labLL0 D) O ψ := by
        have key := GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) hO'
          τ.symm hτ' ψ' ψ hψ' hψ hcc.symm hf.symm F' F
          (fun h => ⟨π (F' h), GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)), rfl, (hπv _ (hF'v h)).symm, rfl⟩) hF'
        rwa [hOO] at key
      refine ⟨F, hFm, funext fun h => ?_⟩
      rw [hC]
      change Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j)
        (π (Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))))) = F' h
      rw [hπx, map_smulₛₗ (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j))]
      have e3 := GlobalTheory.CoefLatConj.mapVV_symm_mapVV (lamV D j) τ.symm (π (F' h))
      rw [RingEquiv.symm_symm] at e3
      rw [e3, smul_smul]
      have : τ κ / κ * (τ (τ.symm κ / κ)) = 1 := by
        rw [map_div₀, RingEquiv.apply_symm_apply]
        have : τ κ ≠ 0 := (map_ne_zero _).2 hκ0
        field_simp
      rw [RingHom.coe_coe, this, one_smul, hπv _ (hF'v h)]

end GlobalTheory.PlaceConj

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_scaled_coords_integral_forms_twist : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → B.w.lam = lamV D j → ∀ (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) →
  (∀ x : VsV D j ℂ, harmFn (Wc D j).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ →
  ∃ C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j, (∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) ∧ (C F = 0 → F = 0)) ∧
    ∀ O : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → C '' (B.mtLat (embLL0 D) (labLL0 D) O ψ : Set (Amb D j)) = (B.mtLat (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) ψ' : Set (Amb D j)) := by
  atlas_forward_decl GlobalTheory.PlaceConj.conj_lat
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosen_twist_via_embedding_good_conjugate : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → ∀ (j : Fin D.R.m) (ι : KE c w →+* ℂ),
  (twVia ρ ι).Good ∧ (ρ.B (c.twI w) j (c.sd w)).admitted (twVia ρ ι).Q ∧ ∀ τ : ℂ ≃+* ℂ, ConjChar τ (twVia ρ ι) (twVia ρ ((τ : ℂ →+* ℂ).comp ι)) := by
  first | exact @GlobalTheory.PlaceRead.twVia_good | exact GlobalTheory.PlaceRead.twVia_good | (intros; apply GlobalTheory.PlaceRead.twVia_good <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceUnit

theorem card_residueField_ne_zero {E : Type} [Field E] [NumberField E] (P : Pl E) : Nat.card (kP P) ≠ 0 := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  exact Nat.card_pos.ne'

theorem card_residueField_mem {E : Type} [Field E] [NumberField E] (P : Pl E) : ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  letI : Fintype (kP P) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] (P : Pl E) {q l : ℕ} (h : Nat.Coprime q l)
    (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro hl
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((l : ℕ) : 𝓞 E)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hl)

theorem not_mem_of_pD {D : D7} (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  have h : P ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hP
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  refine not_mem_of_coprime P ?_ h
  split_ifs with e
  · exact (Nat.coprime_primes D.host.pde'_prime hl).2 (e ▸ D.host.pde_ne.symm)
  · exact (Nat.coprime_primes D.host.pde_prime hl).2 (Ne.symm e)

theorem isUnit_card_residueField_Oe {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) {P : Pl D.host.E}
    (hl : ((D.ntw.l (c.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : IsUnit ((Nat.card (kP P) : ℕ) : c.Oe w) := by
  haveI := D.ntw.Ok_fin (c.twI w) (c.k' w)
  have h : IsUnit ((Nat.card (kP P) : ℕ) : D.ntw.Ok (c.twI w) (c.k' w)) :=
    GlobalTheory.ResidueUnit.isUnit_of_coprime _ _ (GlobalTheory.ResidueUnit.card_residueField_coprime P _ (D.ntw.lPrime _).out hl)
      (GlobalTheory.ResidueUnit.natCast_mem_maximalIdeal_of_finite (O := D.ntw.O (c.twI w)) _ (D.ntw.O_l _))
  simpa using h.map (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w))

theorem tupPrime_isUnit : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι
  have hQ := (H.tup ι hι).2
  refine ⟨?_, fun P hP => ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_residueField_ne_zero P
  · obtain ⟨m, hm⟩ : Nat.card (kP P) ∣ GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hP)
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_residueField_mem P)
  · rw [GlobalTheory.TwistField.tupPrime, Nat.cast_prod]
    refine IsUnit.prod_iff.2 fun q hq => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine isUnit_card_residueField_Oe c w ?_
    rw [hQ, Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Z.good.delta] at hP
      exact not_mem_of_pD _ (mem_half.1 hP).1
    · exact fun h => Finset.disjoint_left.1 H.ok.2.1 (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar _ h)

end GlobalTheory.PlaceUnit
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  atlas_forward_decl GlobalTheory.PlaceUnit.tupPrime_isUnit
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem exists_extend_fractionRing {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (e : FractionRing A →+* ℂ) :
    ∃ ε : FractionRing B →+* ℂ, ε.comp (algebraMap A (FractionRing B)) = e.comp (algebraMap A (FractionRing A)) := by
  letI : Algebra A ℂ := (e.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective A ℂ).2
    (e.injective.comp (IsFractionRing.injective A (FractionRing A)))
  haveI : FaithfulSMul A (FractionRing B) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B _
  let φ : FractionRing B →ₐ[A] ℂ := IsAlgClosed.lift
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem exists_extends_and_emb : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  intro D c w ρ hρ
  haveI := c.Oe_fin w
  refine ⟨exists_extend_fractionRing (c.Oe_inj w) (ρ.ek (c.twI w) (c.sd w) (c.k' w)), fun hT ε hε x => ?_⟩
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w))
    ((if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have h0 : (if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x * algebraMap _ _ z = algebraMap _ _ y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have h1 := congrArg ε (hT.embedding_baseField_condition w x y z hz0 h0)
  have key : ∀ t : D.ntw.O (c.twI w), ε (algebraMap (c.Oe w) (FractionRing (c.Oe w))
      (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (algebraMap _ (D.ntw.Ok (c.twI w) (c.k' w)) t))) =
      ρ.eO (c.twI w) (c.sd w) t := fun t => by
    rw [← IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w), hε.apply, hρ.ek_e]
  rw [map_mul, key, key] at h1
  rw [← hρ.e_LL0 (c.twI w) (c.sd w) x]
  let m : FractionRing (D.ntw.O0 (c.twI w)) →+* FractionRing (D.ntw.O (c.twI w)) := IsFractionRing.map (D.ntw.O_inj (c.twI w))
  have hm : ∀ t, ρ.e (c.twI w) (c.sd w) (m (algebraMap _ _ t)) =
      ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) t) := fun t =>
    congrArg (ρ.e (c.twI w) (c.sd w)) (IsLocalization.map_eq _ t)
  have h2 := congrArg (fun t => ρ.e (c.twI w) (c.sd w) (m t)) h0
  simp only [map_mul, hm] at h2
  have hne : ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) ≠ 0 := by
    rw [← hm]
    exact (map_ne_zero _).2 ((map_ne_zero m).2 hz1)
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

end GlobalTheory.PlaceRead
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  atlas_forward_decl GlobalTheory.PlaceRead.exists_extends_and_emb
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem unit_of_unitOff : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  intro O _ _ _ ε N t hN ⟨ht0, n, h1, h2⟩
  have hε : Function.Injective ε := ε.injective
  have key : ∀ s : FractionRing O, IsIntegral ℤ (ε s) → ∃ a : O, algebraMap O (FractionRing O) a = s := by
    intro s hs
    letI : Algebra ℤ (FractionRing O) := Ring.toIntAlgebra _
    have hs' : IsIntegral ℤ s := (isIntegral_algHom_iff (ε.toIntAlgHom) hε).mp hs
    have hO : IsIntegral O s := by
      have := IsIntegral.map_of_comp_eq (Int.castRingHom O) (RingHom.id (FractionRing O)) (RingHom.ext_int _ _) hs'
      simpa using this
    exact IsIntegrallyClosed.isIntegral_iff.mp hO
  have ht : t ≠ 0 := by rintro rfl; simp at ht0
  obtain ⟨a, ha⟩ := key (((N : FractionRing O)) ^ n * t) (by simpa [map_mul, map_pow, map_natCast] using h1)
  obtain ⟨b, hb⟩ := key (((N : FractionRing O)) ^ n * t⁻¹) (by simpa [map_mul, map_pow, map_natCast, map_inv₀] using h2)
  have hN' : (N : FractionRing O) ≠ 0 := by
    have := (hN.map (algebraMap O (FractionRing O))).ne_zero
    simpa using this
  have hab : a * b = (N : O) ^ (2 * n) := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_pow, map_natCast]
    field_simp
    ring
  have hua : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ hN.pow _)
  have hinv : algebraMap O (FractionRing O) ((hN.unit⁻¹ : Oˣ) : O) = (N : FractionRing O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap O (FractionRing O)) N, ← map_mul, IsUnit.val_inv_mul, map_one]
  refine ⟨hua.unit * hN.unit⁻¹ ^ n, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_mul, map_pow, hinv, ha]
  rw [mul_comm (_ ^ n) t, mul_assoc, ← mul_pow, mul_inv_cancel₀ hN', one_pow, mul_one]

end GlobalTheory.PlaceRead
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  atlas_forward_decl GlobalTheory.PlaceRead.unit_of_unitOff
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.GlobalTheory.T.rational_lattice_fock_polys_span_integral_forms : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
  (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) =
    Submodule.span (intLL D) ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1)) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  classical
  have key := UpperTheory.KN.scaled_fock_form_mem_mtLat_iff D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  have hrat := UpperTheory.KN.exists_fock_form_eq_of_mem_mtLat D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  obtain ⟨e, -, htie, -⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · intro F hF
    obtain ⟨m, rfl⟩ := hrat F hF
    obtain ⟨a, ha⟩ := (key m).1 hF
    rw [ha, map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [map_smul, smul_comm]
    refine Submodule.smul_mem _ (⟨D.what₂.embLL (a v : D.what₂.LL), a v, rfl⟩ : intLL D) (Submodule.subset_span ?_)
    obtain ⟨x, hx⟩ := htie.1 v hv
    have hx' : D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) = v := hx
    exact ⟨e x, by show D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen; rw [hx']; exact hv, by simp only [hx']⟩
  · rintro _ ⟨m, hm, rfl⟩
    refine (key m).2 ⟨fun v => if v = D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m)]
    · simp
    · intro v _ hv
      simp [hv]
    · exact fun h => absurd hm h
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem image_span {R V A : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup A] [Module ℂ A] (φ : R →+* ℂ)
    (O : Subring ℂ) (hO : O = φ.range) (f : V →+ A) (hf : ∀ r v, f (r • v) = φ r • f v) (s : Set V) :
    f '' (Submodule.span R s : Set V) = (Submodule.span O (f '' s) : Set A) := by
  subst hO
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [hf]; exact Submodule.smul_mem _ (⟨φ r, r, rfl⟩ : φ.range) hx
  · induction hy using Submodule.span_induction with
    | mem x hx => exact Set.image_mono Submodule.subset_span hx
    | zero => exact ⟨0, zero_mem _, map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, map_add f x y⟩
    | smul r x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨_, r, rfl⟩ := r
      exact ⟨r • x, Submodule.smul_mem _ r hx, hf r x⟩

theorem span_span_sub {A : Type} [AddCommGroup A] [Module ℂ A] {O₁ O₂ : Subring ℂ} (h : O₁ ≤ O₂) (s : Set A) :
    Submodule.span O₂ (Submodule.span O₁ s : Set A) = Submodule.span O₂ s := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (Submodule.span_mono Submodule.subset_span)
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ (⟨r.1, h r.2⟩ : O₂) hx

theorem isIntegral_of_root {ζ : ℂ} (h : IsRoot1 ζ) : IsIntegral ℤ ζ ∧ IsIntegral ℤ ζ⁻¹ ∧ ζ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one), IsIntegral.of_pow hn (by rw [inv_pow, h, inv_one]; exact isIntegral_one), ?_⟩
  rintro rfl
  rw [zero_pow hn.ne'] at h
  exact zero_ne_one h

theorem unitOff_conj {N : ℕ} {a ζ ξ : ℂ} (τ : ℂ ≃+* ℂ) (ha : UnitOff N a) (hζ : IsRoot1 ζ) (hξ : IsRoot1 ξ) :
    UnitOff N (ξ * ζ * (τ a)⁻¹) := by
  obtain ⟨h0, n, h1, h2⟩ := ha
  obtain ⟨z1, z2, z0⟩ := isIntegral_of_root hζ
  obtain ⟨x1, x2, x0⟩ := isIntegral_of_root hξ
  have k1 := h1.map (τ : ℂ →+* ℂ).toIntAlgHom
  have k2 := h2.map (τ : ℂ →+* ℂ).toIntAlgHom
  simp only [map_mul, map_pow, map_natCast, map_inv₀] at k1 k2
  have t0 : τ a ≠ 0 := by simpa using h0
  refine ⟨mul_ne_zero (mul_ne_zero x0 z0) (inv_ne_zero t0), n, ?_, ?_⟩
  · have e : (N : ℂ) ^ n * (ξ * ζ * (τ a)⁻¹) = ξ * ζ * ((N : ℂ) ^ n * (τ a)⁻¹) := by ring
    rw [e]
    exact (x1.mul z1).mul k2
  · have e : (N : ℂ) ^ n * (ξ * ζ * (τ a)⁻¹)⁻¹ = ξ⁻¹ * ζ⁻¹ * ((N : ℂ) ^ n * τ a) := by rw [mul_inv, mul_inv, inv_inv]; ring
    rw [e]
    exact (x2.mul z2).mul k1

variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}

theorem mem_ringOf (ι : KE c w →+* ℂ) {y : D.what₂.LL} (hy : IsIntegral ℤ y) : ι (c.embW w y) ∈ ringOf ι := by
  obtain ⟨p, pm, hp⟩ := hy
  have h := congrArg (c.embW w) hp
  rw [Polynomial.hom_eval₂, map_zero] at h
  have hi : IsIntegral (c.Oe w) (c.embW w y) := ⟨p.map (Int.castRingHom _), pm.map _, by
    rw [Polynomial.eval₂_map, ← h]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨o, congrArg ι ho⟩

theorem intLL_le {ι : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x) : intLL D ≤ ringOf ι := by
  rintro _ ⟨a, rfl⟩
  change D.what₂.embLL (a : D.what₂.LL) ∈ _
  rw [← hι]
  exact mem_ringOf ι a.isIntegral_coe

theorem coefRing_LL {O : Subring ℂ} (h : intLL D ≤ O) : IsCoefRing D.what₂.embLL (labLL D) O :=
  ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => h ⟨a, rfl⟩⟩

theorem coefficient_ring_of_integral_le {O : Subring ℂ} (h : intLL D ≤ O) : IsCoefRing (embLL0 D) (labLL0 D) O :=
  ⟨embLL0_labLL0, fun a => h ⟨⟨((a : D.LL0) : D.what₂.LL), a.isIntegral_coe.map D.LL0.val.toRingHom.toIntAlgHom⟩, rfl⟩⟩

theorem span_latT (j : ℕ) : Submodule.span (KE c w) (latT c w j : Set (Tgt c w j)) = ⊤ := by
  refine top_unique fun y _ => ?_
  induction y using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem (hx trivial) (hy trivial)
  | tmul a f =>
    have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok (c.twI w) (c.k' w)))
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) : Set _) := by
      rw [D.nexp.MtLat_span]; trivial
    induction hf using Submodule.span_induction generalizing a with
    | mem f hf =>
      have e : (a ⊗ₜ f : Tgt c w j) = a • ((1 : KE c w) ⊗ₜ f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact Submodule.smul_mem _ a (Submodule.subset_span (Submodule.subset_span ⟨f, hf, rfl⟩))
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [TensorProduct.tmul_add]; exact add_mem (hf a trivial) (hg a trivial)
    | smul r f _ hf =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := D.ntw.Ok (c.twI w) (c.k' w)) r
      have hq0 := nonZeroDivisors.ne_zero hq
      have hq1 : algebraMap _ (KE c w) q ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply _ (c.Oe w) (KE c w)]
        exact fun h => hq0 (c.Oe_inj w ((IsFractionRing.injective (c.Oe w) (KE c w) (h.trans (map_zero _).symm)).trans (map_zero _).symm))
      have e : (a ⊗ₜ ((algebraMap _ (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) p / algebraMap _ _ q) • f) : Tgt c w j) =
          (p • (a / algebraMap _ (KE c w) q)) ⊗ₜ f := by
        conv_lhs => rw [← div_mul_cancel₀ a hq1, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
        rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) q,
          ← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) p f, smul_smul,
          mul_div_cancel₀ _ (by simpa using hq0)]
      rw [e]
      exact hf _ trivial

theorem span_smul_latT (j : ℕ) (o : (c.Oe w)ˣ) :
    Submodule.span (c.Oe w) ((fun y => algebraMap (c.Oe w) (KE c w) o • y) '' (latT c w j : Set (Tgt c w j))) = latT c w j := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun y hy => Submodule.subset_span ⟨((o⁻¹ : (c.Oe w)ˣ) : c.Oe w) • y, Submodule.smul_mem _ _ hy, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    beta_reduce
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  · beta_reduce
    rw [algebraMap_smul, smul_smul, Units.mul_inv, one_smul]

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

theorem rdF_thPe (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (hok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w))
    (hr : ∀ f, ρ.sum (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (T.rdV (c.k' w) (c.Q w) (chr c w) f) ∈ Set.range (rdK rd hρ (c.k' w)))
    (y : Tgt c w (j.1 + 1)) :
    rdF rd hρ hε (NChoice.thPe D c w (j.1 + 1) y) = ρ.sum (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (rdE T hε y) := by
  have key : ∀ m, rdF rd hρ hε (((Algebra.linearMap (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w)).restrictScalars (D.ntw.O (c.twI w))).rTensor
      (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) m) = rdK rd hρ (c.k' w) m := fun m => by
    induction m using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul a f =>
      rw [LinearMap.rTensor_tmul, rdF_tmul, rdK_tmul, ← hε.apply]
      rfl
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a f =>
    have e : (a ⊗ₜ f : Tgt c w (j.1 + 1)) = a • ((1 : KE c w) ⊗ₜ f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [rdE_tmul, map_smul, e, map_smul, LinearMap.map_smulₛₗ, NChoice.thPe_one, key, T.thP_eq _ _ _ hok f (hr f)]

end GlobalTheory.PlaceRead

namespace GlobalTheory.PlaceRead

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} {Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0} {S : NX.RatDat D.ntw}
  {YS : NX.NExpRealS X.R X.cG S} {Z : ExportTie YS X.geo.v₀} {c : NChoice D} {w : D.what₂.places.Pl} {j : Fin D.R.m}

theorem levJ_congr {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (h : ψ'.Q = ψ.Q) : B.levJ ψ' = B.levJ ψ := by
  obtain ⟨Q, a, b⟩ := ψ
  obtain ⟨Q', a', b'⟩ := ψ'
  dsimp only at h
  subst h
  rfl

theorem span_translate (H : AtPlace Y Z c w j) {ι : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x)
    {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0) (hs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ)
    {z : GA D (Vc D j)} (hz : IsCentAt j (X.R.Q (Y.tupT (D.what₂.muTw w))) z) :
    ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) : Set (Amb D j)) =
      Submodule.span (ringOf ι) ((fun x h => (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))
        (h * finPt (Vc D j) z)) '' latS w (j.1 + 1)) := by
  have hB := Z.good.base (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  have hle := intLL_le hι
  obtain ⟨hN0, hNP, o, ho⟩ := GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι
  have hNi : ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : ℂ)⁻¹ ∈ ringOf ι := by
    refine ⟨((o⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← map_natCast (ι.comp (algebraMap (c.Oe w) (KE c w))), ← ho, ← map_mul, Units.inv_mul, map_one]
  have h1 : (baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) =
      Submodule.span (ringOf ι) ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) ''
        latS w (j.1 + 1)) := by
    have e1 : (baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) =
        (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (ringOf ι) (twVia Z.ρ ι) := by
      unfold Base.mtLat
      rw [funext (GlobalTheory.T.coefficient_lattice_eq_small_coefficient_field D _ _ _ hB _ hle)]
    have e2 := GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing D _ _ _ hB _ hg ha _ D.what₂.embLL (labLL D) (𝓞 D.what₂.LL) (D.what₂.embLL.comp (algebraMap _ _))
      (D.what₂.embLL.injective.comp RingOfIntegers.coe_injective) (coefRing_LL le_rfl) (GlobalTheory.T.level_twist_character_mem_coefficientIntegers D X X0 Y S YS Z c w j H ι hι) _ hle
    have e3 := GlobalTheory.T.rational_lattice_fock_polys_span_integral_forms D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
    rw [e1, e2]
    exact (congrArg (fun M : Submodule (intLL D) (Amb D j) => Submodule.span (ringOf ι) (M : Set (Amb D j))) e3).trans
      (span_span_sub hle _)
  have hc := GlobalTheory.T.integral_forms_central_translate_iff D j _ hB (twVia Z.ρ ι) _ (embLL0 D) (labLL0 D) _ (coefficient_ring_of_integral_le hle) _ z hz _ hN0 hNP hNi
  let Tz : Amb D j →ₗ[ℂ] Amb D j := LinearMap.funLeft ℂ _ fun h => h * finPt (Vc D j) z
  have h2 := image_span (ringOf ι).subtype (ringOf ι) (Subring.range_subtype _).symm Tz.toAddMonoidHom
    (fun r v => Tz.map_smul (r : ℂ) v)
    ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1))
  rw [Set.image_image, ← h1] at h2
  refine Eq.trans (Set.Subset.antisymm (fun F hF => ?_) ?_) h2
  · have e : (fun h => (fun h => F (h * (finPt (Vc D j) z)⁻¹)) (h * finPt (Vc D j) z)) = F :=
      funext fun h => by beta_reduce; rw [mul_inv_cancel_right]
    exact ⟨fun h => F (h * (finPt (Vc D j) z)⁻¹), (hc _).2 (by rw [e]; exact hF), e⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact (hc F).1 hF

noncomputable def trOf (H : AtPlace Y Z c w j) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (κ : ℂ) (z : GA D (Vc D j)) :
    D.what₂.Mt (D.what₂.muTw w) (j.1 + 1) →ₗ[ℂ] Amb D j :=
  LinearMap.funLeft ℂ _ (fun h => h * finPt (Vc D j) z) ∘ₗ (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u)

theorem trOf_apply (H : AtPlace Y Z c w j) (u κ z y h) :
    trOf H u κ z y h = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u y (h * finPt (Vc D j) z) := rfl

theorem trOf_eq_zero (H : AtPlace Y Z c w j) {u κ z} (hκ : κ ≠ 0) (hinj : Function.Injective (fockOf Y (used_of_tw H.tw) j u)) (y)
    (hy : trOf H u κ z y = 0) : y = 0 := by
  refine hinj (Eq.trans (funext fun h => ?_) (map_zero _).symm)
  have := congrFun hy (h * (finPt (Vc D j) z)⁻¹)
  rw [trOf_apply, inv_mul_cancel_right] at this
  exact (smul_eq_zero.1 this).resolve_left (inv_ne_zero hκ)

theorem indep_conj {M A I : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A] (τ : ℂ ≃+* ℂ) (Φ : M →ₗ[ℂ] A)
    (C : A →ₛₗ[(τ : ℂ →+* ℂ)] A) (h : ∀ y, C (Φ y) = 0 → y = 0) {b : I → M} (hb : LinearIndependent ℂ b) :
    LinearIndependent ℂ fun k => C (Φ (b k)) := by
  refine linearIndependent_iff'.2 fun s g hg k hk => ?_
  have h1 : C (Φ (∑ i ∈ s, τ.symm (g i) • b i)) = 0 := by
    rw [map_sum, map_sum, ← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ]
    exact congrArg (· • _) (τ.apply_symm_apply _)
  simpa using linearIndependent_iff'.1 hb s _ (h _ h1) k hk

noncomputable def semiComp {L V M A : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
    [Module ℂ A] (τ : ℂ ≃+* ℂ) {σ : L →+* ℂ} (J : V →ₛₗ[σ] M) (Φ : M →ₗ[ℂ] A) (C : A →ₛₗ[(τ : ℂ →+* ℂ)] A) (σ' : L →+* ℂ)
    (h : ∀ r, τ (σ r) = σ' r) : V →ₛₗ[σ'] A where
  toFun x := C (Φ (J x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' r x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ]
    exact congrArg (· • _) (h r)

theorem rescale_conj {A : Type} [AddCommGroup A] [Module ℂ A] (τ : ℂ ≃+* ℂ) {n : ℕ} {κ ν ζ a₀ : ℂ} (hκ : κ ≠ 0) (hν : ν ≠ 0)
    {g : Fin n → A} {a a' : Fin n → ℂ} (ha : ∀ k, τ (a k) = a' k) {s : A} (h : κ • s = ζ • ∑ k, τ (a₀⁻¹ * a k) • g k) :
    s = (ν / κ * ζ * (τ a₀)⁻¹) • ν⁻¹ • ∑ k, a' k • g k := by
  rw [← inv_smul_smul₀ hκ s, h]
  simp only [map_mul, map_inv₀, ha, mul_smul]
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  congr 1
  field_simp

theorem expansion_eq (H : AtPlace Y Z c w j) {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0)
    {z : GA D (Vc D j)} {a₀ : ℂ} (ha₀ : a₀ ≠ 0) (L : Amb D j →ₗ[ℂ] (GA D (Wc D j) → ℂ)) {x} (hx : x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1))
    (hth : X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))
        (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) =
      a₀ • L (fun h => fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) (h * finPt (Vc D j) z)))
    {n : ℕ} {a : Fin n → D.what₂.LL} {f : Fin n → NX.FmK S (j.1 + 1)}
    (hf : (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
      Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) :
    κ • L (trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) =
      ∑ k, (a₀⁻¹ * D.what₂.embLL (a k)) • evW YS X.geo.v₀ j (f k).val := by
  have k1 := GlobalTheory.T.liftForm_at_evaluationVector_eq_realisationLift D X X0 Y S YS Z c w j H x hx
  have k0 : (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) = X.geo.v₀ j (sg0 D X.A3.A) := funext hu
  have k3 : evW YS X.geo.v₀ j (∑ k, a k • (f k).val) = ∑ k, D.what₂.embLL (a k) • evW YS X.geo.v₀ j (f k).val := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => evW_smul YS X.geo.v₀ j _ _
  have k4 : evW YS X.geo.v₀ j (∑ k, a k • (f k).val) = _ :=
    (congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y (X.geo.v₀ j (sg0 D X.A3.A))) hf).trans (k1.trans (k0 ▸ hth))
  have k5 : κ • trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) =
      fun h => fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) (h * finPt (Vc D j) z) :=
    funext fun h => by rw [Pi.smul_apply, trOf_apply, smul_inv_smul₀ hκ]
  rw [← map_smul, k5]
  simp only [mul_smul]
  rw [← Finset.smul_sum, ← k3, k4, inv_smul_smul₀ ha₀]

theorem span_conj (H : AtPlace Y Z c w j) {ι ε : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x) {τ : ℂ ≃+* ℂ}
    (hιε : (τ : ℂ →+* ℂ).comp ι = ε) {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0)
    (hs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ) {z : GA D (Vc D j)} (hz : IsCentAt j (X.R.Q (Y.tupT (D.what₂.muTw w))) z)
    (C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j) (M : Set (Amb D j))
    (hC : C '' ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) : Set (Amb D j)) = M) :
    M = Submodule.span (ringOf ε) ((fun x => C (trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) '' latS w (j.1 + 1)) := by
  have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
    rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
  have e3 := image_span ((τ : ℂ →+* ℂ).comp (ringOf ι).subtype) (ringOf ε)
    (by rw [← RingHom.map_range, Subring.range_subtype, e1]) C.toAddMonoidHom (fun r v => C.map_smulₛₗ (r : ℂ) v)
    ((fun x => trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1))
  rw [Set.image_image] at e3
  rw [← hC, span_translate H hι hu hκ hs hz]
  exact e3

theorem exists_read (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : PrN) (H : AtPlace Y Z c w j) {ε : KE c w →+* ℂ} (hε : Extends Z.ρ ε) :
    ∃ (Ψ : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[ε.comp (c.embW w)] Amb D j) (N : ℕ) (z₁ : ℂ),
      (∀ (I : Type) (b : I → D.what₂.MtL (D.what₂.muTw w) (j.1 + 1)),
        LinearIndependent ℂ (fun k => D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (b k)) → LinearIndependent ℂ fun k => Ψ (b k)) ∧
      ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia Z.ρ ε) : Set (Amb D j)) =
        Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)) ∧
      IsUnit (N : c.Oe w) ∧ UnitOff N z₁ ∧
      ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
        (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
          Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
        (baseOf Z c w j).classSum (Z.ρ.om (c.twI w) j (c.sd w) (twVia Z.ρ ε).chi) (twVia Z.ρ ε)
          (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) (Ψ x) =
          z₁ • (Z.ν (c.twI w) j (c.sd w))⁻¹ • ∑ k, ε (c.embW w (a k)) • evW YS X.geo.v₀ j (f k).val := by
  obtain ⟨τ, hτ0⟩ := GlobalTheory.BigOn.Exp.TwConj.exists_aut_on D.what₂.embLL (ε.comp (c.embW w))
    (GlobalTheory.BigOn.Exp.TwConj.countable_alg D.what₂.embLL)
  have hτ : ∀ x, τ (D.what₂.embLL x) = ε (c.embW w x) := fun x =>
    hτ0 x ((Algebra.IsAlgebraic.isAlgebraic x).algHom D.what₂.embLL.toRatAlgHom)
  have hfix : ∀ a, τ (embLL0 D a) = embLL0 D a := fun a => (hτ a).trans (H.emb ε hε a)
  obtain ⟨ι, hιε⟩ : ∃ ι : KE c w →+* ℂ, (τ : ℂ →+* ℂ).comp ι = ε :=
    ⟨(τ.symm : ℂ →+* ℂ).comp ε, RingHom.ext fun y => τ.apply_symm_apply _⟩
  have hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x := fun x => τ.injective ((RingHom.congr_fun hιε _).trans (hτ x).symm)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo : BaseOf X.R.toRealDat j (baseOf Z c w j) :=
    GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, hcc⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  obtain ⟨hg', ha', -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ε
  have hcj : ConjChar τ (twVia Z.ρ ι) (twVia Z.ρ ε) := hιε ▸ hcc τ
  obtain ⟨u, cc, κ, hu, hc, hκ, hval, hfn, hs, hν⟩ := GlobalTheory.T.exists_scale_twisted_place_coefficient_map D X X0 Y S YS Z c w j H
  obtain ⟨hfb, hfd⟩ := GlobalTheory.T.fix_base_of_fixing_field hP D X X0 Y S YS Z c w j H τ hfix
  obtain ⟨C, hC1, hC2⟩ := GlobalTheory.T.conjugation_scaled_coords_integral_forms_twist D j _ hB hBo.lam (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ hκ hval hfn τ hfix _ _ hg hg' hcj hfd
  have hω := Z.good.weil (c.twI w) j (c.sd w) _ hg
  have hω' := Z.good.weil (c.twI w) j (c.sd w) _ hg'
  have hcl' := Z.good.classes (c.twI w) j (c.sd w) _ hg' ha'
  have hcl : IsClassSystem (Vc D j) ((baseOf Z c w j).levJ (twVia Z.ρ ι)) (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) := by
    rw [← levJ_congr (baseOf Z c w j) hcj.1]
    exact hcl'
  refine (GlobalTheory.T.thetaLift_twistLevelForm_eq_unit_mul_classSum D X j _ hB hBo _ _ hg ha (H.tup ι hι) _ hω _ _ hcl u).elim fun z hz => hz.elim fun a₀ hz => ?_
  obtain ⟨hz, ha₀, hth⟩ := hz
  refine (GlobalTheory.T.classSums_conjugate_twists_conjugate_expansions D X j _ hB _ _ hg hg' ha (GlobalTheory.T.embedding_compat_at_place hCo hCW hHM hP D X X0 Y S YS Z c w j H ι hι τ hfix _ hg' hcj) u cc κ hu hc hκ τ hfb hfd
    hcj _ _ hω hω').elim fun ζ hζ => ?_
  obtain ⟨hζ, hcs⟩ := hζ
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u hu
  have hmem : ∀ y, fockOf Y (used_of_tw H.tw) j u y ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι) := fun y =>
    hrange.le (LinearMap.mem_range_self _ y)
  have hΦv : ∀ y h, trOf H u κ z y h ∈ (baseOf Z c w j).valSpace := fun y h =>
    Submodule.smul_mem _ κ⁻¹ (((baseOf Z c w j).mem_formsC.1 (hmem y)).1 _)
  have hN := (GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι).2.2
  refine ⟨semiComp τ (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) (trOf H u κ z) C (ε.comp (c.embW w)) hτ, _, _, fun I b hb => ?_, ?_, hN, unitOff_conj τ ha₀ hζ hν, fun x hx n a f hf => ?_⟩
  · exact indep_conj τ (trOf H u κ z) C (fun y hy => trOf_eq_zero H hκ hinj y ((hC1 _ (hΦv y)).2 hy)) hb
  · have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
      rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
    have e2 := hC2 _ (coefficient_ring_of_integral_le (intLL_le hι))
    rw [e1] at e2
    exact span_conj H hι hιε hu hκ hs hz C _ e2
  · have h1 := expansion_eq H hu hκ ha₀.1 _ hx (hth _ (hmem (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) hf
    have h2 := GlobalTheory.T.conjugate_function_at_place hP D X X0 Y S YS Z c w j H τ hfix ζ _ _
      (hcs _ _ hcl'.fin _ _ (hC1 _ (hΦv (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))).1) n _ f h1
    exact rescale_conj τ hκ (Z.scalar (c.twI w) j (c.sd w)).ne (fun k => hτ (a k)) h2

theorem exists_lift {L K V W A : Type} [Field L] [Field K] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W] [AddCommGroup A]
    [Module ℂ A] (φ : L →+* K) (ε : K →+* ℂ) (r : W →ₛₗ[ε] A) (hr : Function.Injective r) (Ψ : V →ₛₗ[ε.comp φ] A) {s : Set V}
    (hs : Submodule.span L s = ⊤) (h : ∀ x ∈ s, ∃ y, r y = Ψ x) : ∃ e : V →ₛₗ[φ] W, ∀ x, r (e x) = Ψ x := by
  have key : ∀ x, ∃ y, r y = Ψ x := fun x => by
    have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      exact ⟨x' + y', by rw [map_add, map_add, hx, hy]⟩
    | smul a x _ hx =>
      obtain ⟨x', hx⟩ := hx
      exact ⟨φ a • x', by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx]; rfl⟩
  choose e he using key
  exact ⟨⟨⟨e, fun x y => hr (by rw [map_add, he, he, he, map_add])⟩,
    fun a x => hr (by
      change r (e (a • x)) = r (φ a • e x)
      rw [LinearMap.map_smulₛₗ, he, he, LinearMap.map_smulₛₗ]; rfl)⟩, he⟩

theorem indep_of_read {K W A I : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup A] [Module ℂ A] (ε : K →+* ℂ)
    (r : W →ₛₗ[ε] A) {b : I → W} (h : LinearIndependent ℂ fun k => r (b k)) : LinearIndependent K b := by
  refine linearIndependent_iff'.2 fun s g hg k hk => ?_
  have h1 : ∑ i ∈ s, ε (g i) • r (b i) = 0 := by
    rw [← map_zero r, ← hg, map_sum]
    exact Finset.sum_congr rfl fun i _ => (r.map_smulₛₗ _ _).symm
  simpa using linearIndependent_iff'.1 h s _ h1 k hk

theorem mem_span_basis {L K V W I : Type} [Field L] [Field K] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W]
    {φ : L →+* K} (e : V →ₛₗ[φ] W) (b : Module.Basis I L V) (x : V) : e x ∈ Submodule.span K (Set.range fun i => e (b i)) := by
  have hx : x ∈ Submodule.span L (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem place_of_at (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : PrN) (H : AtPlace Y Z c w j) :
    ∃ (e : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[c.embW w] Tgt c w (j.1 + 1)) (u : (FractionRing (c.Oe w))ˣ),
      BasisAt c w (j.1 + 1) e ∧ LatAt c w (j.1 + 1) e (u : FractionRing (c.Oe w)) ∧ ThetaAt Y YS c w j e (u : FractionRing (c.Oe w)) := by
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField D c w Z.ρ Z.good).1
  refine (exists_read hCo hCW hHM hP H hε).elim fun Ψ h => h.elim fun N h => h.elim fun z₁ h => ?_
  obtain ⟨hind, hlat, hN, hz, hth⟩ := h
  obtain ⟨hinj, hmt⟩ := GlobalTheory.T.definiteFormReading_injective_lattice_integralForms D c w Z.ρ Z.good j _ (Z.tie (c.twI w) j (c.sd w)) ε hε H.ok H.field.roots
  have hsub : ∀ F ∈ Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)), ∃ y ∈ latT c w (j.1 + 1),
      rdE (Z.tie (c.twI w) j (c.sd w)) hε y = F := fun F hF => (hmt F).1 (hlat.ge hF)
  obtain ⟨e, he⟩ := exists_lift (c.embW w) ε _ hinj Ψ (GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)) fun x hx =>
    (hsub _ (Submodule.subset_span ⟨x, hx, rfl⟩)).imp fun _ h => h.2
  have hL : Submodule.span (c.Oe w) (e '' latS w (j.1 + 1)) = latT c w (j.1 + 1) := by
    have h1 := image_span (ε.comp (algebraMap (c.Oe w) (KE c w))) (ringOf ε) rfl
      (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom
      (fun r v => (congrArg _ (algebraMap_smul (KE c w) r v).symm).trans ((rdE (Z.tie (c.twI w) j (c.sd w)) hε).map_smulₛₗ _ v)) (e '' latS w (j.1 + 1))
    have h2 : (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom '' (e '' latS w (j.1 + 1)) = Ψ '' latS w (j.1 + 1) := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ => he x
    rw [h2] at h1
    refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨y', hy', e1⟩ := hsub _ (h1.le ⟨y, hy, rfl⟩)
      exact hinj e1 ▸ hy'
    · obtain ⟨y', hy', e1⟩ := h1.ge (hlat.le ((hmt _).2 ⟨y, hy, rfl⟩))
      exact hinj e1 ▸ hy'
  have hb : BasisAt c w (j.1 + 1) e := fun b => by
    refine ⟨indep_of_read ε (rdE (Z.tie (c.twI w) j (c.sd w)) hε) ?_, top_unique ?_⟩
    · simp only [he]
      exact hind _ b (D.what₂.jMt_basis _ _ b).1
    · rw [← span_latT, ← hL]
      refine Submodule.span_le.2 fun y hy => ?_
      refine (Submodule.span_le (p := (Submodule.span (KE c w) (Set.range fun i => e (b i))).restrictScalars (c.Oe w))).2 ?_ hy
      rintro _ ⟨x, -, rfl⟩
      exact mem_span_basis e b x
  have hfa : Faithful (Z.rd (c.twI w) j (c.sd w)) :=
    GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ X.R X.cG S YS X.geo.v₀ Z.ρ Z.good _ j _ _ (Z.scalar _ j _).ne X.unif
      X.char.models.HW (Z.vec j) H.ks
  have hrat := GlobalTheory.T.class_sums_twisted_definite_forms_rational D Z.ρ Z.good _ j _ _ (Z.tie (c.twI w) j (c.sd w)) (Z.rat H.rat).2.1 H.field.roots _ _ _ H.ok H.cls
  have key : ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
      (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
        Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
      rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (NChoice.thPe D c w (j.1 + 1) (e x)) =
        z₁ • rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
          (YS.eF (c.twI w) (j.1 + 1) (c.sd w) (Nat.le_add_left _ _) j.2).symm ((1 : NX.KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)) := by
    intro x hx n a f hf
    have h1 := hth x hx n a f hf
    rw [hε.twVia_eq] at h1
    refine (rdF_thPe _ hε H.ok hrat _).trans ((congrArg _ (he x)).trans (h1.trans (congrArg (z₁ • ·) ?_)))
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rdF_tmul, smul_comm]
    refine congrArg (ε (c.embW w (a k)) • ·) ?_
    refine Eq.trans ?_ (realRd_tmul YS X.geo.v₀ Z.good (c.twI w) j (c.sd w) _ 1 (f k)).symm
    rw [show Z.ρ.e (c.twI w) (c.sd w) (1 : NX.KB S (c.twI w) (c.sd w)) = 1 from map_one _, mul_one]
  have hco := fun x hx n a f hf => GlobalTheory.T.chosenField_forms_proportional_of_readings D c w Z.ρ Z.good j _ hfa ε hε _ _ z₁ (key x hx n a f hf)
  obtain ⟨o, ho⟩ : ∃ o : (c.Oe w)ˣ, ThetaAt Y YS c w j e (algebraMap (c.Oe w) (KE c w) o) := by
    by_cases hex : ∃ t : KE c w, ε t = z₁
    · obtain ⟨t, ht⟩ := hex
      obtain ⟨o, rfl⟩ := GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding (c.Oe w) ε N t hN (ht ▸ hz)
      refine ⟨o, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', e1⟩ := h1 hB
      exact e1.trans (congrArg (· • _) (ε.injective (ht'.trans ht.symm)))
    · refine ⟨1, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', -⟩ := h1 hB
      exact absurd ⟨t', ht'⟩ hex
  exact ⟨e, Units.map (algebraMap (c.Oe w) (KE c w)).toMonoidHom o, hb, hL.trans (span_smul_latT _ o).symm, ho⟩

end GlobalTheory.PlaceRead

namespace GlobalTheory.PlaceRead

open Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem exists_map_at_place : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  intro hCo hCW hHM hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ _ _ _ w => ∀ (Z : w.Lt) (X : RealSide (w.st Z).toD7), X.R.C = TC.cf w.I w.l Z → FieldOk X :=
    EvG.imp (GlobalTheory.TwInputs.SmallField.evLgG_fieldOk hP) fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp _ _ w _ Z => (H kp T w Z).1
  refine (((((GlobalTheory.T.rational_row_series hP hS hL).and (GlobalTheory.T.twisting_ok_class_at_place hP hL)).and (GlobalTheory.T.series_character_inverse hL)).and hF).and
    ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev))).trans
    (StepW.of_all fun K B f T w hO _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok v hv i
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H
  obtain ⟨hHo, -⟩ := h5 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h6 (w.st x.o.Z) hO
  let X := RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo (Finite.of_injective _ (ixOf_injective w.I _)) hHo hStd hSize
  have hf : FieldOk X := h4 x.o.Z X x.m.z.lev.C
  obtain ⟨k1, k2⟩ := h2 P x l ch tp hxi hpsi hQ hk hside v hv (hok v hv)
  obtain ⟨k3, k4⟩ := h3 P x l
  obtain ⟨ψ0, -, k5, -⟩ := hside.nct.psi_eq
  exact place_of_at (X := X) (Y := x.r.Y) (YS := l.b.YS) (Z := l.b.ser.ex) hCo hCW hHM hP
    { pins := x.m.z.pins, intersectionNumber_baseChange := x.m.intersectionNumber_baseChange, field := hf, tw := hv, ok := hok v hv, cls := k1
      emb := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField _ ch v _ l.b.ser.ex.good).2 hside.nct
      val := fun σ => ⟨_, (k5 v σ).trans (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
      U_eq := k3, psi_eq := k4, ks := l.rat.In.ks _ (Nat.le_add_left _ _) i.2
      rat := h1 P x l _ (GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ ch hside.nct hf.galois v hv) i _
      tup := k2 i }

end GlobalTheory.PlaceRead
end
