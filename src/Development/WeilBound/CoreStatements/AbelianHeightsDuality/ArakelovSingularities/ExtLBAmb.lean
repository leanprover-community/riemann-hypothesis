import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.ArMixIff
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowSegre
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyDef

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace LBIso IsProjOver)
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.Amb

theorem exists_twist_map {k : Type} [CommRing k] {X : Scheme.{0}} {n : ℕ} (e : X ⟶ PSpace k n) [IsClosedImmersion e]
    (M : LB X) (hM : M.IsLB) :
    ∃ (t r : ℕ) (g : X ⟶ PSpace k r), g ≫ PSpace.str k r = e ≫ PSpace.str k n ∧
      cls ((O1 k r).pull g) (LB.isLB_pull (O1_isLB k r) g) =
        cls M hM + (t : ℤ) • cls ((O1 k n).pull e) (LB.isLB_pull (O1_isLB k n) e) := by
  have hO : ((O1 k n).pull e).IsLB := LB.isLB_pull (O1_isLB k n) e
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X (e ≫ PSpace.str k n) ((O1 k n).pull e) n _ hO
    (veryAmpleBy_secPull_coord e) M hM
  obtain ⟨r, u, hu⟩ := ht (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  refine ⟨t₀.toNat, r, toProj (e ≫ PSpace.str k n) u hu, toProj_str _ _ _, ?_⟩
  have hT : (tw M ((O1 k n).pull e) (t₀.toNat : ℤ)).IsLB := LB.isLB_div hM (isLB_pw hO _)
  rw [(cls_eq_iff _ hT).2 (lbIso_pullback_O1_toProj _ u hu)]
  refine (cls_div hM (isLB_pw hO _) hT).trans ?_
  rw [GlobalTheory.EffBound.cls_pw hO, neg_smul, sub_neg_eq_add]

end GlobalTheory.Amb
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

theorem ringKrullDim_eq_one' [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) : ringKrullDim k = 1 := by
  have := hf
  have : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have : Ring.DimensionLEOne k := Ring.DimensionLEOne.of_isIntegral (R := ℤ) k
  apply eq_of_le_of_not_lt
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · intro h'
    have h'' : ringKrullDim k ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    have hk : IsField k := Ring.KrullDimLE.isField_of_isDomain
    exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := k) Int.cast_injective hk)

theorem topologicalKrullDim_of_polyCovered' [IsDomain k] [IsNoetherianRing k] (hk : ringKrullDim k = 1)
    {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) : topologicalKrullDim X = (d + 1 : ℕ) := by
  obtain ⟨ξ, -, hcov⟩ := h
  have hdim : ∀ (σ : Type) [Fintype σ], Fintype.card σ = d →
      topologicalKrullDim (Sp (MvPolynomial σ k)) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    intro σ _ hσ
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial σ k)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, hk, Nat.card_eq_fintype_card, hσ, add_comm]
    norm_cast
  apply le_antisymm
  · unfold topologicalKrullDim
    rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun Z => ?_
    obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
    obtain ⟨σ, _, e, he, hσ, -, ⟨y, rfl⟩, -⟩ := hcov x
    haveI := he
    let Φ := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding e e.isOpenEmbedding
    have hZ : TopologicalSpace.IrreducibleCloseds.map e e.isOpenEmbedding.continuous
        (Φ.symm ⟨Z, ⟨y, hx⟩⟩) = Z :=
      congrArg Subtype.val (Φ.apply_symm_apply ⟨Z, ⟨y, hx⟩⟩)
    rw [← hZ, e.isOpenEmbedding.coheight_map]
    have h1 := Order.coheight_le_krullDim (Φ.symm ⟨Z, ⟨y, hx⟩⟩)
    have h2 := hdim σ hσ
    unfold topologicalKrullDim at h2
    rw [h2] at h1
    exact h1
  · obtain ⟨σ, _, e, he, hσ, -, -, -⟩ := hcov ξ
    haveI := he
    rw [← hdim σ hσ]
    exact e.isOpenEmbedding.isInducing.topologicalKrullDim_le

theorem isIntegral_of_polyCovered' [IsDomain k] {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) :
    IsIntegral X := by
  obtain ⟨ξ, -, hcov⟩ := h
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨σ, _, e, he, -, -, ⟨y, rfl⟩, -⟩ := hcov x
    haveI := he
    exact isReduced_of_injective (e.stalkMap y).hom
      (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv.injective
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  have hirr : ∀ x : X, ∃ R : Set X, IsOpen R ∧ IsIrreducible R ∧ x ∈ R ∧ ξ ∈ R := by
    intro x
    obtain ⟨σ, _, e, he, -, -, hx, hξ⟩ := hcov x
    haveI := he
    refine ⟨Set.range e, e.isOpenEmbedding.isOpen_range, ?_, hx, hξ⟩
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (Sp (MvPolynomial σ k))).image _
      e.continuous.continuousOn
  haveI : IrreducibleSpace X := by
    refine (irreducibleSpace_def X).mpr ⟨⟨ξ, trivial⟩, ?_⟩
    rintro u v hu hv ⟨a, -, ha⟩ ⟨b, -, hb⟩
    obtain ⟨Ra, hRa, iRa, haRa, hξa⟩ := hirr a
    obtain ⟨Rb, hRb, iRb, hbRb, hξb⟩ := hirr b
    obtain ⟨p, hpa, hpu, hpb⟩ := iRa.2 u Rb hu hRb ⟨a, haRa, ha⟩ ⟨ξ, hξa, hξb⟩
    obtain ⟨q, -, ⟨hqu, -⟩, hqv⟩ :=
      iRb.2 (u ∩ Ra) v (hu.inter hRa) hv ⟨p, hpb, hpu, hpa⟩ ⟨b, hbRb, hb⟩
    exact ⟨q, trivial, hqu, hqv⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem polyCovered_pSpace' [IsDomain k] (N : ℕ) : PolyCovered (PSpace.str k N) N := by
  classical
  letI : GradedAlgebra (ProjSpace.grading k N) := MvPolynomial.gradedAlgebra
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ≠ 0 :=
    fun i => MvPolynomial.X_ne_zero i
  let ξ0 : PSpace k N := (⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.bot_prime, fun hle => hX 0 (by
      have h0 : MvPolynomial.X 0 ∈ HomogeneousIdeal.irrelevant (ProjSpace.grading k N) := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
        exact DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem k N 0) one_ne_zero
      have h1 := hle h0
      change _ ∈ (⊥ : HomogeneousIdeal (ProjSpace.grading k N)).toIdeal at h1
      rwa [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h1)⟩ :
    ProjectiveSpectrum (ProjSpace.grading k N))
  have hmem : ∀ i, ξ0 ∈ ProjSpace.chart k N i := fun i =>
    (Proj.mem_basicOpen _ _ _).mpr fun h => hX i (by
      change _ ∈ (⊥ : HomogeneousIdeal (ProjSpace.grading k N)).toIdeal at h
      rwa [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h)
  have hspec : ∀ z : PSpace k N, ξ0 ⤳ z := fun z =>
    specializes_iff_mem_closure.mpr
      ((ProjectiveSpectrum.le_iff_mem_closure (𝒜 := ProjSpace.grading k N)
        (ξ0 : ProjectiveSpectrum (ProjSpace.grading k N)) (z : ProjectiveSpectrum (ProjSpace.grading k N))).mp
      (show (⊥ : HomogeneousIdeal (ProjSpace.grading k N)) ≤ z.asHomogeneousIdeal from bot_le))
  have hr : ∀ i, ξ0 ∈ Set.range (ProjSpace.chartι k N i) := fun i => by
    have := hmem i
    rw [← ProjSpace.opensRange_chartι] at this
    exact this
  obtain ⟨η, hη⟩ := hr 0
  let w : Sp (MvPolynomial {j : Fin (N + 1) // j ≠ 0} k) := ⟨⊥, Ideal.bot_prime⟩
  have hηw : η ⤳ w := by
    have h1 : ProjSpace.chartι k N 0 η ⤳ ProjSpace.chartι k N 0 w := by
      rw [hη]
      exact hspec _
    exact (ProjSpace.chartι k N 0).isOpenEmbedding.isInducing.specializes_iff.mp h1
  have hηbot : η.asIdeal = ⊥ := le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr hηw)
  refine ⟨ξ0, fun y => ?_, fun x => ?_⟩
  · have hs : PSpace.str k N ξ0 = (spMap MvPolynomial.C) η := by
      rw [← hη, ← ProjSpace.chartι_str k N 0]
      rfl
    rw [hs]
    refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
    change Ideal.comap (MvPolynomial.C : k →+* MvPolynomial {j : Fin (N + 1) // j ≠ 0} k) η.asIdeal ≤ y.asIdeal
    intro a ha
    rw [Ideal.mem_comap, hηbot, Ideal.mem_bot, MvPolynomial.C_eq_zero] at ha
    rw [ha]
    exact zero_mem _
  · obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k N x
    refine ⟨{j : Fin (N + 1) // j ≠ i}, inferInstance, ProjSpace.chartι k N i, inferInstance, ?_,
      ProjSpace.chartι_str k N i, ?_, hr i⟩
    · simp
    · rw [← ProjSpace.opensRange_chartι] at hi
      exact hi

end GlobalTheory.Amb
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

def sumTensEquiv (σ τ : Type) : MvPolynomial (τ ⊕ σ) k ≃+* MvPolynomial σ k ⊗[k] MvPolynomial τ k :=
  (MvPolynomial.sumAlgEquiv k τ σ).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv k (MvPolynomial σ k)).symm.toRingEquiv

theorem sumTensEquiv_C (σ τ : Type) (r : k) :
    sumTensEquiv σ τ (MvPolynomial.C r) = algebraMap k (MvPolynomial σ k ⊗[k] MvPolynomial τ k) r := by
  have h1 : (MvPolynomial.sumAlgEquiv k τ σ) (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have h2 : (MvPolynomial.C (MvPolynomial.C r) : MvPolynomial τ (MvPolynomial σ k)) =
      MvPolynomial.monomial 0 (MvPolynomial.C r) := rfl
  show (MvPolynomial.algebraTensorAlgEquiv k (MvPolynomial σ k)).symm
    ((MvPolynomial.sumAlgEquiv k τ σ) (MvPolynomial.C r)) = _
  rw [h1, h2, MvPolynomial.algebraTensorAlgEquiv_symm_monomial, Algebra.TensorProduct.algebraMap_apply]
  rfl

variable {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) {σ τ : Type}

def prodChart (e : Sp (MvPolynomial σ k) ⟶ X) (e' : Sp (MvPolynomial τ k) ⟶ Y)
    (he : e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k))
    (he' : e' ≫ g = spMap (MvPolynomial.C : k →+* MvPolynomial τ k)) :
    Sp (MvPolynomial (τ ⊕ σ) k) ⟶ pullback f g :=
  spMap (sumTensEquiv σ τ).symm.toRingHom ≫ (pullbackSpecIso k (MvPolynomial σ k) (MvPolynomial τ k)).inv ≫
    pullback.map _ _ f g e e' (𝟙 _) (by rw [Category.comp_id, he]; rfl) (by rw [Category.comp_id, he']; rfl)

variable {f g} {e : Sp (MvPolynomial σ k) ⟶ X} {e' : Sp (MvPolynomial τ k) ⟶ Y}
  {he : e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k)}
  {he' : e' ≫ g = spMap (MvPolynomial.C : k →+* MvPolynomial τ k)}

theorem isOpenImmersion_prodChart [IsOpenImmersion e] [IsOpenImmersion e'] :
    IsOpenImmersion (prodChart f g e e' he he') := by
  unfold prodChart
  have : IsIso (CommRingCat.ofHom (sumTensEquiv (k := k) σ τ).symm.toRingHom) :=
    (sumTensEquiv (k := k) σ τ).symm.toCommRingCatIso.isIso_hom
  have : IsIso (spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom) := inferInstanceAs (IsIso (Spec.map _))
  have : IsOpenImmersion (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial σ k))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial τ k)))) f g e e' (𝟙 _)
      (by rw [Category.comp_id, he]; rfl) (by rw [Category.comp_id, he']; rfl)) :=
    Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  infer_instance

theorem prodChart_str : prodChart f g e e' he he' ≫ (pullback.fst f g ≫ f) =
    spMap (MvPolynomial.C : k →+* MvPolynomial (τ ⊕ σ) k) := by
  unfold prodChart
  rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, Category.assoc, he,
    pullbackSpecIso_inv_fst_assoc]
  unfold spMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  refine RingHom.ext fun r => ?_
  change (sumTensEquiv (k := k) σ τ).symm (Algebra.TensorProduct.includeLeftRingHom (MvPolynomial.C r)) = MvPolynomial.C r
  rw [RingEquiv.symm_apply_eq, sumTensEquiv_C]
  rfl

theorem range_prodChart : Set.range (prodChart f g e e' he he') =
    pullback.fst f g ⁻¹' Set.range e ∩ pullback.snd f g ⁻¹' Set.range e' := by
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial σ k))) ≫ 𝟙 (Sp k) = e ≫ f := by
    rw [Category.comp_id, he]; rfl
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial τ k))) ≫ 𝟙 (Sp k) = e' ≫ g := by
    rw [Category.comp_id, he']; rfl
  have hr := Scheme.Pullback.range_map _ _ f g e e' (𝟙 _) e₁ e₂
  have : IsIso (CommRingCat.ofHom (sumTensEquiv (k := k) σ τ).symm.toRingHom) :=
    (sumTensEquiv (k := k) σ τ).symm.toCommRingCatIso.isIso_hom
  have : IsIso (spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom) := inferInstanceAs (IsIso (Spec.map _))
  let a := spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom ≫
    (pullbackSpecIso k (MvPolynomial σ k) (MvPolynomial τ k)).inv
  have ha : Function.Surjective a := (inferInstance : Surjective a).surj
  have hc : prodChart f g e e' he he' = a ≫ pullback.map _ _ f g e e' (𝟙 _) e₁ e₂ := by
    simp only [prodChart, a, Category.assoc]
  rw [hc, ← hr]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a t, (Scheme.Hom.comp_apply a _ t).symm⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨t, rfl⟩ := ha u
    exact ⟨t, Scheme.Hom.comp_apply a _ t⟩

theorem polyCovered_pullback' {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (a b : ℕ) (hf : PolyCovered f a)
    (hg : PolyCovered g b) : PolyCovered (pullback.fst f g ≫ f) (a + b) := by
  obtain ⟨ξ, hξ, hX⟩ := hf
  obtain ⟨η, hη, hY⟩ := hg
  have heq : f ξ = g η := ((hξ (g η)).antisymm (hη (f ξ))).eq
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback ξ η heq
  refine ⟨z, fun y => ?_, fun x => ?_⟩
  · rw [Scheme.Hom.comp_apply, hz1]
    exact hξ y
  · obtain ⟨σ, _, e, he1, he2, he3, hxe, hξe⟩ := hX (pullback.fst f g x)
    obtain ⟨τ, _, e', he1', he2', he3', hxe', hηe'⟩ := hY (pullback.snd f g x)
    refine ⟨τ ⊕ σ, inferInstance, prodChart f g e e' he3 he3', isOpenImmersion_prodChart, ?_, prodChart_str, ?_, ?_⟩
    · rw [Fintype.card_sum, he2, he2', add_comm]
    · rw [range_prodChart]
      exact ⟨hxe, hxe'⟩
    · rw [range_prodChart]
      refine ⟨?_, ?_⟩
      · show pullback.fst f g z ∈ Set.range e
        rw [hz1]; exact hξe
      · show pullback.snd f g z ∈ Set.range e'
        rw [hz2]; exact hηe'

end GlobalTheory.Amb
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

theorem polyCovered_pSpace [IsDomain k] (N : ℕ) : PolyCovered (PSpace.str k N) N :=
  polyCovered_pSpace' N

theorem polyCovered_pullback [IsDomain k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (a b : ℕ) (hf : PolyCovered f a)
    (hg : PolyCovered g b) : PolyCovered (pullback.fst f g ≫ f) (a + b) :=
  polyCovered_pullback' f g a b hf hg

theorem isIntegral_of_polyCovered [IsDomain k] {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) :
    IsIntegral X :=
  isIntegral_of_polyCovered' f d h

theorem topologicalKrullDim_of_polyCovered [IsDomain k] [IsNoetherianRing k] (hk : ringKrullDim k = 1)
    {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) : topologicalKrullDim X = (d + 1 : ℕ) :=
  topologicalKrullDim_of_polyCovered' hk f d h

theorem ringKrullDim_eq_one [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) : ringKrullDim k = 1 :=
  ringKrullDim_eq_one' hf

end GlobalTheory.Amb
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Amb

variable (k : Type) [CommRing k]

theorem polyCovered_mp [IsDomain k] : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), PolyCovered (mpStr k m n) (∑ i, n i)
  | 0, n => by
    rw [Fin.sum_univ_one]
    exact polyCovered_pSpace (n 0)
  | m + 1, n => by
    have h := polyCovered_pullback (toSpecBase k (n 0)) (mpStr k m (Fin.tail n)) (n 0) (∑ i, Fin.tail n i)
      (polyCovered_pSpace (n 0)) (polyCovered_mp m (Fin.tail n))
    rw [Fin.sum_univ_succ]
    exact h

theorem isIntegral_mp [IsDomain k] (m : ℕ) (n : Fin (m + 1) → ℕ) : IsIntegral (MP k m n) :=
  isIntegral_of_polyCovered _ _ (polyCovered_mp k m n)

theorem smooth_mp : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), SmoothOfRelativeDimension (∑ i, n i) (mpStr k m n)
  | 0, n => by
    rw [Fin.sum_univ_one]
    exact (inferInstance : SmoothOfRelativeDimension (n 0) (PSpace.str k (n 0)))
  | m + 1, n => by
    have ih := smooth_mp m (Fin.tail n)
    have h1 : SmoothOfRelativeDimension (∑ i, Fin.tail n i)
        (pullback.fst (toSpecBase k (n 0)) (mpStr k m (Fin.tail n))) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := ∑ i, Fin.tail n i)).of_isPullback
        (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n 0) (toSpecBase k (n 0)) :=
      (inferInstance : SmoothOfRelativeDimension (n 0) (PSpace.str k (n 0)))
    have e : ∑ i, n i = (∑ i, Fin.tail n i) + n 0 := by
      rw [Fin.sum_univ_succ, add_comm]; rfl
    rw [e]
    exact smoothOfRelativeDimension_comp (n := ∑ i, Fin.tail n i) (m := n 0) (hf := h1) (hg := h2) _ _

theorem genSmooth_mp (m : ℕ) (n : Fin (m + 1) → ℕ) : GenSmooth (mpStr k m n) (∑ i, n i) := by
  haveI := smooth_mp k m n
  exact genSmooth_of_smooth _ _

theorem isArithVar_mp [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) (m : ℕ) (n : Fin (m + 1) → ℕ) :
    IsArithVar (mpStr k m n) (∑ i, n i) := by
  haveI : Module.Finite ℤ k := hf
  haveI : IsNoetherian ℤ k := isNoetherian_of_isNoetherianRing_of_finite ℤ k
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hdim : ringKrullDim k = 1 := ringKrullDim_eq_one hf
  have hbase := (GlobalTheory.ArithBase.isArithVar_id (k := k) hdim).flat
  rw [Category.id_comp] at hbase
  haveI := hbase
  haveI : SmoothOfRelativeDimension (∑ i, n i) (mpStr k m n) := smooth_mp k m n
  haveI : Smooth (mpStr k m n) := SmoothOfRelativeDimension.smooth (∑ i, n i) (mpStr k m n)
  refine ⟨inferInstance, hf, isIntegral_mp k m n, ?_, ?_, ?_⟩
  · rw [← multiProjEmb_toSpecBase]
    exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ (GlobalTheory.ProjSpace.isProjOver_pspace_str k _)
  · exact Flat.comp _ _
  · exact topologicalKrullDim_of_polyCovered hdim (mpStr k m n) _ (polyCovered_mp k m n)

theorem isClosedImmersion_lift {T : Scheme.{0}} (m : ℕ) (n' : ℕ) (n : Fin (m + 1) → ℕ) (a : T ⟶ PSpace k n')
    [IsClosedImmersion a] (b : T ⟶ MP k m n) (h : a ≫ toSpecBase k n' = b ≫ mpStr k m n) :
    IsClosedImmersion (pullback.lift a b h : T ⟶ pullback (toSpecBase k n') (mpStr k m n)) := by
  haveI : IsProper (mpStr k m n) := isProper_mpStr k m n
  haveI : IsSeparated (mpStr k m n) := inferInstance
  haveI : IsSeparated (pullback.fst (toSpecBase k n') (mpStr k m n)) := inferInstance
  haveI : IsClosedImmersion (pullback.lift a b h ≫ pullback.fst (toSpecBase k n') (mpStr k m n)) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (pullback.lift a b h) (pullback.fst (toSpecBase k n') (mpStr k m n))

end GlobalTheory.Amb
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Amb

theorem isSeparated_pr_zero (k : Type) [CommRing k] (m : ℕ) (n : Fin (m + 1) → ℕ) :
    IsSeparated (pr k m n 0) := by
  have hs : IsSeparated (pr k m n 0 ≫ toSpecBase k (n 0)) := by
    rw [pr_toSpecBase]
    infer_instance
  exact IsSeparated.of_comp _ (toSpecBase k (n 0))

theorem lbIso_pull_tw {k : Type} [CommRing k] {X P : Scheme.{0}} (i : X ⟶ P) {a b : ℕ} (π₁ : P ⟶ PSpace k a)
    (π₀ : P ⟶ PSpace k b) (g : X ⟶ PSpace k a) (e : X ⟶ PSpace k b) (hg : i ≫ π₁ = g) (he : i ≫ π₀ = e) (t : ℕ)
    (M : LB X) (hM : M.IsLB)
    (h : cls ((O1 k a).pull g) (LB.isLB_pull (O1_isLB k a) g) =
      cls M hM + (t : ℤ) • cls ((O1 k b).pull e) (LB.isLB_pull (O1_isLB k b) e)) :
    LBIso ((tw ((O1 k a).pull π₁) ((O1 k b).pull π₀) (-(t : ℤ))).pull i) M := by
  have hA := LB.isLB_pull (O1_isLB k a) π₁
  have hB := LB.isLB_pull (O1_isLB k b) π₀
  have hT := isLB_tw hA hB (-(t : ℤ))
  have hTi := LB.isLB_pull hT i
  rw [← cls_eq_iff hTi hM, cls_pull hT i hTi]
  have hct : cls (tw ((O1 k a).pull π₁) ((O1 k b).pull π₀) (-(t : ℤ))) hT =
      cls ((O1 k a).pull π₁) hA - (-(-(t : ℤ))) • cls ((O1 k b).pull π₀) hB := by
    show cls (((O1 k a).pull π₁).div (AbLaw.pw ((O1 k b).pull π₀) (-(-(t : ℤ))))) hT = _
    rw [cls_div hA (isLB_pw hB _) hT, EffBound.cls_pw hB]
  rw [hct, map_sub, map_zsmul, cls_pull (O1_isLB k a) π₁ hA, cls_pull (O1_isLB k b) π₀ hB,
    ← pull_comp, ← pull_comp, hg, he]
  rw [cls_pull (O1_isLB k a) g, cls_pull (O1_isLB k b) e] at h
  rw [h, neg_neg]
  abel

end GlobalTheory.Amb
end
end
