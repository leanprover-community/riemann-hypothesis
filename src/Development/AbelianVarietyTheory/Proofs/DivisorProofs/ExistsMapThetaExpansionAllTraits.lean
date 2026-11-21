import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqvDown
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabExtOfTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  first | exact @GlobalTheory.Mum.eqv_eq_smul | exact GlobalTheory.Mum.eqv_eq_smul | (intros; apply GlobalTheory.Mum.eqv_eq_smul <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.ScaleEqv

theorem eqv_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ D A F _ _ N lab E h c
  let gg : F →+* Γ((TFK (R := R) F ⊗ A.A).left, ⊤) :=
    (fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hgg : ∀ u : F, gg u = (fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F u) := fun _ => rfl
  have inv1 : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens) (u : Fˣ), resTop W (gg u.val) * resTop W (gg (u⁻¹).val) = 1 := by
    intro W u
    simp only [resTop]
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let S : F → SecK A.L (snd (TFK (R := R) F) A.A).left N → SecK A.L (snd (TFK (R := R) F) A.A).left N :=
    fun u t => DVR.SecOps.secScale (gg u) t
  have Sf : ∀ u t j, (S u t).f j = resTop _ (gg u) * t.f j := fun _ _ _ => rfl
  have SS : ∀ (u : Fˣ) t, S u.val (S (u⁻¹).val t) = t := by
    intro u t
    apply DVR.SecOps.sec_ext
    intro j
    rw [Sf, Sf, ← _root_.mul_assoc, inv1, _root_.one_mul]
  have SS' : ∀ (u : Fˣ) t, S (u⁻¹).val (S u.val t) = t := by
    intro u t
    have := SS u⁻¹ t
    rwa [inv_inv] at this
  refine ⟨fun s => S c.val (E s), ⟨?_, ?_, ?_, h.onto, h.frame, h.lift, ?_⟩, fun s j => rfl⟩
  · constructor
    · intro s t hst
      apply h.bij.1
      have := congrArg (S (c⁻¹).val) hst
      simpa only [SS'] using this
    · intro t
      obtain ⟨s, hs⟩ := h.bij.2 (S (c⁻¹).val t)
      exact ⟨s, by simp only [hs, SS]⟩
  · intro s s' s'' hs j
    simp only [Sf]
    rw [h.add s s' s'' hs j, mul_add]
  · intro u s s' hs j
    simp only [Sf]
    rw [h.smul u s s' hs j, mul_left_comm]
  · intro p w θ s s' hw hθ hph j
    have key := h.act p w θ s s' hw hθ hph j
    have e : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by
      rw [← Over.comp_left, translT, lift_fst]
    have hψ : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens),
        ((translT A.A θ.pt).left.app W).hom (resTop W (gg c.val)) =
          resTop ((translT A.A θ.pt).left ⁻¹ᵁ W) (gg c.val) := by
      intro W
      simp only [resTop]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      congr 1
      rw [hgg]
      have hT : ((translT A.A θ.pt).left.appTop).hom (((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val)) =
          ((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
      exact hT
    erw [Sf, Sf]
    erw [map_mul, map_mul, map_mul, hψ, key, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, mul_left_comm]

end GlobalTheory.Mum.ScaleEqv
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  atlas_forward_decl GlobalTheory.Mum.ScaleEqv.eqv_scale
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum.GalDesc

open GlobalTheory.FieldBaseChange

theorem exists_algebraMap_eq_of_fixed {K F : Type} [Field K] [CharZero K] [Field F] [Algebra K F] [IsAlgClosure K F]
    (x : F) (h : ∀ σ : F →ₐ[K] F, σ x = x) : ∃ k : K, algebraMap K F k = x := by
  haveI := IsAlgClosure.isGalois K F
  have hx : x ∈ IntermediateField.fixedField (⊥ : IntermediateField K F).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact h σ.toAlgHom
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hx
  exact IntermediateField.mem_bot.1 hx

variable {K F : Type} [Field K] [Field F] [Algebra K F] {V W : Type} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module F W]

theorem linearIndependent_image {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    LinearIndependent F (fun i => a (Module.Basis.ofVectorSpace K V i)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have key : ∀ ℓ : F →ₗ[K] K, ℓ (g i) = 0 := by
    intro ℓ
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    have h0 : ∑ j ∈ s, ℓ (g j) • Module.Basis.ofVectorSpace K V j = 0 := by
      have := congrArg Λ hg
      rw [map_sum, map_zero, Finset.sum_congr rfl fun j _ => hΛ (g j) _] at this
      exact this
    exact linearIndependent_iff'.1 (Module.Basis.ofVectorSpace K V).linearIndependent s _ h0 i hi
  let e := Module.Basis.ofVectorSpace K F
  apply e.repr.injective
  ext j
  simpa using key (e.coord j)

theorem span_image {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    ⊤ ≤ Submodule.span F (Set.range fun i => a (Module.Basis.ofVectorSpace K V i)) := by
  rw [← ha.span, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  rw [← (Module.Basis.ofVectorSpace K V).linearCombination_repr v, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def extBasis {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex K V) F W :=
  Module.Basis.mk (linearIndependent_image ha) (span_image ha)

theorem extBasis_apply {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) (i) :
    extBasis ha i = a (Module.Basis.ofVectorSpace K V i) := Module.Basis.mk_apply _ _ _

theorem repr_semilinear {Idx : Type} (B : Module.Basis Idx F W) (τ : F →+* F) (g : W →ₛₗ[τ] W)
    (hg : ∀ i, g (B i) = B i) (w : W) (i : Idx) : B.repr (g w) i = τ (B.repr w i) := by
  classical
  have hw : w ∈ Submodule.span F (Set.range B) := B.span_eq ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [hg, B.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | smul c x _ hx =>
    rw [map_smulₛₗ, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, hx,
      map_mul]

theorem exists_scale [CharZero K] [IsAlgClosure K F] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a)
    (g : ∀ σ : F →ₐ[K] F, W →ₛₗ[(σ : F →+* F)] W) (hg : ∀ σ v, g σ (a v) = a v)
    {Ix : Type} (T : Ix → W) (c : (F →ₐ[K] F) → Fˣ) (hT : ∀ σ i, g σ (T i) = (c σ : F) • T i) :
    ∃ u : Fˣ, ∀ i, ∃ v, a v = (u : F) • T i := by
  classical
  set B := extBasis ha
  have hgB : ∀ σ j, g σ (B j) = B j := fun σ j => by rw [extBasis_apply, hg]
  have fix : ∀ w : W, (∀ σ, g σ w = w) → ∃ v, a v = w := by
    intro w hw
    have : ∀ j, ∃ k : K, algebraMap K F k = B.repr w j := fun j =>
      exists_algebraMap_eq_of_fixed _ fun σ => by
        have e := repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) w j
        rw [hw σ] at e
        exact e.symm
    choose k hk using this
    refine ⟨∑ j ∈ (B.repr w).support, k j • Module.Basis.ofVectorSpace K V j, ?_⟩
    conv_rhs => rw [← B.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, hk, extBasis_apply]
  by_cases h0 : ∀ i, T i = 0
  · exact ⟨1, fun i => ⟨0, by rw [map_zero, h0 i, smul_zero]⟩⟩
  push_neg at h0
  obtain ⟨i₀, hi₀⟩ := h0
  have : B.repr (T i₀) ≠ 0 := fun h => hi₀ (B.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 this
  set m0 := B.repr (T i₀) j with hm0
  have hm00 : m0 ≠ 0 := by simpa using hj
  have hσm : ∀ σ : F →ₐ[K] F, σ m0 = (c σ : F) * m0 := fun σ => by
    have := repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) (T i₀) j
    rw [hT, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨(Units.mk0 m0 hm00)⁻¹, fun i => fix _ fun σ => ?_⟩
  rw [map_smulₛₗ, hT, smul_smul]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, RingHom.coe_coe, map_inv₀, hσm]
  field_simp
end GlobalTheory.Mum.GalDesc

namespace GlobalTheory.Mum

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.GalDesc

theorem exists_common_scale_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))) (N : ℕ) (Ix : Type) (T : Ix → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) (a : (Kb R →ₐ[FractionRing R] Kb R) → (Kb R)ˣ), (∀ σ i, ∃ t', SecTw σ (T i) t' ∧ ∀ j, t'.f j = liftFun A.A _ (fnF (Kb R) (a σ).val) * (T i).f j) → ∃ c : (Kb R)ˣ, ∀ i, ∃ Φ : H0 A.L N, ∀ t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N, (∀ j, t''.f j = liftFun A.A _ (fnF (Kb R) c.val) * (T i).f j) → Agree A.L t'' Φ := by
  intro R _ _ _ hB A N Ix T a hT
  haveI : CharZero R := hB.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  let π : A.A.left ⟶ Spec (CommRingCat.of (FractionRing R)) := A.A.hom
  let π' := (fst (TFK (R := R) (Kb R)) A.A).left
  let p := (snd (TFK (R := R) (Kb R)) A.A).left
  have H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R)))) :=
    (IsPullback.of_hasPullback _ _).flip
  haveI : TopologicalSpace.NoetherianSpace A.A.left := by
    have := A.isAb.proper
    have : IsLocallyNoetherian A.A.left := LocallyOfFiniteType.isLocallyNoetherian A.A.hom
    have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
    have : IsNoetherian A.A.left := {}
    infer_instance
  let ε : Fin 1 → ℤ := fun _ => (N : ℤ)
  let aM := pullOver A.L ε (π := π) (π' := π') (φ := fun _ => 𝟙 A.A.left) (φ' := fun _ => p) H.w
    (fun _ => (Category.comp_id _).symm)
  have hext : IsExtension aM := isExtension_pullOver H A.isLB ε _

  have hσ : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, spMap (σ : Kb R →+* Kb R) ≫ (TFK (R := R) (Kb R)).hom =
      (TFK (R := R) (Kb R)).hom := fun σ => by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  let m : (Kb R →ₐ[FractionRing R] Kb R) → ((TFK (R := R) (Kb R) ⊗ A.A).left ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left) :=
    fun σ => ((Over.homMk (spMap (σ : Kb R →+* Kb R)) (hσ σ) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R)) ▷ A.A).left
  have hm₁ : ∀ σ, m σ ≫ π' = π' ≫ Spec.map (CommRingCat.ofHom (σ : Kb R →+* Kb R)) := fun σ => by
    simp only [m, π', ← Over.comp_left, whiskerRight_fst]; rfl
  have hm₂ : ∀ σ, m σ ≫ p = p := fun σ => by
    simp only [m, p, ← Over.comp_left, whiskerRight_snd]
  let g : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) →ₛₗ[(σ : Kb R →+* Kb R)]
      SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) :=
    fun σ => pullOver A.L ε (π := π') (π' := π') (p := m σ) (φ := fun _ => p) (φ' := fun _ => p) (hm₁ σ)
      (fun _ => (hm₂ σ).symm)

  have hg : ∀ σ v, g σ (aM v) = aM v := fun σ v => sec_ext' A.isLB fun y J hJ => by
    rw [sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ,
      sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, Category.assoc, hm₂]
  let T' : Ix → SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) := T

  have hsmul : ∀ (c : Kb R) (s t : SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε)),
      (∀ j, t.f j = liftFun A.A _ (fnF (Kb R) c) * s.f j) → t = c • s := fun c s t ht =>
    SecOver.ext _ _ fun j => (ht j).trans rfl
  have hT' : ∀ σ i, g σ (T' i) = ((a σ : (Kb R)ˣ) : Kb R) • T' i :=
    fun σ i => by
    obtain ⟨t', htw, ht'⟩ := hT σ i
    rw [← hsmul _ _ t' ht']
    refine sec_ext' A.isLB fun y J hJ => ?_
    rw [sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ]
    refine (htw _ (𝟙 _) (𝟙 _ ≫ m σ) (by rw [Category.assoc, hm₂]) ?_ y J hJ).symm
    rw [Category.assoc, hm₁, Category.id_comp, Category.id_comp]; rfl
  obtain ⟨u, hu⟩ := exists_scale hext g hg T' a hT'
  refine ⟨u, fun i => ?_⟩
  obtain ⟨v, hv⟩ := hu i
  refine ⟨v, fun t'' ht'' => ?_⟩
  have e : t'' = aM v := (hsmul _ (T' i) t'' ht'').trans hv.symm
  intro Z q q' hq z J hJ
  rw [show t'' = aM v from e, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, hq, Category.comp_id]

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_scaling_descends_to_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))) (N : ℕ) (Ix : Type) (T : Ix → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) (a : (Kb R →ₐ[FractionRing R] Kb R) → (Kb R)ˣ), (∀ σ i, ∃ t', SecTw σ (T i) t' ∧ ∀ j, t'.f j = liftFun A.A _ (fnF (Kb R) (a σ).val) * (T i).f j) → ∃ c : (Kb R)ˣ, ∀ i, ∃ Φ : H0 A.L N, ∀ t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N, (∀ j, t''.f j = liftFun A.A _ (fnF (Kb R) c.val) * (T i).f j) → Agree A.L t'' Φ := by
  atlas_forward_decl GlobalTheory.Mum.exists_common_scale_descends
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_eqv_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ lab lab) → ∃ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N) (E₀ : _), Eqv D.toPre A (Kb R) N lab E₀ ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀) := by
  intro R _ _ _ hB D A N hN lab E hE hlab
  have hc0 : CharZero R := hB.2
  choose E' hE' hT using fun σ => GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist R hB D A N hN lab E hE hlab σ
  choose c hc using fun σ => GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar R (maximalIdeal R) D A (Kb R) N hN lab E (E' σ) hE (hE' σ)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_common_scaling_descends_to_fractionField R hB A N {q : IntFam (maximalIdeal R) D.toPre N × Fam D.toPre (Kb R) N // q.1.Over q.2}
    (fun i => E i.1.2) c (fun σ i => ⟨E' σ i.1.2, hT σ i.1.1 i.1.2 i.2, hc σ i.1.2⟩)
  obtain ⟨E₀, hE₀, hE₀f⟩ := GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero R D.toPre A (Kb R) N lab E hE c₀
  choose Φ hΦ using hc₀
  have hex := fun F₀ => GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
  refine ⟨fun F₀ => Φ ⟨(F₀, (hex F₀).exists.choose), (hex F₀).exists.choose_spec⟩, E₀, hE₀, fun F₀ s hs => ?_⟩
  obtain rfl : (hex F₀).exists.choose = s := (hex F₀).unique (hex F₀).exists.choose_spec hs
  exact hΦ _ (E₀ _) (hE₀f _)

end GlobalTheory.Mum
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_expBy_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
      (F₀ : IntFam (maximalIdeal R) D.toPre k), ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀ := by
  intro R _ _ _ hR D C k hk W _ _ _ T F₀
  have := hR.2
  have hW := T.cdvr
  have := hW.1
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have cW : CharZero W := charZero_of_injective_ringHom T.inj
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨F', hF'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F₀
  obtain ⟨σ', hσ'⟩ := GlobalTheory.Mum.IntFam.exists_expandsAt W ⟨bW, cW⟩ T.D' T.A T.G T.U hGs k hk F'
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso C.P.L.L T.U.LG.L T.β T.ℓ C.P.L.isLB T.U.LG.isLB T.ℓ_gen k σ'
  refine ⟨σ, σ', F'.f, fun Z r z J J' hJ hJ' => ?_, hF', hσ'⟩
  have h1 : scal T.G.hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  rw [hσ Z r z J J' hJ hJ', h1, gs_eq r z ⊤ (by trivial), map_one, map_one, _root_.one_mul]

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralSection_expanding_thetaFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F₀ : IntFam (maximalIdeal R) D.toPre k), ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀ := by
  atlas_forward_decl GlobalTheory.Mum.Trait.exists_expBy_one
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.FieldBaseChange

def basisOfIsExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) : Module.Basis I F W :=
  Module.Basis.mk (GlobalTheory.ConstFam.linearIndependent_of_isExtension ha B.linearIndependent) (by
    have h : Submodule.span K (Set.range B) ≤
        Submodule.comap a (Submodule.span F (Set.range fun i => a (B i))) :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [← ha.span, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range B) := B.span_eq ▸ Submodule.mem_top
    exact h hv)

theorem basisOfIsExtension_apply {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) (i : I) : basisOfIsExtension ha B i = a (B i) := by
  simp [basisOfIsExtension]

theorem exists_bijective_extension : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  intro K F V V' W W' _ _ _ _ _ _ _ _ _ _ _ a d ha hd e he
  let B := Module.Basis.ofVectorSpace K V
  let B' := B.map (LinearEquiv.ofBijective e he)
  let C := basisOfIsExtension ha B
  let C' := basisOfIsExtension hd B'
  let E := C.equiv C' (Equiv.refl _)
  refine ⟨E.toLinearMap, E.bijective, fun v => ?_⟩
  have key : (E.toLinearMap.comp a : V →ₛₗ[algebraMap K F] W') = d.comp e := B.ext fun i => by
    have h1 : a (B i) = C i := (basisOfIsExtension_apply ha B i).symm
    have h2 : d (e (B i)) = C' i := by
      rw [basisOfIsExtension_apply hd B' i]; simp [B']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, h2, E, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun key v

end GlobalTheory.FieldBaseChange
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  atlas_forward_decl GlobalTheory.FieldBaseChange.exists_bijective_extension
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpExt

theorem torsion_from_closure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  intro R _ _ A F _ _ _ em N hN x hx
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp (FractionRing R)) A.A A.isAb N hN).1
  let i : K' →ₐ[FractionRing R] Kb R := IsAlgClosed.lift
  let : Algebra K' (Kb R) := i.toRingHom.toAlgebra
  have : IsScalarTower (FractionRing R) K' (Kb R) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hmul : x ≫ mulN A.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  let t0 : _ ⟶ torsion A.A N := pullback.lift x (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A N = x := pullback.lift_fst _ _ _
  have hs : (TFK (R := R) F).hom = spMap (em.toRingHom.comp (algebraMap (FractionRing R) (Kb R))) :=
    congrArg spMap em.comp_algebraMap.symm
  obtain ⟨w, hw⟩ := H (Kb R) F em.toRingHom t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A N).hom = (TFK (R := R) (Kb R)).hom := by
    refine spec_map_field_cancel em.toRingHom _ _ ?_
    rw [← Category.assoc, hw, Over.w t0, hs, ← spMap_comp_spMap]
    rfl
  let w1 : TFK (R := R) (Kb R) ⟶ torsion A.A N := Over.homMk w hw2
  refine ⟨w1 ≫ torsion.ι A.A N, ?_, ?_⟩
  · have hc : torsion.ι A.A N ≫ mulN A.A N = toUnit _ ≫ η :=
      pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    have h1 : (w1 ≫ torsion.ι A.A N) ≫ mulN A.A N = toUnit _ ≫ η := by
      rw [Category.assoc, hc, ← Category.assoc, comp_toUnit]
    rwa [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, ← Hom.one_def] at h1
  · rw [← ht0, Over.comp_left, ← hw, Category.assoc]
    rfl

end GlobalTheory.Mum.UpExt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  atlas_forward_decl GlobalTheory.Mum.UpExt.torsion_from_closure
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.UpExt

theorem over_famPull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  intro R _ _ I D k F₀ E F _ _ _ _ _ _ s h α
  have hL := D.P.isLB
  have g1 : ∀ {W : Scheme.{0}} (w : W), gs (𝟙 W) w ⊤ (1 : Γ(W, ⊤)) = 1 := fun w => by
    rw [gs_eq _ w ⊤ trivial, map_one, map_one]
  have h1 := (secScal_iff_val hL _ _ _ _).1 (h α)
  refine (secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  have e1 : (𝟙 _ ≫ (DegPre.prB D F).left) = (famMap D E F).left ≫ (𝟙 _ ≫ (DegPre.prB D E).left) := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, famMap_snd]
  have e2 : (𝟙 _ ≫ (famMap D E F).left) = (famMap D E F).left ≫ 𝟙 _ := by
    rw [Category.id_comp, Category.comp_id]
  change _ = _ * sval (termPull D E F k α (s.s α)) _ y J
  rw [g1, _root_.one_mul, show sval (termPull D E F k α (s.s α)) (𝟙 _) y J =
      sval (s.s α) (𝟙 _ ≫ (famMap D E F).left) y J from sval_pullOver _ _ _ _ hJ, e1, e2, GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ,
    GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ, h1 _ _ (fun ψ => hJ _), g1, _root_.one_mul]

end GlobalTheory.Mum.UpExt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  atlas_forward_decl GlobalTheory.Mum.UpExt.over_famPull
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpAct
open GlobalTheory.UT GlobalTheory.ThetaScalar

variable {R : Type} [CommRing R] [IsDomain R] {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E]
  [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem exists_frame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : w.IsGen) :
    ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J := by
  obtain ⟨hy, hb, hs⟩ := h
  have h0 : (baseMap (R := R) E F).left ≫ (DegPre.zeroF D E).left = (DegPre.zeroF D F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (baseMap (R := R) E F))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F p'.g.b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.P.L _ _ w (baseMap (R := R) E F).left) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem txFrame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : TXFrame k p w) {w' : Frm D F k p'.g.b} (hw' : w'.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) : TXFrame k p' w' := by
  obtain ⟨hy, hb, hs⟩ := h
  have hL := D.P.isLB
  have hb' : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ p.g.b.left = p'.g.b.left := by
    rw [Category.id_comp]; exact hb.symm
  refine ⟨hw', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have c : LB.Gen.Corr D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w 2)
        (LB.mulGen D.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.P.L _ _ ν p.g.b.left)) :=
      corr_of_val hL fun y I hI => (map_pow _ _ _).trans ((hw.2.1 ν hν y I hI).trans (by
        rw [val_mul hI, val_pull hI, Category.id_comp]))
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    rw [val_mul hJ, val_pull hJ, hb'] at e
    rw [hv _ _ z J hJ, val_corr hJ (hs p'.y), val_pull hJ, hy]
    exact (map_pow _ _ _).symm.trans e
  · have c : LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w k) (LB.pullGen D.P.L _ _ κ p.g.b.left))
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi p.y) (jFK (R := R) E))
          (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (TF (R := R) E).hom)) :=
      corr_of_val hL fun y I hI => by
        rw [val_mul hI, val_mul hI, val_pull hI, val_pull hI, val_pull hI, Category.id_comp, Category.id_comp,
          Category.id_comp]
        exact (congrArg (· * _) (map_pow _ _ _)).trans (hw.2.2 κ hκ y I hI)
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    have e₁ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ jFK (R := R) E = jFK (R := R) F := by
      rw [Category.id_comp]; exact specMap_jFK E F
    have e₂ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ (TF (R := R) E).hom = (TF (R := R) F).hom := by
      rw [Category.id_comp]; exact Over.w _
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb', e₁, e₂] at e
    rw [hv _ _ z J hJ, hy]
    exact (congrArg (· * _) (map_pow _ _ _)).symm.trans e

theorem phiVal_pull (hG : GlobalFnsSt) {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} {w' : Frm D F k p'.g.b}
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) (s t : Fam D E k) (H : PhiVal p w s.s t.s) :
    PhiVal p' w' (famPull D E F hG k s).s (famPull D E F hG k t).s := by
  obtain ⟨hy, hb, hs⟩ := h
  have hb' : p'.g.b = baseMap (R := R) E F ≫ p.g.b := Over.OverMorphism.ext hb
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D F p'.g.b ≫ famMap D E F = famMap D E F ≫ DegPre.trPt D E p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D E F)).trans (tr_pr D F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D E _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D E F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) E F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D E k α p.g.b (ρ ≫ famMap D E F) z J = uVal D F k α p'.g.b ρ z J := by
    have : famMap D E F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D E F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, hv _ _ z J hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

theorem secMap_eq (A : PolAV (Sp (FractionRing R))) : secMap A E F = baseK (R := R) E F ▷ A.A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [secMap_fst, whiskerRight_fst]
  · rw [secMap_snd, whiskerRight_snd]

theorem actVal_secPull {A : PolAV (Sp (FractionRing R))} {N : ℕ} (hN : Odd N) {x : TFK (R := R) E ⟶ A.A}
    {θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) E)} {θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)}
    (H : SymLift A.A A.L N N x θ) (H' : SymLift A.A A.L N N (baseK (R := R) E F ≫ x) θ')
    {t u : SecF A E N} (h : ActVal θ t u) : ActVal θ' (UpExt.secPull A E F N t) (UpExt.secPull A E F N u) := by
  obtain ⟨ξ, Hξ, v⟩ := SymLiftGlobal.exists_symLift_pull_val A.isLB (baseK (R := R) E F) H
  have c := SymLiftOdd.symLift_unique GlobalTheory.globalFns_holds A.isAb A.isLB hN θ' ξ H' Hξ
  intro Z r z J hJ
  have h₂ : thetaVal θ' r z J = thetaVal θ (r ≫ (secMap A E F).left) z J := by
    rw [secMap_eq]; exact (val_corr hJ c _).trans (v _ _ z J hJ)
  refine (sval_pullOver _ _ _ _ hJ).trans ((h _ _ z J hJ).trans (congrArg₂ (· * ·)
    (congrArg Units.val h₂.symm) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm)))
  have e : (translT A.A θ'.pt).left ≫ (secMap A E F).left = (secMap A E F).left ≫ (translT A.A θ.pt).left := by
    rw [H'.pt_eq, H.pt_eq, secMap_eq]
    exact congrArg (fun q => q.left) (CommPairing.whisker_translT (baseK (R := R) E F) x)
  rw [Category.assoc, Category.assoc, e]
  rfl

end GlobalTheory.Mum.UpAct

open GlobalTheory.Mum.UpAct GlobalTheory.UT GlobalTheory.ThetaScalar in

theorem GlobalTheory.Mum.UpAct.act_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = UpExt.secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  intro R _ _ _ hR D A N hN lab E₀ hE F _ _ _ _ _ lab' hlab E' hE' p w θ s s' hw hθ hs
  have : CharZero R := hR.2
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨p₀, hp, -⟩ := (qkPt_algClosure_bijective R D.toPre F
    (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) N hN.pos).2 p
  have hx : lab' p = baseK (R := R) (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp)
  replace hp : QkExt (algebraMap (Kb R) F) p₀ p := hp
  obtain ⟨w₀, hw₀⟩ := hE.frame p₀
  obtain ⟨θ₀, hθ₀⟩ := hE.lift p₀
  obtain ⟨w', hw', hv'⟩ := exists_frame_pull hp hw₀.1
  have hu := (GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R _ hR.1 D F N hN p).2 w w' hw (txFrame_pull hp hw₀ hw' hv')
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.toPre.P.L z J →
      val w r z J = val w₀ (r ≫ (baseMap (R := R) (Kb R) F).left) z J := fun Z r z J hJ =>
    (val_corr hJ (corr_of_val D.toPre.P.isLB hu) r).trans (hv' Z r z J hJ)
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of_globalFns hG R _ D (Kb R) N hN.pos p₀ w₀ hw₀.1
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R _ D F N hN.pos p w hw.1
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : SecF A F N →ₗ[F] SecF A F N, ∀ t, ActVal θ t (Θ t) := GlobalTheory.TorsionExt.exists_act θ
  rw [hx] at hθ
  have key : E' ∘ₗ Φ = Θ ∘ₗ E' := LinearMap.ext_on
    (isExtension_famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds hN.pos).span (by
      rintro _ ⟨u, rfl⟩
      have r₀ : PhiRel D.toPre (Kb R) N p₀ w₀ u (Φ₀ u) := (hΦ₀ u _).2 rfl
      have r := (hΦ _ _).1 ((phiRel_iff hG p w hw.1 _ _).2
        (phiVal_pull GlobalTheory.globalFns_holds hp hv u _ ((phiRel_iff hG p₀ w₀ hw₀.1 _ _).1 r₀)))
      have a := actVal_secPull hN hθ₀ hθ (ThetaBaseChange.actVal_of_isActOf (hE.act p₀ w₀ θ₀ u _ hw₀ hθ₀ r₀))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← r, hE', hE']
      exact GlobalTheory.TorsionExt.actVal_unique a (hΘ _))
  obtain rfl := (hΦ _ _).1 hs
  have e : E' (Φ s) = Θ (E' s) := LinearMap.congr_fun key s
  rw [e]
  exact (hΘ _).isActOf A.isLB
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_linearExtension_to_algClosedField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  atlas_forward_decl GlobalTheory.Mum.UpAct.act_extension
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  intro R _ _ _ hR D A N hN lab E₀ Φ hE hΦ F _ _ _ em lab' hlab
  have hN1 : 1 ≤ N := hN.pos
  haveI : CharZero R := hR.2
  letI : Algebra (Kb R) F := em.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
  have hem : IsScalarTower.toAlgHom (FractionRing R) (Kb R) F = em := AlgHom.ext fun _ => rfl
  let e : Fam D.toPre (Kb R) N →ₗ[Kb R] SecF A (Kb R) N :=
    { toFun := E₀
      map_add' := fun s t => SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecOver.ext _ _ fun j => hE.smul c s (c • s) ((isSmul_iff _ _ _).2 rfl) j }
  obtain ⟨e', he', hc⟩ := GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange _ _ _ _ _ _ (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N) (secPull A (Kb R) F N)
    (isExtension_famPull _ _ _ GlobalTheory.globalFns_holds hN1) (isExtension_secPull A (Kb R) F N) e hE.bij
  have hq := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1
  have onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure R A F em N hN1 x hx
      obtain ⟨p₀, hp₀⟩ := (hE.onto y).1 hy
      obtain ⟨p', hp', -⟩ := hq.1 p₀
      refine ⟨p', Over.OverMorphism.ext ?_⟩
      rw [hlab p₀ p' hp', hp₀, hxy]
    · rintro ⟨p, rfl⟩
      obtain ⟨p₀, hp₀, -⟩ := hq.2 p
      have hy := (hE.onto (lab p₀)).2 ⟨p₀, rfl⟩
      have e1 : lab' p = baseK (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp₀)
      rw [e1, ← MonObj.comp_pow, hy, MonObj.comp_one]
  refine ⟨fun s => e' s, ⟨he', fun s s' s'' h j => ?_, fun c s s' h j => ?_, onto,
    fun p => ((GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hR.1 D F N hN p).1),
    fun p => GlobalTheory.SymFrameClause.exists_symLift R A F N hN (lab' p) ((onto _).2 ⟨p, rfl⟩),
    fun p w θ s s' hw hθ hs => GlobalTheory.T.equivariant_linearExtension_to_algClosedField R hR D A N hN lab E₀ hE F lab' (hem ▸ hlab) e' hc p w θ s s' hw hθ hs⟩, ?_⟩
  · obtain rfl : s'' = s + s' := fam_ext h
    rw [map_add]
    rfl
  · obtain rfl : s' = c • s := (isSmul_iff _ _ _).1 h
    rw [map_smul]
    rfl
  · intro F₀ s hs
    obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
    have h1 := GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback R (maximalIdeal R) D.toPre N F₀ (Kb R) F s₀ hs₀
    obtain rfl := (GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ F).unique hs h1
    intro Z p p' hpp z J hJ
    show sval (e' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s₀)) p z J = _
    rw [hc]
    refine (sval_pullOver _ _ _ _ hJ).trans (hΦ F₀ s₀ hs₀ Z (p ≫ (secMap A (Kb R) F).left) p' ?_ z J hJ)
    rw [Category.assoc, ← hpp]
    exact congrArg (p ≫ ·) (congrArg (fun q => q.left) (secMap_snd A (Kb R) F))
end GlobalTheory.Mum.UpExt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_bijection_larger_closed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  atlas_forward_decl GlobalTheory.Mum.UpExt.exists_eqv_ext
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_liftFun_top {S0 : Scheme.{0}} (A : Over S0) {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤))
    {Z : Scheme.{0}} (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem fvalue_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  intro R _ _ _ hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W _ _ _ T F _ _ _ _ em hem
  obtain ⟨lab, E, hlab, hE, hT⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W T F em hem
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hAg⟩ := GlobalTheory.T.exists_equivariant_bijection_larger_closed_field R hR D C.A (C.n ^ j) hodd (C.lab j) E₀ Φ₀ hE₀ hΦ₀ F em lab hlab
  haveI : CharZero R := hR.2
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.Mum.eqv_eq_smul R (maximalIdeal R) D C.A F (C.n ^ j) hodd lab E E' hE hE'
  refine ⟨(c₀ : F)⁻¹, inv_ne_zero c₀.ne_zero, ?_⟩
  intro F₀ σ hσ Z p p' h1 h2 z J hJ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre (C.n ^ j) F₀ F
  obtain ⟨J', hJ', -⟩ := exists_good C.A.L C.A.isLB z (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun a => a.elim) (fun k => k.elim)
  set q := p' ≫ (snd (TFK (R := R) F) C.A.A).left with hq
  have e1 := hT F₀ s σ hs hσ Z p p' h1 h2 z J J' hJ hJ'
  have e2 : sval (E' s) p' z J' = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) * sval (E s) p' z J' := by
    unfold sval
    refine (congrArg (gs p' z _) (hc₀ s _)).trans ?_
    exact (gs_mul p' z _ (hJ'.mem _ p') _ _).trans (congrArg (· * _) (gs_liftFun_top _ _ _ _ _ (hJ'.mem _ p')))
  have e3 := hAg F₀ s hs Z p' q (Category.comp_id _).symm z J' hJ'
  have e4 := hΦ F₀ Z q z J J' hJ hJ'
  have hβ : J (q ≫ C.α) = J (p ≫ T.β) := by rw [h1, hq, Category.assoc]
  rw [hβ] at e4
  have huv : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)⁻¹) *
      gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) = 1 := by
    rw [← gs_mul (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ c₀.ne_zero,
      map_one, gs_eq (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, map_one, map_one]
  rw [e1, e4, ← e3, e2]
  linear_combination (-(gw wA q z (J (p ≫ T.β)) (J' q) ^ (C.n ^ j)).val * sval (E s) p' z J') * huv

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  atlas_forward_decl GlobalTheory.Mum.fvalue_const
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ValDescent

theorem spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem eq_of_comp_jK {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} {f g : X ⟶ Sp (FractionRing R)}
    (h : f ≫ jK R = g ≫ jK R) : f = g := by
  haveI : Mono (jK R) := Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap R (FractionRing R))).op
  exact (cancel_mono (jK R)).1 h

theorem desc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s w H Z p p' hpp z J hJ
  have := C.semi.smooth
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  haveI : Flat C.gp := Modif.flat_gp R C.toModif
  haveI : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip inferInstance
  haveI : Flat (pullback.fst T.β C.α) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.β C.α).flip inferInstance
  set q₁ : pullback T.β C.α ⟶ T.G.left := pullback.fst T.β C.α with hq₁
  set q₂ : pullback T.β C.α ⟶ C.A.A.left := pullback.snd T.β C.α with hq₂
  have hq : q₁ ≫ T.β = q₂ ≫ C.α := pullback.condition
  set ρ : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hρ
  have hρi : Function.Injective ρ := (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  set d : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ pullback T.β C.α := pullback.fst _ _ with hd
  set t : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ Sp F := pullback.snd _ _ with ht
  have hdt : d ≫ q₁ ≫ T.G.hom = t ≫ spMap ρ := pullback.condition
  have hinj : ∀ V, Function.Injective (d.app V) := by
    intro V
    have : IsDominant (spMap ρ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hρi).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (spMap ρ)
    have : IsSchemeTheoreticallyDominant d :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip
    have : QuasiCompact d := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip inferInstance
    exact d.app_injective V

  have hover : t ≫ jFK (R := R) F = d ≫ q₂ ≫ C.A.A.hom := by
    apply ValDescent.eq_of_comp_jK
    have e₁ : jFK (R := R) F ≫ jK R = spMap ρ ≫ spMap T.φ := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext hF
    have e₂ : T.G.hom ≫ spMap T.φ = T.β ≫ C.G.hom ≫ C.π := by
      rw [← T.ξ_π, ← Category.assoc, ← T.cart.1.w, Category.assoc]
    have e₃ : C.α ≫ C.G.hom ≫ C.π = C.A.A.hom ≫ jK R := by
      rw [← Category.assoc, C.α_cart.1.w, Category.assoc, C.gp_π]
    rw [Category.assoc, e₁, ← Category.assoc, ← hdt, Category.assoc, Category.assoc, e₂, ← Category.assoc q₁,
      hq, Category.assoc, e₃]
    simp only [Category.assoc]
  let P' : Over (Sp (FractionRing R)) := Over.mk (d ≫ q₂ ≫ C.A.A.hom)
  let ℓ : P' ⟶ TFK (R := R) F ⊗ C.A.A := lift (Over.homMk t hover) (Over.homMk (d ≫ q₂) (Category.assoc _ _ _))
  have hfst : ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left = t := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left = d ≫ q₂ := by
    rw [← Over.comp_left, lift_snd]; rfl

  have hL : C.P.L.L.IsLB := C.P.L.isLB
  set i := J (p ≫ T.β) with hi
  set Vβ := LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => i) with hVβ
  set Vα := LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i) with hVα
  set V : (pullback T.β C.α).Opens := q₁ ⁻¹ᵁ Vβ ⊓ q₂ ⁻¹ᵁ Vα with hV
  have l₀ : V ≤ q₁ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let a : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_left : V ≤ q₁ ⁻¹ᵁ Vβ)).op).hom ((q₁.app Vβ).hom (σ.f fun _ => i))
  let b : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE l₀).op).hom ((q₁.app ⊤).hom (scal T.G.hom w)) *
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_right : V ≤ q₂ ⁻¹ᵁ Vα)).op).hom ((q₂.app Vα).hom (s.f fun _ => i))
  have ka : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₁) ≫ T.β) = i → gs r z₀ V a = sval σ (r ≫ q₁) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of σ (r ≫ q₁) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ Vβ hr.1 _)
  have kb : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₂) ≫ C.α) = i → gs r z₀ V b = gs (r ≫ q₁) z₀ ⊤ (scal T.G.hom w) * sval s (r ≫ q₂) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of s (r ≫ q₂) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_mul r z₀ V hr _ _).trans (congrArg₂ (· * ·) ((gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ ⊤ trivial _))
      ((gs_res r z₀ _ hr _).trans (gs_pull r q₂ z₀ Vα hr.2 _)))
  have hab : a = b := by
    apply hinj V
    refine fn_ext fun x hx => ?_
    rw [gs_pull (𝟙 _) d x V hx, gs_pull (𝟙 _) d x V hx, Category.id_comp]
    have hmem : ((d ≫ q₁) ≫ T.β) x ∈ C.P.L.L.U i := Set.mem_iInter.1 hx.1 0
    obtain ⟨J', hJ', eJ'⟩ := exists_good C.P.L.L hL x (fun _ : Fin 1 => (d ≫ q₁) ≫ T.β) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hmem)
    have e₁ : J' ((d ≫ q₁) ≫ T.β) = i := eJ' 0
    have e₂ : J' ((d ≫ q₂) ≫ C.α) = i := by rw [Category.assoc, ← hq, ← Category.assoc]; exact e₁
    rw [ka _ d x J' hx e₁, kb _ d x J' hx e₂]
    have h₁ : (d ≫ q₁) ≫ T.β = ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
      rw [← Category.assoc, hsnd, Category.assoc, Category.assoc, hq]
    have h₂ : (d ≫ q₁) ≫ T.G.hom = ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ρ := by
      rw [← Category.assoc, hfst, Category.assoc, hdt]
    have := H _ (d ≫ q₁) ℓ.left h₁ h₂ x J' hJ'
    rw [hsnd] at this
    exact this

  set u : Z ⟶ pullback T.β C.α := pullback.lift p p' hpp with hu
  have hu₁ : u ≫ q₁ = p := pullback.lift_fst _ _ _
  have hu₂ : u ≫ q₂ = p' := pullback.lift_snd _ _ _
  have hz : u z ∈ V := by
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [← hu₁] at h
      exact h
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [hpp, ← hu₂] at h
      exact h
  have A := ka Z u z J hz (by rw [hu₁])
  have B := kb Z u z J hz (by rw [hu₂, ← hpp])
  rw [hu₁] at A B
  rw [hu₂] at B
  rw [hab] at A
  exact A.symm.trans B

end GlobalTheory.Mum.ValDescent
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  atlas_forward_decl GlobalTheory.Mum.ValDescent.desc
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatConst

open scoped TensorProduct

theorem mem_range_of_tmul_eq {K F O : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup O] [Module K O]
    {t u : O} {c : F} (ht : t ≠ 0) (h : (1 : F) ⊗ₜ[K] t = c ⊗ₜ[K] u) : ∃ x : K, algebraMap K F x = c := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K ht
  have e := congrArg (fun v => TensorProduct.rid K F (LinearMap.lTensor F l v)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl, one_smul, Algebra.smul_def] at e
  refine ⟨(l u)⁻¹, ?_⟩
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right (by simpa using e.symm)

theorem gs_spec {A B : CommRingCat.{0}} (h : A ⟶ B) (y : Spec B) (x : A) :
    gs (Spec.map h) y ⊤ ((Scheme.ΓSpecIso A).inv.hom x) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom x)) := by
  have e := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e]
  exact ((gs_pull (𝟙 _) (Spec.map h) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem mem_of_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (y : Spec (Z.presheaf.stalk z)) :
    f (Z.fromSpecStalk z y) ∈ U := by
  have : Z.fromSpecStalk z y ⤳ z := by
    have := Set.mem_range_self (f := Z.fromSpecStalk z) y
    rwa [Scheme.range_fromSpecStalk] at this
  exact (this.map f.continuous).mem_open U.isOpen hz

theorem gs_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (a : Γ(X, U)) {B : CommRingCat.{0}}
    (h : Z.presheaf.stalk z ⟶ B) (y : Spec B) :
    gs (Spec.map h ≫ Z.fromSpecStalk z ≫ f) y U a = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom (gs f z U a))) := by
  have m := mem_of_stalk f z U hz (Spec.map h y)
  rw [← gs_spec, ← Category.assoc, ← gs_pull _ f y U m, ← gs_pull _ (Z.fromSpecStalk z) y _ m,
    Scheme.fromSpecStalk_app (U := f ⁻¹ᵁ U) hz, gs_eq f z U hz]
  exact gs_res (Spec.map h) y le_top m _

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s c H ⟨Z, p, p', h₁, h₂, z, J, hJ, hne⟩
  let O := Z.presheaf.stalk z
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of F ⟶ O,
      Spec.map ρ = Z.fromSpecStalk z ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left := ⟨Spec.preimage _, Spec.map_preimage _⟩
  letI : Algebra (FractionRing W) O := (ρ.hom.comp (algebraMap (FractionRing W) F)).toAlgebra
  let B := CommRingCat.of (F ⊗[FractionRing W] O)
  let iL : CommRingCat.of F ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : O ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).toRingHom
  have hK : ∀ x : FractionRing W, iR.hom (ρ.hom (algebraMap _ F x)) = iL.hom (algebraMap _ F x) := fun x =>
    ((Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).commutes x).trans rfl
  let g : Spec B ⟶ Z := Spec.map iR ≫ Z.fromSpecStalk z
  have hg : g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map (ρ ≫ iR) := by
    rw [Spec.map_comp, hρ, Category.assoc]
  have w : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom = Spec.map iL ≫ jFK (R := R) F := by
    have e : (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom = (fst (TFK (R := R) F) C.A.A).left ≫ jFK (R := R) F :=
      (Over.w _).trans (Over.w (fst (TFK (R := R) F) C.A.A)).symm
    have e' : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom =
        (g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫ jFK (R := R) F := by simp only [Category.assoc, e]
    rw [e', hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    refine CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    exact (congrArg (fun q => iR.hom (ρ.hom q)) (hF r)).trans ((hK _).trans (congrArg iL.hom (hF r).symm))
  obtain ⟨q, q₁, q₂⟩ : ∃ q : Spec B ⟶ (TFK (R := R) F ⊗ C.A.A).left,
      q ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map iL ∧
      q ≫ (snd (TFK (R := R) F) C.A.A).left = g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left := by
    let T' : Over (Sp (FractionRing R)) := Over.mk (Spec.map iL ≫ jFK (R := R) F)
    let a : T' ⟶ TFK (R := R) F := Over.homMk (Spec.map iL) rfl
    let b : T' ⟶ C.A.A := Over.homMk (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) w
    exact ⟨(lift a b).left, congrArg (·.left) (lift_fst a b), congrArg (·.left) (lift_snd a b)⟩
  have k₁ : (g ≫ p) ≫ T.β = q ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
    rw [← Category.assoc q, q₂, Category.assoc, h₁]; simp only [Category.assoc]
  have k₂ : (g ≫ p) ≫ T.G.hom = q ≫ (fst (TFK (R := R) F) C.A.A).left ≫
      spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [← Category.assoc q, q₁, Category.assoc, h₂, ← Category.assoc p', ← Category.assoc g, hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun r => hK _)
  let u : O := sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J
  let t : O := sval σ p z J
  have key : iR.hom t = iL.hom c * iR.hom u := by
    apply (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J', hJ', e⟩ := exists_good C.P.L.L C.P.L.isLB y (K := Unit) (fun _ => (g ≫ p) ≫ T.β) (fun _ => J (p ≫ T.β))
      (fun _ _ _ => rfl) (fun _ => mem_of_stalk (p ≫ T.β) z _ (hJ _) (Spec.map iR y))
    have e := e ()
    have := H _ (g ≫ p) q k₁ k₂ y J' hJ'
    rw [sval_of σ _ y J' (fun _ => J (p ≫ T.β)) (fun _ => e),
      sval_of s _ y J' (fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) (fun _ => by
        rw [Category.assoc, ← k₁, Category.assoc p', ← h₁]; exact e), q₁, q₂] at this
    have a₁ := gs_stalk p z _ (hJ.mem (fun _ : Fin 1 => T.β) p) (σ.f fun _ => J (p ≫ T.β)) iR y
    have a₂ := gs_stalk (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z _
      (hJ.mem (fun _ : Fin 1 => C.α) (p' ≫ (snd (TFK (R := R) F) C.A.A).left))
      (s.f fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) iR y
    have a₃ := gs_spec iL y c
    simp only [g, Category.assoc] at this a₁ a₂
    refine a₁.symm.trans (this.trans (Eq.trans (congrArg₂ (· * ·) a₃ a₂) ?_))
    refine (gs_mul _ y ⊤ trivial _ _).symm.trans (congrArg _ ?_)
    simp only [u, sval, Category.assoc]
    exact (map_mul _ _ _).symm
  refine mem_range_of_tmul_eq (O := O) (t := t) (u := u) hne (key.trans ?_)
  exact (Algebra.TensorProduct.tmul_mul_tmul c 1 1 u).trans (by rw [_root_.mul_one, _root_.one_mul])

end GlobalTheory.Mum.RatConst
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatingConstant_mem_traitFractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  atlas_forward_decl GlobalTheory.Mum.RatConst.main
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitDescent

theorem gs_one {Y Z : Scheme.{0}} (p : Z ⟶ Y) (z : Z) : gs p z ⊤ (1 : Γ(Y, ⊤)) = 1 := by
  rw [gs_eq p z ⊤ trivial, map_one, map_one]

theorem scal_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) (a b : A) :
    scal g (a * b) = scal g a * scal g b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one {A : Type} [CommRing A] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) : scal g 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem gs_scal_eq {A F : Type} [CommRing A] [Field F] {Y Z : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (io : A →+* F) (p : Z ⟶ Y) (q : Z ⟶ Spec (CommRingCat.of F)) (h : p ≫ g = q ≫ spMap io) (z : Z) (w : A) :
    gs p z ⊤ (scal g w) = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (io w)) := by
  have e1 := gs_pull p g z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w)
  have e2 := gs_pull q (spMap io) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w)
  have e3 : ((spMap io).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (io w) := by
    have := congrArg (fun f => f.hom w) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom io))
    exact this.symm
  unfold scal
  rw [← e3]
  exact e1.trans (h ▸ e2.symm)

end GlobalTheory.Mum.TraitDescent

noncomputable section
namespace GlobalTheory.Mum.TraitDescent

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem expBy_scale {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u a : W) {k : ℕ}
    {σ : SecK C.P.L.L T.β k} {F₀ : IntFam (maximalIdeal R) D.toPre k} (h : T.ExpBy u σ F₀) :
    ∃ σ₂ : SecK C.P.L.L T.β k, T.ExpBy (a * u) σ₂ F₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J,
      Good C.P.L.L z J → sval σ₂ r z J = gs r z ⊤ (scal T.G.hom a) * sval σ r z J := by
  obtain ⟨σ', f', hc, hp, he⟩ := h
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J, Good C.P.L.L z J →
      sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal T.G.hom a) σ) r z J = gs r z ⊤ (scal T.G.hom a) * sval σ r z J :=
    fun Z r z J hJ => sval_scale _ σ r z hJ
  refine ⟨_, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hp, he⟩, hv⟩
  rw [hv Z r z J hJ, hc Z r z J J' hJ hJ', scal_mul, gs_mul r z ⊤ trivial]
  ring

end GlobalTheory.Mum.TraitDescent

noncomputable section
namespace GlobalTheory.Mum.TraitDescent

theorem exp_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  intro R _ _ _ hR D C k W _ _ _ T F _ _ _ _ hF Φ c hc h1 h2
  by_cases hB : ∃ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ ∧ ∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0
  · obtain ⟨F₀, σ, hσ, hw⟩ := hB
    obtain ⟨x, hx⟩ := GlobalTheory.T.relatingConstant_mem_traitFractionField R hR D C k W T F hF σ (Φ F₀) c (h2 F₀ σ hσ) hw
    have hx0 : x ≠ 0 := by rintro rfl; exact hc (by rw [← hx, map_zero])
    obtain ⟨⟨b, ⟨a, ha⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors W) x
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hb0 : b ≠ 0 := by rintro rfl; exact hx0 (by simp)
    have key : ((algebraMap (FractionRing W) F).comp (algebraMap W _)) a * c =
        ((algebraMap (FractionRing W) F).comp (algebraMap W _)) b := by
      rw [← hx, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, mul_comm]
      congr 1
      exact IsLocalization.mk'_spec (FractionRing W) b ⟨a, ha⟩
    refine ⟨b, a, hb0, ha0, fun F₁ => ?_⟩
    obtain ⟨σ₁, hσ₁⟩ := h1 F₁
    obtain ⟨σ₂, hσ₂, hv⟩ := expBy_scale T 1 a hσ₁
    rw [_root_.mul_one] at hσ₂
    refine ⟨σ₂, hσ₂, GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct R hR D C k W T F hF σ₂ (Φ F₁) b ?_⟩
    intro Z p p' e1 e2 z J hJ
    have e2' : p ≫ T.G.hom = (p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫
        spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by rw [e2, Category.assoc]
    have ga := gs_scal_eq T.G.hom ((algebraMap (FractionRing W) F).comp (algebraMap W _)) p _ e2' z a
    have gb := gs_scal_eq T.G.hom ((algebraMap (FractionRing W) F).comp (algebraMap W _)) p _ e2' z b
    rw [hv Z p z J hJ, h2 F₁ σ₁ hσ₁ Z p p' e1 e2 z J hJ, ga, gb, ← _root_.mul_assoc, ← gs_mul _ z ⊤ trivial, fnF, ← map_mul, key]
  · push_neg at hB
    refine ⟨1, 1, one_ne_zero, one_ne_zero, fun F₀ => ?_⟩
    obtain ⟨σ, hσ⟩ := h1 F₀
    refine ⟨σ, hσ, GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct R hR D C k W T F hF σ (Φ F₀) 1 ?_⟩
    intro Z p p' e1 e2 z J hJ
    have h0 := hB F₀ σ hσ Z p p' e1 e2 z J hJ
    have e := h2 F₀ σ hσ Z p p' e1 e2 z J hJ
    rw [h0] at e
    rw [h0, scal_one, gs_one, _root_.one_mul]
    have hu : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c⁻¹) *
        gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) = 1 := by
      rw [← gs_mul _ z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ hc, map_one, gs_one]
    rw [← _root_.one_mul (sval (Φ F₀) _ z J), ← hu, _root_.mul_assoc, ← e, mul_zero]

end GlobalTheory.Mum.TraitDescent
end
end
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitExpansion_descends_from_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  atlas_forward_decl GlobalTheory.Mum.TraitDescent.exp_of_values
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_field_over_trait : ∀ (R : Type) [CommRing R] [IsDomain R] (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F) (_ : Algebra (FractionRing W) F) (_ : Kb R →ₐ[FractionRing R] F), ∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r)) := by
  intro R _ _ W _ _ φ hφ
  let g : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) (Kb W) := (IsFractionRing.lift (K := FractionRing R) hg).toAlgebra
  refine ⟨Kb W, inferInstance, inferInstance, inferInstance, inferInstance, IsAlgClosed.lift, fun r => ?_⟩
  exact IsFractionRing.lift_algebraMap hg r

theorem exists_map_exp_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  intro R _ _ _ hR D C j
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  have h1 : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  obtain ⟨wA, hwA⟩ := C.α_lb
  have hL : C.P.L.L.IsLB := by first | exact C.P.L.isLB | exact C.P.L.hL | exact C.P.L.lb
  have hL' : C.A.L.IsLB := C.A.isLB
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  · obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
    obtain ⟨K₀, _, _, _, _, em₀, hK₀⟩ := exists_field_over_trait R W₀ T₀.φ T₀.inj
    obtain ⟨lab, E, hlab, hE, -⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W₀ T₀ K₀ em₀ hK₀
    obtain ⟨Eb, hEb⟩ := GlobalTheory.Mum.Desc.eqv_down R hR D C.A (C.n ^ j) hodd (C.lab j) K₀ em₀ lab E hlab hE
    have hgal := GlobalTheory.Mum.labExt_of_trait R hR D C j W₀ ⟨T₀⟩
    obtain ⟨Φ₀, E₀, hE₀, hΦ₀⟩ := GlobalTheory.Mum.exists_eqv_rational R hR D C.A (C.n ^ j) hodd (C.lab j) Eb hEb hgal
    choose Φ hΦ using fun F₀ => GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso C.P.L.L C.A.L C.α wA hL hL' hwA (C.n ^ j) (Φ₀ F₀)
    refine ⟨Φ, fun W _ _ _ T => ?_⟩
    obtain ⟨K, _, _, _, _, em, hK⟩ := exists_field_over_trait R W T.φ T.inj
    obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure R hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W T K em hK
    exact GlobalTheory.T.traitExpansion_descends_from_algClosed_field R hR D C (C.n ^ j) W T K hK Φ c hc (fun F₀ => GlobalTheory.T.exists_integralSection_expanding_thetaFamily R hR D C (C.n ^ j) h1 W T F₀) hcv
  · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_thetaExpansion_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  atlas_forward_decl GlobalTheory.Mum.exists_map_exp_all_traits
end
