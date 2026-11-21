import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricFibreIsoOfTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFiel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemma

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∀ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) → GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ UniTrait D₁.toPre A := by
  first | exact @GlobalTheory.Mum.ClosureDescent.exists_uniTrait | exact GlobalTheory.Mum.ClosureDescent.exists_uniTrait | (intros; apply GlobalTheory.Mum.ClosureDescent.exists_uniTrait <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_pow_left {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {a : G'.left ⟶ G.left} (h : IsGrpPullback G' G f a) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ a) : ∀ n : ℕ, (x₀ ^ n).left = (x ^ n).left ≫ a := by
  intro n
  induction n with
  | zero =>
    let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ a) (by
      show ((1 : T ⟶ G').left ≫ a) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    have hm := h.2 T 1 1 u u rfl rfl
    rw [_root_.mul_one] at hm
    have hu : u * u = u := Over.OverMorphism.ext hm
    have hu1 : u = 1 := mul_eq_left.1 hu
    rw [pow_zero, pow_zero, ← hu1]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T (x ^ n) x (x₀ ^ n) x₀ ih hx

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oneTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ →
    ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A →
      ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  intro R _ _ _ hR D A hU
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, hW, hφ, hloc, hG', ga, hga, hpb, hLa⟩ := hU
  haveI : CharZero R := hR.2
  haveI : CharZero W := charZero_of_injective_ringHom hφ
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI iW : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have tf : ∀ (K M : Type) [Field K] [Field M] [Algebra K M], Module.IsTorsionFree K M := fun _ _ _ _ _ => inferInstance
  haveI := tf (FractionRing R) (Kb W)
  haveI := tf (FractionRing R) (Kb R)
  let em : Kb R →ₐ[FractionRing R] Kb W := IsAlgClosed.lift
  have hF : ∀ r, algebraMap (FractionRing R) (Kb W) (algebraMap R _ r) =
      algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r)) := fun r =>
    congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (Kb R) := charZero_of_injective_ringHom (algebraMap (FractionRing R) (Kb R)).injective
  haveI : CharZero (Kb W) := charZero_of_injective_ringHom em.toRingHom.injective
  haveI := GlobalTheory.ArcExt.epi_spMap em.toRingHom
  have hρ : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact em.commutes x
  let ρ : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap em.toRingHom) hρ
  let Φ : (TFK (R := R) (Kb R) ⟶ A.A) →* (Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A) :=
    MonoidHom.mk' (fun y => ρ ≫ y) fun x y => by rw [MonObj.comp_mul]
  have hΦ : ∀ y, (Φ y).left = spMap em.toRingHom ≫ y.left := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext
    ((cancel_epi (spMap em.toRingHom)).1 ((hΦ x).symm.trans ((congrArg (fun q => q.left) e).trans (hΦ y))))
  have desc : ∀ k : ℕ, 1 ≤ k → ∀ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z ^ k = 1 →
      ∃ y : TFK (R := R) (Kb R) ⟶ A.A, Φ y = z := by
    intro k hk z hz
    let u : {y : TFK (R := R) (Kb R) ⟶ A.A // y ^ k = 1} →
        {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      fun y => ⟨Φ y.1, by rw [← map_pow, y.2, map_one]⟩
    have hu : Function.Injective u := fun y y' e => Subtype.ext (hΦinj (congrArg Subtype.val e))
    have c := GlobalTheory.ArcExt.card_torsion hL A (jFK (R := R) (Kb R)) (n := k) (Nat.cast_ne_zero.2 (by omega))
    have c' := GlobalTheory.ArcExt.card_torsion hL A ((TFK (R := W) (Kb W)).hom ≫ spMap ga) (n := k)
      (Nat.cast_ne_zero.2 (by omega))
    haveI : Finite {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c']; positivity)
    obtain ⟨y, e⟩ := (hu.bijective_of_nat_card_le (c'.trans c.symm).le).2 ⟨z, hz⟩
    exact ⟨y.1, congrArg Subtype.val e⟩
  have toA : ∀ (k : ℕ) (x' : TFK (R := W) (Kb W) ⟶ A'.A), x' ^ k = 1 →
      ∃ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z.left = x'.left ≫ a ∧ z ^ k = 1 := by
    intro k x' hx
    let z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A := Over.homMk (x'.left ≫ a) (by
      show (x'.left ≫ a) ≫ A.A.hom = (TFK (R := W) (Kb W)).hom ≫ spMap ga
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w])
    refine ⟨z, rfl, Over.OverMorphism.ext ?_⟩
    rw [grpPullback_pow_left hpb x' z rfl k, hx]
    exact ((grpPullback_pow_left hpb x' z rfl 0).trans (by rw [pow_zero])).symm
  have key : ∀ (k : ℕ) (p : QkPt D.toPre (Kb R) k), ∃ y : TFK (R := R) (Kb R) ⟶ A.A, 1 ≤ k →
      ∀ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k) (x' : TFK (R := W) (Kb W) ⟶ A'.A),
        QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD (Kb W) p₁.g p'.g →
        x'.left ≫ a = spMap em.toRingHom ≫ y.left → QkToAkU U'.toUnifPre (Kb W) k p' x' := by
    intro k p
    by_cases hk : 1 ≤ k
    swap
    · exact ⟨1, fun h => absurd h hk⟩
    by_cases hex : ∃ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k),
        QkExt em.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD (Kb W) p₁.g p'.g
    swap
    · exact ⟨1, fun _ p₁ p' _ h₁ h₂ h₃ _ => absurd ⟨p₁, p', h₁, h₂, h₃⟩ hex⟩
    obtain ⟨p₁, p', h₁, h₂, h₃⟩ := hex
    obtain ⟨f, hf, hfk⟩ := GlobalTheory.TorsionIso.torsion_clause W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
    obtain ⟨z, hz, hzk⟩ := toA k (f p') (hfk p')
    obtain ⟨y, hy⟩ := desc k hk z hzk
    refine ⟨y, fun _ q₁ q' x' e₁ e₂ e₃ e₄ => ?_⟩
    obtain rfl : q₁ = p₁ := GlobalTheory.DegActCompare.qkExt_unique e₁ h₁
    obtain rfl : q' = p' := GlobalTheory.TorusExt.qk_ext (e₂.trans h₂.symm) (GlobalTheory.ArcPull.pullGt_unique hD hF e₃ h₃)
    rw [(hf.1 q' x')]
    refine Over.OverMorphism.ext (hpb.1.hom_ext ?_ ?_)
    · rw [e₄, ← hz, ← hy]
      exact (hΦ y).symm
    · rw [Over.w x', Over.w (f q')]
  choose lab hlab using key
  exact ⟨lab, W, inferInstance, inferInstance, inferInstance, φ, G', inferInstance, inferInstance, D', A', U', hD, a, iW, em,
    hW, hφ, hloc, hG', ⟨ga, hga, hpb, hLa⟩, hF, fun k hk p p₁ p' x' h₁ h₂ h₃ h₄ => hlab k p hk p₁ p' x' h₁ h₂ h₃ h₄⟩

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  atlas_forward_decl GlobalTheory.Mum.exists_oneTrait
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_realising : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (E : IntermediateField (FractionRing R₁) (Kb R₁)), FiniteDimensional (FractionRing R₁) E → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ ∧ FinExt (i₁₂.comp ρ) ∧ IsLocalHom i₁₂ ∧ ∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r) := by
  intro R _ _ _ hR R₁ _ _ _ ρ hρ E hE
  obtain ⟨hadm, hinj, hfin⟩ := hρ
  haveI : CharZero R := hR.2
  haveI : CharZero R₁ := charZero_of_injective_ringHom hinj
  have hR₁ : Base R₁ := ⟨hadm, inferInstance⟩
  let E' := IntermediateField.normalClosure (FractionRing R₁) E (Kb R₁)
  haveI : IsGalois (FractionRing R₁) E' := inferInstance
  haveI : FiniteDimensional (FractionRing R₁) E' := inferInstance
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E') hR₁
  letI : Algebra R₁ E' := (baseMap R₁ E').toAlgebra
  haveI : IsScalarTower R₁ (FractionRing R₁) E' := IsScalarTower.of_algebraMap_eq' rfl
  set R₂ := integralClosure R₁ E'
  haveI : IsFractionRing R₂ E' := integralClosure.isFractionRing_of_finite_extension (FractionRing R₁) E'
  let incl : E →ₐ[FractionRing R₁] E' := IntermediateField.inclusion (IntermediateField.le_normalClosure E)
  let eqv : E' ≃ₐ[R₂] FractionRing R₂ := (FractionRing.algEquiv R₂ E').symm
  have hloc' : IsLocalHom (algebraMap R₁ R₂) := by
    haveI : Module.Finite R₁ R₂ := RingHom.finite_algebraMap.1 hfe.2.2
    have : (Ideal.comap (algebraMap R₁ R₂) (maximalIdeal R₂)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R₂)
    exact ((local_hom_TFAE (algebraMap R₁ R₂)).out 0 4).mpr (IsLocalRing.eq_maximalIdeal this)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R₁ R₂, eqv.toRingHom.comp incl.toRingHom, hfe,
    ⟨hfe.1, hfe.2.1.comp hinj, hfe.2.2.comp hfin⟩, hloc', fun r => ?_⟩
  have h1 : incl (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ E' (algebraMap R₁ R₂ r) :=
    incl.commutes _
  change eqv (incl _) = _
  rw [h1]
  exact eqv.commutes _

end GlobalTheory.GalClosure
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_realising_subextension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (E : IntermediateField (FractionRing R₁) (Kb R₁)), FiniteDimensional (FractionRing R₁) E → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ ∧ FinExt (i₁₂.comp ρ) ∧ IsLocalHom i₁₂ ∧ ∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r) := by
  atlas_forward_decl GlobalTheory.GalClosure.exists_finExt_realising
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkPt_rational_of_pull : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ → IsLocalHom i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p := by
  intro R₁ _ _ _ hR D₁ n hn
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hG := hL.globalFns
  have hB₁ := D₁.tau_bimult
  have := hR.2
  have : CharZero (Kb R₁) := (RingHom.charZero_iff (algebraMap (FractionRing R₁) (Kb R₁)).injective).1 inferInstance
  obtain ⟨M, hM, H⟩ := GlobalTheory.QkNumberField.exists_finite_qk (D := D₁.toPre) (L := Kb R₁) hL hB₁ (N := n)
    (Nat.cast_ne_zero.2 (by omega))
  refine ⟨M, hM, ?_⟩
  intro R₂ _ _ _ i₁₂ e hfin _ he D₂ ⟨hD⟩ p
  have hB₂ := D₂.tau_bimult
  have hi : Function.Injective i₁₂ := hfin.2.1
  letI : Algebra (FractionRing R₁) (FractionRing R₂) := (fracMap hi).toAlgebra
  have he' : e.comp (algebraMap (FractionRing R₁) M) = algebraMap (FractionRing R₁) (FractionRing R₂) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => (he r).trans (fracMap_algebraMap hi r).symm)
  letI : Algebra (FractionRing R₁) (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp (fracMap hi)).toAlgebra
  have cK : Compat i₁₂ (Kb R₂) := fun r => congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (fracMap_algebraMap hi r)
  have cF : Compat i₁₂ (FractionRing R₂) := fracMap_algebraMap hi
  letI : Algebra M (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp e).toAlgebra
  haveI : Module.IsTorsionFree M (Kb R₂) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree M (Kb R₁) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic M (Kb R₁) := Algebra.IsAlgebraic.tower_top (K := FractionRing R₁) M
  let σ' : Kb R₁ →ₐ[M] Kb R₂ := IsAlgClosed.lift
  have hσ' : ∀ m : M, σ' (m : Kb R₁) = algebraMap (FractionRing R₂) (Kb R₂) (e m) := fun m => σ'.commutes m
  let σ : Kb R₁ →ₐ[FractionRing R₁] Kb R₂ := ⟨σ'.toRingHom, fun x => by
    show σ' (algebraMap (FractionRing R₁) (Kb R₁) x) = _
    exact (hσ' (algebraMap (FractionRing R₁) M x)).trans (congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.congr_fun he' x))⟩
  have key : σ.toRingHom.comp M.val.toRingHom = (algebraMap (FractionRing R₂) (Kb R₂)).comp e :=
    RingHom.ext fun m => hσ' m
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG cK hB₁ hB₂ p
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.LabTrans.exists_of_ext hB₁ σ hn q
  obtain ⟨z, rfl⟩ := H n dvd_rfl q₀
  let z' : QkPt D₁.toPre (FractionRing R₂) n := qkExt hB₁ e he' z
  let p₀ := pullQk hD hG cF hB₁ hB₂ z'
  let p₁ := qkExt hB₂ (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.comp_id _) p₀
  have hp₁ : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ := (qkExt_iff hB₂ _ _ _ _).2 rfl
  have hf₂ : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₁) (FractionRing R₂)) =
      algebraMap (FractionRing R₁) (Kb R₂) := rfl
  let w := qkExt hB₁ (algebraMap (FractionRing R₂) (Kb R₂)) hf₂ z'
  have hw : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) z' w := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz' : QkExt e z z' := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz : QkExt M.val.toRingHom z (qkExt hB₁ M.val.toRingHom (GlobalTheory.QkNumberField.val_comp M) z) :=
    (qkExt_iff hB₁ _ _ _ _).2 rfl
  have t₁ := GlobalTheory.LabTrans.qkExt_trans hz hq₀
  have t₂ := GlobalTheory.LabTrans.qkExt_trans hz' hw
  rw [← key] at t₂
  have hqw : q = w := GlobalTheory.QkClosure.qkExt_unique (σ.toRingHom.comp M.val.toRingHom) (σ.comp_algebraMap ▸ rfl) t₁ t₂
  refine ⟨p₀, p₁, hp₁, ?_⟩
  have e₁ : p₁ = pullQk hD hG cK hB₁ hB₂ q := by
    rw [eq_pullQk_iff]
    refine ⟨?_, ?_⟩
    · rw [hqw]; rfl
    · rw [hqw]
      exact isPullGtF_ext hD cK _ (RingHom.comp_id _) (isPullGtF_pullGt hD hG cF z'.g) hw hp₁
  rw [e₁]
  exact qk_equiv_refl hB₂ _

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationQuotientPoints_rational_finiteExtension : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ → IsLocalHom i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p := by
  atlas_forward_decl GlobalTheory.Mum.qkPt_rational_of_pull
end

section
open Polynomial

namespace GlobalTheory.FiniteFieldOfPoints

theorem factor_of_range {C K₂ Ω : Type} [CommRing C] [Field K₂] [Field Ω]
    (j : K₂ →+* Ω) (ψ : C →+* Ω) (h : ∀ c, ∃ x, j x = ψ c) :
    ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · ext c; simp [hf]

theorem exists_finite_field_of_points (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C)
    (hφ : RingHom.Finite φ) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)), FiniteDimensional K ↥E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : ↥E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        RingHom.comp ψ φ = RingHom.comp j (RingHom.comp e (algebraMap K ↥E)) →
        ∃ (ψ₀ : C →+* K₂), RingHom.comp j ψ₀ = ψ := by
  classical
  letI : Algebra K C := φ.toAlgebra
  haveI : Module.Finite K C := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := C)
  have hint : ∀ c : C, IsIntegral K c := fun c => Algebra.IsIntegral.isIntegral c
  choose p hpm hpe using hint
  set P : K[X] := ∏ c ∈ s, p c with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ (fun c _ => hpm c)
  have hsf : IsSplittingField K
      (IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  refine ⟨IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)),
    IsSplittingField.finiteDimensional _ P, ?_⟩
  generalize IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)) = E at hsf ⊢
  intro K₂ Ω _ _ e j ψ hc
  have hspl : (P.map (algebraMap K E)).Splits := hsf.splits'
  have hspl2 : (P.map (e.comp (algebraMap K E))).Splits := by
    rw [← Polynomial.map_map]; exact hspl.map e
  have hgen : ∀ c ∈ s, ψ c ∈ j.range := by
    intro c hcs
    have h0 : eval₂ φ c P = 0 := by
      rw [hP, eval₂_finsetProd]
      exact Finset.prod_eq_zero hcs (hpe c)
    have h1 : ((P.map (e.comp (algebraMap K E))).map j).IsRoot (ψ c) := by
      rw [Polynomial.map_map, ← hc, IsRoot, eval_map, ← hom_eval₂, h0, map_zero]
    exact hspl2.mem_range_of_isRoot (hPm.map _).ne_zero h1
  apply factor_of_range
  intro c
  have hmem : c ∈ Submodule.span K (s : Set C) := by rw [hs]; trivial
  change ψ c ∈ j.range
  induction hmem using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    refine ⟨e (algebraMap K E a), ?_⟩
    exact (RingHom.congr_fun hc a).symm

end GlobalTheory.FiniteFieldOfPoints
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatTors

open Polynomial in

theorem exists_split_ext (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C) (hφ : φ.Finite) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        ψ.comp φ = j.comp (e.comp (algebraMap K E)) → ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  first
  | exact @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | (apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points ..)

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

theorem exists_finite_tors (K : Type) [Field K] (A : PolAV (Sp K)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (C : Type) (_ : CommRing C) (φ : K →+* C) (p : Sp C ⟶ A.A.left), φ.Finite ∧ p ≫ A.A.hom = spMap φ ∧
      ∀ (Ω : Type) [Field Ω] (y : Sp Ω ⟶ A.A.left),
        y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left → ∃ ψ : C →+* Ω, y = spMap ψ ≫ p := by
  have hF : IsFinite (mulA A.A n).left := (GlobalTheory.firstFiveLaws.1.mulN (Sp K) A n hn).1
  haveI : IsAffine ((𝟙_ (Over (Sp K))).left) := (inferInstance : IsAffine (Sp K))
  let f := (mulA A.A n).left
  let g := (η[A.A]).left
  haveI : IsFinite f := hF
  haveI hY : IsFinite (pullback.snd f g) := inferInstance
  haveI : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  let Y := pullback f g
  let q : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd f g
  let φ₀ := Spec.preimage q
  have hq : spMap φ₀.hom = q := Spec.map_preimage q
  have hfst : pullback.fst f g ≫ A.A.hom = pullback.snd f g := by
    have h1 : f ≫ A.A.hom = A.A.hom := Over.w (mulA A.A n)
    have h2 : g ≫ A.A.hom = 𝟙 _ := Over.w (η[A.A])
    rw [← h1, ← Category.assoc, pullback.condition, Category.assoc, h2, Category.comp_id]
  refine ⟨Γ(Y, ⊤), inferInstance, φ₀.hom, Y.isoSpec.inv ≫ pullback.fst f g, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff]
    change IsFinite (spMap φ₀.hom)
    rw [hq]
    infer_instance
  · rw [hq, Category.assoc, hfst]
  · intro Ω _ y hy
    let z : Sp Ω ⟶ Y := pullback.lift y (y ≫ A.A.hom) (by rw [hy, Category.assoc])
    let w : Sp Ω ⟶ Sp Γ(Y, ⊤) := z ≫ Y.isoSpec.hom
    refine ⟨(Spec.preimage w).hom, ?_⟩
    change y = Spec.map (Spec.preimage w) ≫ _
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

section Push
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem mulA_push (h : IsGrpPullback G' G f φ) (n : ℕ) : (mulA G' n).left ≫ φ = φ ≫ (mulA G n).left := by
  have e := congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e2 : (pushHom h G' (𝟙 G')) ^ n = pushHom h G' (𝟙 G') ≫ mulA G n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e2] at e
  calc (mulA G' n).left ≫ φ = (pushHom h G' (𝟙 G' ^ n)).left := rfl
    _ = (pushHom h G' (𝟙 G') ≫ mulA G n).left := e
    _ = (𝟙 G'.left ≫ φ) ≫ (mulA G n).left := rfl
    _ = _ := by rw [Category.id_comp]

theorem eta_push (h : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (Over.mk (𝟙 S'))))
  have e' : (𝟙 S' ≫ (η[G']).left) ≫ φ = (𝟙 S' ≫ f) ≫ (η[G]).left := e
  rwa [Category.id_comp, Category.id_comp] at e'

end Push

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

theorem spMap_inj {P Q : Type} [CommRing P] [CommRing Q] {u v : P →+* Q} (h : spMap u = spMap v) : u = v :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem torsion_rational : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (A : PolAV (Sp (FractionRing R₁))) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), Function.Injective i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → ∃ x₀ : Sp (FractionRing R₂) ⟶ A₂.A.left, x.left = spMap (algebraMap (FractionRing R₂) (Kb R₂)) ≫ x₀ := by
  intro R₁ _ _ _ _ A n hn
  obtain ⟨C, _, φ, p, hφ, hp, hpt⟩ := exists_finite_tors _ A n hn
  obtain ⟨E, hE, hEs⟩ := exists_split_ext (FractionRing R₁) C φ hφ
  refine ⟨E, hE, ?_⟩
  rintro R₂ _ _ _ i₁₂ e _ he A₂ a ⟨ga, hga, hpb, -⟩ x hx
  let j := algebraMap (FractionRing R₂) (Kb R₂)
  have hge : ga = e.comp (algebraMap (FractionRing R₁) E) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hga, RingHom.comp_apply, he])
  let y := x.left ≫ a
  have hxh : x.left ≫ A₂.A.hom = spMap j := Over.w x
  have hyh : y ≫ A.A.hom = spMap j ≫ spMap ga := by
    change (x.left ≫ a) ≫ A.A.hom = _
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hxh]
  have h1 : x.left ≫ (mulA A₂.A n).left = spMap j ≫ (η[A₂.A]).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx]
    rfl
  have htors : y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left := by
    change (x.left ≫ a) ≫ _ = (x.left ≫ a) ≫ _
    rw [Category.assoc, ← mulA_push hpb, ← Category.assoc, h1, Category.assoc, eta_push hpb,
      ← Category.assoc (x.left ≫ a), hyh, Category.assoc]
  obtain ⟨ψ, hψ⟩ := hpt (Kb R₂) y htors
  have hψφ : ψ.comp φ = j.comp ga := by
    refine spMap_inj ?_
    rw [GlobalTheory.Ex.spMap_comp', GlobalTheory.Ex.spMap_comp', ← hp, ← Category.assoc, ← hψ, hyh]
  obtain ⟨ψ₀, hψ₀⟩ := hEs (FractionRing R₂) (Kb R₂) e j ψ (by rw [hψφ, hge])
  have hψ₀φ : ψ₀.comp φ = ga := by
    refine RingHom.ext fun r => j.injective ?_
    have := RingHom.congr_fun hψφ r
    rw [← hψ₀] at this
    exact this
  let y₀ : Sp (FractionRing R₂) ⟶ A.A.left := spMap ψ₀ ≫ p
  have hy₀ : y₀ ≫ A.A.hom = 𝟙 _ ≫ spMap ga := by
    change (spMap ψ₀ ≫ p) ≫ _ = _
    rw [Category.assoc, hp, ← GlobalTheory.Ex.spMap_comp', hψ₀φ, Category.id_comp]
  refine ⟨hpb.1.lift y₀ (𝟙 _) hy₀, hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hpb.1.lift_fst]
    change y = _
    rw [hψ, ← hψ₀, GlobalTheory.Ex.spMap_comp', Category.assoc]
  · rw [Category.assoc, hpb.1.lift_snd, Category.comp_id, hxh]

end GlobalTheory.Mum.RatTors
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_fraction_field_uniform : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (A : PolAV (Sp (FractionRing R₁))) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), Function.Injective i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → ∃ x₀ : Sp (FractionRing R₂) ⟶ A₂.A.left, x.left = spMap (algebraMap (FractionRing R₂) (Kb R₂)) ≫ x₀ := by
  atlas_forward_decl GlobalTheory.Mum.RatTors.torsion_rational
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UniEnlarge

open GlobalTheory.Mum.ClosureDescent GlobalTheory.ThetaDescent

theorem uniTrait_of_finExt : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  intro R₁ _ _ _ _ D₁ A hU R₂ _ _ _ i₁₂ hi₁₂ hl₁₂ D₂ ⟨hD₂⟩ A₂ a₂ hA₂
  classical
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD', a, hW, hφ, hφl, hG', ga, hga, g₁, l₁⟩ := hU
  obtain ⟨ga₂, hga₂, g₂, l₂⟩ := hA₂
  have hfin : i₁₂.Finite := hi₁₂.2.2
  let β : FractionRing W →+* AlgebraicClosure (FractionRing W) := algebraMap _ _
  have hβ : β.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := FractionRing W) x
  obtain ⟨j₁, hj₁⟩ := exists_extend hfin (algebraMap R₁ (FractionRing R₁)) ga₂ (RingHom.ext fun r => hga₂ r)
    (β.comp ga)
  have hjρ : ∀ r, j₁ (algebraMap R₂ _ (i₁₂ r)) = β (((algebraMap W (FractionRing W)).comp φ) r) := fun r => by
    rw [← hga₂, ← RingHom.comp_apply j₁ ga₂, hj₁, RingHom.comp_apply, hga, RingHom.comp_apply]
  obtain ⟨s₀, hs₀⟩ := exists_range_le_gen hfin β ((algebraMap W _).comp φ) j₁ hjρ
  let i := β.codRestrict _ (mem_gen β s₀)
  let k := j₁.codRestrict _ hs₀
  have hi : i.Finite := finite_gen β hβ s₀
  have := hW.1
  have hWb : Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩, hW.2.2⟩
  obtain ⟨W₁, _, _, _, io, σ, hio, hiol, hσ⟩ := GlobalTheory.CommonCover.exists_cover_field W hWb _ i hi
  obtain ⟨D₃, hD₃, A₃, U₃, a₃, hA₃⟩ := exists_unif_fib hWb.1 hio.1 io hio.2.1 (map_maximalIdeal_le io) hG' U'
    (σ.comp i) ((RingHom.comp_assoc _ _ _).trans hσ)
  have f₁ : Fib A₃ A ((σ.comp i).comp ga) (a₃ ≫ a) := hA₃.comp ⟨g₁, l₁⟩ rfl
  have e : (σ.comp k).comp ga₂ = (σ.comp i).comp ga := RingHom.ext fun x =>
    congrArg σ (Subtype.ext (DFunLike.congr_fun hj₁ x))
  obtain ⟨d, -, hd⟩ := Fib.cancel (σ.comp k) (⟨g₂, l₂⟩ : Fib A₂ A ga₂ a₂) f₁ e
  haveI := hio.1.2.2.1
  obtain ⟨φ₂, hφ₂, hcomp, hinj, hl⟩ := exists_restrict hfin (io.comp φ) (σ.comp k) fun r => by
    have e₁ : k (algebraMap R₂ _ (i₁₂ r)) = i (algebraMap W _ (φ r)) := Subtype.ext (hjρ r)
    exact (congrArg σ e₁).trans (DFunLike.congr_fun hσ (φ r))
  obtain ⟨q⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ hio.2.1 hD' hD₃
  rw [← hcomp] at q
  obtain ⟨q₁⟩ := GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel hi₁₂.2.1 hinj hD₂ q
  exact ⟨W₁, _, _, _, φ₂, _, inferInstance, inferInstance, D₃, A₃, U₃, q₁, d, cDvr_of_finExt hW hio, hinj, hl,
    IsSemiAbelian.pullback _ G' hG', σ.comp k, hφ₂, hd.1, hd.2⟩

end GlobalTheory.Mum.UniEnlarge
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedTrait_moves_to_finite_extension : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  atlas_forward_decl GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_fixes_quotientPoints_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  first | exact @GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | exact GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | (intros; apply GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Enlarge

theorem exists_rational_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D n hn hodd hnu R₁ _ _ _ ρ D₁ A hρ hP hS hU
  have hn1 : 1 ≤ n := hn.one_lt.le
  have hR₁ : Base R₁ := ⟨hρ.1, by haveI := hR.2; exact charZero_of_injective_ringHom hρ.2.1⟩
  obtain ⟨EQ, fQ, hQ⟩ := GlobalTheory.T.degenerationQuotientPoints_rational_finiteExtension R₁ hR₁ D₁ n hn1
  obtain ⟨EA, fA, hA⟩ := GlobalTheory.T.exists_finite_extension_fraction_field_uniform R₁ hR₁ A n hn1
  haveI := fQ
  haveI := fA
  obtain ⟨R₂, _, _, _, i₁₂, e, hi₁₂, hi₁₂ρ, hloc, he⟩ := GlobalTheory.T.exists_finiteExtension_realising_subextension R hR R₁ ρ hρ (EQ ⊔ EA) inferInstance
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ i₁₂ hi₁₂.2.1 hloc D₁
  have hP₂ := nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ i₁₂ D.toPre D₁.toPre D₂.toPre hi₁₂.2.1 hP hD₂
  have hle : nonZeroDivisors R₁ ≤ (nonZeroDivisors R₂).comap i₁₂ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i₁₂ hi₁₂.2.1
  let ga : FractionRing R₁ →+* FractionRing R₂ := IsLocalization.map (FractionRing R₂) i₁₂ hle
  obtain ⟨A₂, g, hg, -, hm, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap ga) A
  have gp : IsGrpPullback A₂.A A.A (spMap ga) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact congrArg (·.left) (hm T x y).symm⟩
  have hlb : LBIso A₂.L (A.L.pull g) := LBIso.symm ⟨t, ht⟩
  have hfib : IsFib i₁₂ A A₂ g := ⟨ga, fun r => IsLocalization.map_eq hle r, gp, hlb⟩
  have hS₂ : (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) := by
    letI := A.isAb.comm
    letI := A₂.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A A₂.A (spMap ga) g A.L A₂.L A.isLB A₂.isLB gp hlb hS
  let eQ : EQ →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_left : EQ ≤ EQ ⊔ EA)).toRingHom
  let eA : EA →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_right : EA ≤ EQ ⊔ EA)).toRingHom
  have hrat := hQ R₂ i₁₂ eQ hi₁₂ hloc (fun r => he r) D₂ hD₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, i₁₂.comp ρ, D₂, A₂, hi₁₂ρ, hP₂, hS₂,
    GlobalTheory.T.uniformisedTrait_moves_to_finite_extension R₁ hR₁ D₁ A hU R₂ i₁₂ hi₁₂ hloc D₂ hD₂ A₂ g hfib, fun σ => ⟨GlobalTheory.T.galois_fixes_quotientPoints_of_rational R₂ D₂ n hrat σ, fun x hx => ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ := hA R₂ i₁₂ eA hi₁₂.2.1 (fun r => he r) A₂ g hfib x hx
  rw [hx₀, ← Category.assoc, ← spMap_comp]
  exact congrArg (fun f => spMap f ≫ x₀) (RingHom.ext fun a => σ.commutes a)

end GlobalTheory.Mum.Enlarge
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_rational_torsion_uniformised_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  atlas_forward_decl GlobalTheory.Mum.Enlarge.exists_rational_ext
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalSquares

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_div {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    {k : ℕ} (l N : ℕ) (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) :
    ∃ q : QkPt D.toPre (Kb R) N, q.y = p.y ∧ l • q.g = p.g := by
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_nsmul_eq (F := Kb R) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1.1)
    (n := l) (by omega) p.g
  refine ⟨GlobalTheory.TorusExt.qkMk D.tau_bimult p.y g ?_, rfl, hg⟩
  rw [hN, mul_nsmul', hg]
  exact GlobalTheory.TorusExt.qk_nsmul D.tau_bimult p

theorem qkExt_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') {k N : ℕ}
    (l : ℕ) {p : QkPt D F k} {p' : QkPt D F' k} {q : QkPt D F N} (hp : QkExt σ.toRingHom p p') (hy : q.y = p.y)
    (hg : l • q.g = p.g) : ∃ q' : QkPt D F' N, QkExt σ.toRingHom q q' ∧ q'.y = p'.y ∧ l • q'.g = p'.g := by
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext σ.commutes
  refine ⟨GlobalTheory.TorusExt.qkExt hB σ.toRingHom hσ q, (GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).2 rfl, ?_, ?_⟩
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    exact hy
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    show l • GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ q.g = GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ p.g
    rw [← map_nsmul, hg]

theorem pow_left_of_comp {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (x y : TFK (R := R) (Kb R) ⟶ A.A) (h : y.left = spMap σ.toRingHom ≫ x.left)
    (l : ℕ) : (y ^ l).left = spMap σ.toRingHom ≫ (x ^ l).left := by
  let s : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap σ.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext σ.commutes))
  have hy : y = s ≫ x := Over.OverMorphism.ext h
  have hp : ∀ m : ℕ, s ≫ x ^ m = (s ≫ x) ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [hy, ← hp]
  rfl

theorem compPow {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (m : ℕ) :
    (ρ ≫ x) ^ m = ρ ≫ x ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem lab_level {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hO : OneTrait D.toPre A lab) (k l N : ℕ) (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) N) (hy : q.y = p.y)
    (hg : GtPtF.IsNsmul l q.g p.g) : (lab k p).left = ((lab N q) ^ l).left := by
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hl
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := (GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k l N hk hl hN
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab N q))).2
    (by show hD.xe.symm p.y = hD.xe.symm q.y; rw [hy])
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g) =
        l • GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g)
      rw [(GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hg, map_nsmul, map_nsmul])) (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₁).trans ((hf _ _).1 h₂).symm
  have hs : s ≫ lab k p = s ≫ lab N q ^ l := by
    have := congrArg e hx
    rw [e.apply_symm_apply, map_pow, e.apply_symm_apply] at this
    rw [this, compPow]
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs)

end GlobalTheory.Mum.GalSquares

open GlobalTheory.Mum.GalSquares in

theorem GlobalTheory.Mum.galEqN_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime →
    Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' →
        (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  intro R _ _ _ hR n hn _ _ D A lab hO ⟨i₀, H⟩ σ j p p' hpp'
  letI := GlobalTheory.TorusExt.gtGroup D.toPre (Kb R)
  have hi : i₀ ≤ max i₀ j := le_max_left _ _
  have hj : j ≤ max i₀ j := le_max_right _ _
  have hN : (n ^ max i₀ j) ^ 2 = n ^ j * n ^ (2 * max i₀ j - j) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hl : 1 ≤ n ^ (2 * max i₀ j - j) := Nat.one_le_pow _ _ hn.pos
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  obtain ⟨q, hqy, hqg⟩ := exists_div hR D _ _ hl hN p
  obtain ⟨q', hq', hq'y, hq'g⟩ := qkExt_nsmul D.toPre D.tau_bimult σ _ hpp' hqy hqg
  have e₁ := lab_level D A lab hO _ _ _ hk hl hN p q hqy ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hqg.symm)
  have e₂ := lab_level D A lab hO _ _ _ hk hl hN p' q' hq'y ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hq'g.symm)
  rw [e₂, pow_left_of_comp σ _ _ (H _ hi σ q q' hq'), ← e₁]
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_galois_all_levels_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  atlas_forward_decl GlobalTheory.Mum.galEqN_of_squares
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  intro R _ _ _ hR D A lab hT m hm hmu v H σ
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em₀, hW, hφ, hloc, -, -, -, -⟩ := hT
  obtain ⟨C, _, _, _, _, _, _, hC⟩ := GlobalTheory.Ex.StepInh.exists_cExt W hW
  have hg : Function.Injective ((algebraMap (FractionRing W) C).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) C).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) C := (IsFractionRing.lift hg).toAlgebra
  have hA : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) =
      algebraMap (FractionRing W) C (algebraMap W _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hg r
  haveI := hloc
  have hCR : GlobalTheory.Ex.CExt R (maximalIdeal R) C :=
    ⟨fun r => by rw [hA]; exact hC.1 _, fun r hr => by rw [hA]; exact hC.2 _ (map_nonunit φ r hr)⟩
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, nu, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 R D.toPre D.psi_even D.tau_bimult C ⊤
    (fun _ => trivial)
  have hB := D.tau_bimult
  let em : Kb R →ₐ[FractionRing R] C := IsAlgClosed.lift
  have hq := ((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N nu).2.2.2.2 (m ^ 2)).1
  choose e₁ he₁ using fun i => GlobalTheory.LabTrans.exists_ext hB em i
  choose e₂ he₂ using fun i => GlobalTheory.LabTrans.exists_ext hB σ i
  choose qq hqq using fun x : QkPt D.toPre C (m ^ 2) => (hq x).exists
  obtain ⟨s, hs⟩ := H C hCR em N nu e₁ (fun i => qq (e₁ i)) he₁ (fun i => hqq _)
  obtain ⟨s', hs'⟩ := H C hCR (em.comp σ) N nu (fun i => e₁ (e₂ i)) (fun i => qq (e₁ (e₂ i)))
    (fun i => GlobalTheory.LabTrans.qkExt_trans (he₂ i) (he₁ (e₂ i))) (fun i => hqq _)
  have key : ∀ p p', QkExt σ.toRingHom p p' → em (σ (v p)) = ((s' * s⁻¹ : Cˣ) : C) * em (v p') := by
    intro p p' h
    obtain rfl : e₂ p = p' := GlobalTheory.LabTrans.ext_unique hB σ (he₂ p) h
    have h1 := hs' p
    have h2 := hs (e₂ p)
    rw [AlgHom.comp_apply] at h1
    rw [h1, h2, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left]
  have emi : Function.Injective em := em.toRingHom.injective
  by_cases hex : ∃ p p', QkExt σ.toRingHom p p' ∧ v p' ≠ 0
  · obtain ⟨p₀, p₀', h₀, hv₀⟩ := hex
    have hσ0 : σ (v p₀) ≠ 0 := by
      intro h0
      have k0 := key p₀ p₀' h₀
      rw [h0, map_zero] at k0
      exact hv₀ ((map_eq_zero em).1 ((mul_eq_zero.1 k0.symm).resolve_left (Units.ne_zero _)))
    refine ⟨Units.mk0 (σ (v p₀) / v p₀') (div_ne_zero hσ0 hv₀), fun p p' h => emi ?_⟩
    have hne : em (v p₀') ≠ 0 := (map_ne_zero em).2 hv₀
    rw [Units.val_mk0, map_mul, map_div₀, key p p' h, key p₀ p₀' h₀]
    field_simp
  · push_neg at hex
    refine ⟨1, fun p p' h => ?_⟩
    have k := key p p' h
    rw [hex p p' h, map_zero, mul_zero] at k
    rw [hex p p' h, mul_zero]
    exact (map_eq_zero em).1 k
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  atlas_forward_decl GlobalTheory.Mum.values_galois_scalar
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → OneTrait D₁.toPre A lab → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))) (lab₂ : Labels D₂.toPre A₂), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ OneTrait D₂.toPre A₂ lab₂ ∧ GalEqN n lab₂ := by
  intro R _ _ _ hR D n hn ho hu R₁ _ _ _ ρ D₁ A lab hρ hP hS hOT
  have hU₁ : UniTrait D₁.toPre A := by
    obtain ⟨W, i1, i2, i3, φ, G', i4, i5, D', A', U', hD, a, i6, em, hW, hφ, hloc, hG, hF, -, -⟩ := hOT
    exact ⟨W, i1, i2, i3, φ, G', i4, i5, D', A', U', hD, a, hW, hφ, hloc, hG, hF⟩
  obtain ⟨R₂, _, _, _, ρ₂, D₂, A₂, hρ₂, hP₂, hS₂, hU₂, hRat⟩ := GlobalTheory.T.exists_finite_ext_rational_torsion_uniformised_trait R hR D n hn ho hu R₁ ρ D₁ A hρ hP hS hU₁
  have hB₂ : Base R₂ := by
    have := hR.2
    exact ⟨hρ₂.1, charZero_of_injective_ringHom hρ₂.2.1⟩
  have hu₂ : IsUnit (n : R₂) := by simpa using hu.map ρ₂
  obtain ⟨lab₂, hOT₂⟩ := GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait R₂ hB₂ D₂ A₂ hU₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂, D₂, A₂, lab₂, hρ₂, hP₂, hS₂, hOT₂, ?_⟩
  obtain ⟨i₀, hi₀⟩ := GlobalTheory.T.thetaLevelLabels_galoisConj_eq_serreLemma R₂ hB₂ n hn ho hu₂ D₂ A₂ lab₂ hOT₂ hRat
  refine GlobalTheory.T.torsionLabels_galois_all_levels_of_squares R₂ hB₂ n hn ho hu₂ D₂ A₂ lab₂ hOT₂ ⟨i₀, fun i hi => ?_⟩
  have hmo : Odd (n ^ i) := ho.pow
  have hmu : IsUnit ((n ^ i : ℕ) : R₂) := by rw [Nat.cast_pow]; exact hu₂.pow i
  obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R₂ hB₂ D₂ (n ^ i) hmo hmu (QkPt D₂.toPre (Kb R₂) ((n ^ i) ^ 2)) id
  have hθ := GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R₂ hB₂ D₂ A₂ lab₂ n hn ho hu₂ hOT₂ i v hv
  exact hi₀ i hi v hθ (GlobalTheory.T.thetaSeries_values_galois_scalar R₂ hB₂ D₂ A₂ lab₂ hOT₂ (n ^ i) hmo hmu v hv)

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_galois_equivariant_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → OneTrait D₁.toPre A lab → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))) (lab₂ : Labels D₂.toPre A₂), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ OneTrait D₂.toPre A₂ lab₂ ∧ GalEqN n lab₂ := by
  atlas_forward_decl GlobalTheory.Mum.exists_finExt_galEqN
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_desc_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  intro R _ _ _ hR D n hn ho hu W _ _ _ hW φ hφ hl D' G' _ _ A' hP hG hU hS
  obtain ⟨A₀, e₀, hc, hS₀, hI⟩ := GlobalTheory.T.exists_geometricFibreIso_of_traitUniformisation R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS
  obtain ⟨R₁, _, _, _, ρ, D₁, A, hF, hP₁, hS₁, hT⟩ :=
    GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS A₀ e₀ hc hS₀ hI
  have hR₁ : Base R₁ := ⟨hF.1, by haveI := hR.2; exact charZero_of_injective_ringHom hF.2.1⟩
  obtain ⟨lab, hO⟩ := GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait R₁ hR₁ D₁ A hT
  exact GlobalTheory.T.exists_finite_extension_galois_equivariant_labels R hR D n hn ho hu R₁ ρ D₁ A lab hF hP₁ hS₁ hO

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  atlas_forward_decl GlobalTheory.Mum.exists_desc_labels
end
