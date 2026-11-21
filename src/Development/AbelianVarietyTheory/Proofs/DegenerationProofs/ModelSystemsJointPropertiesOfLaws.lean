import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiserStatement

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_mem_moduli_of_meets_abelian_locus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  first | exact @GlobalTheory.LN.generic_point_of_meets_abLocus | exact GlobalTheory.LN.generic_point_of_meets_abLocus | (intros; apply GlobalTheory.LN.generic_point_of_meets_abLocus <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.fibrewise_nonvanishing_of_invertible_pushforward : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | exact GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | (intros; apply GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelTrivialisation_isUnit_on_abelianLocus : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso → IsOpen (abLocus t.G) → ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) := by
  first | exact @GlobalTheory.psiUnitOn_abLocus_pel | exact GlobalTheory.psiUnitOn_abLocus_pel | (intros; apply GlobalTheory.psiUnitOn_abLocus_pel <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory

theorem isAdmissibleCompleteLocalDomainPrime_maximalIdeal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (h₁ : IsNoetherianRing R) (h₂ : IsIntegrallyClosed R) (h₃ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) :
    admitted R (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨h₁, inferInstance, h₂, h₃⟩, h₃, inferInstance, (IsLocalRing.maximalIdeal.isMaximal R).isPrime, ?_⟩
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  infer_instance

theorem model_uniformisation_of_clauses : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  intro hL hL2 hL3 hL4 hL5 hE hU hP E _ _ _ H D l Xo c W₀ Y p hN R _ _ _ _ hR₁ hR₂ hR₃ ξ t ht hne hsp
  obtain ⟨-, hpol, hloc⟩ := T.generic_point_mem_moduli_of_meets_abelian_locus hL hL2 E H D l Xo c W₀ Y p hN R ξ t ht hne
  have hθ : ThetaNZ t.G t.PP.L := T.fibrewise_nonvanishing_of_invertible_pushforward E H Y.X Y.t hN.2.2.1 R ξ t ht
  have hadm : admitted R (IsLocalRing.maximalIdeal R) := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hR₁ hR₂ hR₃
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hpid : IsPrincipalIdealRing (R ⧸ IsLocalRing.maximalIdeal R) := inferInstance
  have hsplit : SplitOver t.G (IsLocalRing.maximalIdeal R) := hsp
  obtain ⟨P, hP'⟩ := T.exists_uniformisation_complete_local_normal_prime hL hL2 hL3 hL4 hL5 hE hU hP E H R _ hadm hpid t hpol hsplit hθ
  have hopen : IsOpen (abLocus t.G) := by
    obtain ⟨U, hU', -⟩ := hN.2.2.2.1
    rw [← hloc, ← hU']
    exact U.isOpen.preimage ξ.continuous
  refine ⟨P, ?_, hP'⟩
  rw [hloc]
  exact T.pelTrivialisation_isUnit_on_abelianLocus hL hL2 hL3 hL4 hL5 E H R _ hadm t P hP' hopen

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_uniformisation_of_abelianLocus_directImage : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  first | exact @GlobalTheory.model_uniformisation_of_clauses | exact GlobalTheory.model_uniformisation_of_clauses | (intros; apply GlobalTheory.model_uniformisation_of_clauses <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcGenericPoint_descends_to_powerSeries : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → TraitData Y a g y₁ → ∃ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ ∧ TraitData Y a (RingHom.id _) y := by
  first | exact @GlobalTheory.ArcPointDescent.point_descends | exact GlobalTheory.ArcPointDescent.point_descends | (intros; apply GlobalTheory.ArcPointDescent.point_descends <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S Z : Scheme.{0}) (t₀ : SAB H S) (t : SAB H Z) (π : Z ⟶ S) (_ : SABMap t t₀ π) (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [CommRing R] [IsDomain R] [CharZero R] (g : R₁ →+* R) (gam : FractionRing R₁ →+* FractionRing R), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R _ (g r)) → ∀ (x₁ : Sp (FractionRing R₁) ⟶ S) (x : Sp (FractionRing R) ⟶ Z), x ≫ π = spMap gam ≫ x₁ → PolAt t₀ x₁ → ∀ (N n : ℕ) (f₁ : Fin n → LB.Sec (LPow t₀.G t₀.PP.L (N : ℤ) (Over.mk x₁))), IsFrame t₀.G t₀.PP.L N x₁ f₁ → ∃ f : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk x)), IsFrame t.G t.PP.L N x f ∧ BasisAlong t.G t.PP.L N (𝟙 _) f := by
  first | exact @GlobalTheory.FramePull.frame_pull | exact GlobalTheory.FramePull.frame_pull | (intros; apply GlobalTheory.FramePull.frame_pull <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcExtends

theorem exists_lift_finite {K : Type} [Field K] {Z X : Scheme.{0}} (π : Z ⟶ X) [IsFinite π] [Surjective π]
    (x : Sp K ⟶ X) : ∃ (L : Type) (_ : Field L) (σ : K →+* L) (z : Sp L ⟶ Z), σ.Finite ∧ z ≫ π = spMap σ ≫ x := by
  have : CompactSpace ↥(pullback π x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (default : PrimeSpectrum K)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π x)) ⟨p, trivial⟩
  have := isClosed_singleton_iff_isClosedImmersion.mp hq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback π x).fromSpecResidueField q ≫ pullback.snd π x)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  refine ⟨(pullback π x).residueField q, inferInstance, φ.hom,
    (pullback π x).fromSpecResidueField q ≫ pullback.fst π x, (IsFinite.SpecMap_iff φ).1 hf, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hφ]
  rfl

theorem spMap_jK {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ jK R = jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem finite_fractionRing {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) : gam.Finite := by
  letI := g.toAlgebra
  letI := gam.toAlgebra
  have : Module.Finite R R₁ := hg
  have : IsScalarTower R (FractionRing R) (FractionRing R₁) := IsScalarTower.of_algebraMap_eq fun r => (h r).symm
  have : FaithfulSMul R R₁ := (faithfulSMul_iff_algebraMap_injective R R₁).2 fun a b e =>
    IsFractionRing.injective R (FractionRing R) (gam.injective (by
      rw [h, h]; exact congrArg _ e))
  show Module.Finite (FractionRing R) (FractionRing R₁)
  exact Module.Finite.of_isLocalization R R₁ (nonZeroDivisors R)

theorem exists_normalisation (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (hc : IsAdicComplete (IsLocalRing.maximalIdeal R) R) {R₁ : Type} [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) {L : Type} [Field L] {σ : FractionRing R₁ →+* L} (hσ : σ.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (_ : IsNoetherianRing R₂)
      (_ : IsIntegrallyClosed R₂) (_ : CharZero R₂) (g₂ : R₁ →+* R₂) (f : L →+* FractionRing R₂),
      (∀ r, (f.comp σ) (algebraMap R₁ _ r) = algebraMap R₂ _ (g₂ r)) ∧ (g₂.comp g).IsIntegral := by
  letI := (σ.comp gam).toAlgebra
  letI := ((σ.comp gam).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (FractionRing R) L := hσ.comp (finite_fractionRing h hg)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hc L
  have hR : ∀ r, algebraMap R L r = σ (algebraMap R₁ _ (g r)) := fun r => congrArg σ (h r)
  have hi : ∀ r : R₁, (σ.comp (algebraMap R₁ (FractionRing R₁))) r ∈ integralClosure R L := fun r => by
    obtain ⟨p, hp, e⟩ := hg.to_isIntegral r
    refine ⟨p, hp, ?_⟩
    have e' := congrArg (σ.comp (algebraMap R₁ (FractionRing R₁))) e
    rw [Polynomial.hom_eval₂, map_zero] at e'
    rw [← e']
    congr 1
    exact RingHom.ext hR
  have hinj : Function.Injective (algebraMap R L) :=
    (σ.comp gam).injective.comp (IsFractionRing.injective R (FractionRing R))
  have : CharZero L := charZero_of_injective_algebraMap hinj
  let g₂ : R₁ →+* integralClosure R L := (σ.comp (algebraMap R₁ (FractionRing R₁))).codRestrict _ hi
  refine ⟨integralClosure R L, inferInstance, inferInstance, h₂, h₃, h₄, inferInstance, g₂,
    (FractionRing.algEquiv (integralClosure R L) L).symm.toRingHom, fun r => ?_, ?_⟩
  · exact (FractionRing.algEquiv (integralClosure R L) L).symm.commutes (g₂ r)
  · have e : g₂.comp g = algebraMap R (integralClosure R L) := RingHom.ext fun r => Subtype.ext (hR r).symm
    rw [e]
    exact (RingHom.finite_algebraMap.2 h₁).to_isIntegral

theorem arcBase_complete {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : ArcBase O' ϖ) :
    ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
  rcases h with ⟨hF, -⟩ | ⟨hD, hi, hc⟩
  · letI := hF.toField
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · refine ⟨inferInstance, inferInstance, ?_⟩
    rwa [hi.maximalIdeal_eq]

theorem polAt_moduli {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K]
    (y : Sp K ⟶ Xo.XF c) : PolAt Y.t (y ≫ Y.j) := by
  have hm : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp := isGrpPullback_pullback Y.t.G (y ≫ Y.j)
  let ψ : ((Over.pullback (y ≫ Y.j)).obj Y.t.G).left ⟶ Y.oF.t.G.left :=
    hm.1.lift (pullback.fst Y.t.G.hom (y ≫ Y.j)) (pullback.snd Y.t.G.hom (y ≫ Y.j) ≫ y)
      (by rw [Category.assoc]; exact pullback.condition)
  have e₁ : ψ ≫ Y.m.φ = pullback.fst Y.t.G.hom (y ≫ Y.j) := hm.1.lift_fst _ _ _
  have hq : IsGrpPullback ((Over.pullback (y ≫ Y.j)).obj Y.t.G) Y.oF.t.G y ψ :=
    IsGrpPullback.cancel hm (hp.congr rfl e₁.symm) (hm.1.lift_snd _ _ _)
  obtain ⟨w, hw, -⟩ := Y.m.lin
  have hI : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (pullback.fst Y.t.G.hom (y ≫ Y.j))) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L _ _ _ ψ fun _ => e₁.symm) ⟨w, hw⟩
  have := Y.oF.proper
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hq.1 Y.oF.proper,
    amplePt _ K y _ _ ψ hq _ _ Y.oF.t.PP.isLB (pull_isLB Y.t.PP.isLB _) hI.symm Y.oF.ample Y.oF.ktriv⟩

theorem exists_extension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  intro hL hL₂ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hO m Z π t mt hfin hsurj ⟨Am⟩ R₁ _ _ g y₁ gam hgam hg _ y hy hs
    ⟨θ₁, hθ₁⟩ ⟨n, f₁, hf₁⟩
  obtain ⟨_, _, hc⟩ := arcBase_complete hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨L, _, σ, z, hσ, hz⟩ := exists_lift_finite π (y₁ ≫ Y.j)
  obtain ⟨R₂, _, _, _, _, _, hch, g₂, f, hf, hint⟩ :=
    exists_normalisation (PowerSeries O') ReciprocityTheory.P1.isAdicComplete_ps hgam hg hσ
  have hx : (spMap f ≫ z) ≫ π = spMap (f.comp σ) ≫ y₁ ≫ Y.j := by
    rw [Category.assoc, hz, spMap_comp, Category.assoc]
  have hP := polAt_moduli Y y₁
  obtain ⟨θ, hθ, bθ⟩ := GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP 1 1 _ hθ₁
  obtain ⟨ff, hff, bff⟩ := GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP (m ^ 2) n _ hf₁
  obtain ⟨θ', rfl⟩ : ∃ θ', θ = fun _ : Fin 1 => θ' := ⟨θ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hab : Set.range (spMap f ≫ z) ⊆ abLocus t.G := by
    rintro _ ⟨p, rfl⟩
    refine (abLocus_pullback abLocusOne Y.t.semi mt.cart.1 _).1 (abLocusOne _ Y.t.G Y.t.semi _ _ hP.1 ?_)
    exact ⟨spMap (f.comp σ) p, (congrArg (fun q => q p) hx).symm⟩
  obtain ⟨e, he, hE⟩ := GlobalTheory.FrameGen.exists_gen_of_frames Z t.G t.PP.L t.PP.isLB (m ^ 2) Am Am.A rfl R₂ _ hab θ' n ff hθ hff bθ bff hch
  have := projProper _ _ _ Y.proj
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (π ≫ Y.s)
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (π ≫ Y.s)
  have hG : ∀ r, ((f.comp σ).comp gam) (algebraMap (PowerSeries O') _ r) = algebraMap R₂ _ ((g₂.comp g) r) := fun r =>
    (congrArg (f.comp σ) (hgam r)).trans (hf _)
  have hx' : (spMap f ≫ z) ≫ π = spMap ((f.comp σ).comp gam) ≫ y ≫ Y.j := by
    rw [hx, ← hy, spMap_comp gam]
    simp only [Category.assoc]
  obtain ⟨χ₂, hχ₂⟩ := GlobalTheory.ExtLB.exists_extension Z Am.A Am.isLB Am.ample R₂ _ e he fun V _ _ _ hV φ gV hgV => by
    have := hV.1
    obtain ⟨χ, hχ, -⟩ := val_exists (π ≫ Y.s) (spMap gV ≫ spMap f ≫ z)
      (spMap φ ≫ spMap (g₂.comp g) ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b) (by
        rw [Category.assoc, ← Category.assoc (spMap f ≫ z), hx', Category.assoc, Category.assoc, hs,
          ← Category.assoc (spMap _) (jK _), spMap_jK hG, Category.assoc, ← Category.assoc (spMap gV), spMap_jK hgV,
          Category.assoc])
    exact ⟨χ, hχ.symm, hE V hV φ gV hgV χ hχ.symm⟩
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.extension_descends_of_isIntegral _ R₂ _ _ hG hint Y.X (y ≫ Y.j) (χ₂ ≫ π)
    (by rw [← Category.assoc, hχ₂, hx'])
  exact ⟨χ, hχ⟩

end GlobalTheory.LN.ArcExtends
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_generic_point_extends_powerSeries : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  first | exact @GlobalTheory.LN.ArcExtends.exists_extension | exact GlobalTheory.LN.ArcExtends.exists_extension | (intros; apply GlobalTheory.LN.ArcExtends.exists_extension <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory
namespace ArcLocus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem closedPoint_notMem (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (f : O' →+* R) (u : R)
    (χ : Sp R ⟶ Y.X) (h : Y.HasArcData a (IsLocalRing.maximalIdeal R) f u χ) :
    χ (IsLocalRing.closedPoint R) ∉ abLocus Y.t.G := by
  intro h₁
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ f u χ).1 h
  have h₂ := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 _).1 h₁
  have hmax : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  obtain ⟨p, hp⟩ : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zero_add, pow_one]
    exact le_refl (IsLocalRing.maximalIdeal R)
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick R (IsLocalRing.maximalIdeal R) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial a.D₀.X := a.nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (x : PrimeSpectrum R)
    (hx : x.asIdeal ≠ ⊥) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), CDvr W ∧ (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      (IsLocalRing.maximalIdeal W).comap φ = x.asIdeal := by
  obtain ⟨W, _, _, _, _, φ, h1, h2⟩ :=
    exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) x.asIdeal (bot_lt_iff_ne_bot.2 hx)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
  have hφ' : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  exact ⟨W, inferInstance, inferInstance, inferInstance, φ, IsFractionRing.lift hφ',
    ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩,
    fun r => IsFractionRing.lift_algebraMap hφ' r, h2⟩

theorem j_mem (Y : Model Xo c β) (p : Xo.XF c) : Y.j p ∈ abLocus Y.t.G := by
  have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  exact hz

theorem mem_range_j (Y : Model Xo c β) (z : Y.X) (hz : z ∈ abLocus Y.t.G) (p : Xo.XF c)
    (hp : Y.s z = Y.s (Y.j p)) : z ∈ Set.range Y.j := by
  have h₁ : z ∈ Set.range (pullback.fst Y.s (spMap β)) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hp]
    have : Y.j p ∈ Set.range (pullback.fst Y.s (spMap β)) := ⟨Y.jQ p, rfl⟩
    rwa [Scheme.Pullback.range_fst] at this
  obtain ⟨w, rfl⟩ := h₁
  have h₂ : w ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hz
  obtain ⟨q, rfl⟩ := h₂
  exact ⟨q, rfl⟩

theorem exists_jK_eq_bot (R : Type) [CommRing R] [IsDomain R] :
    ∃ pt : Sp (FractionRing R), jK R pt = (⊥ : PrimeSpectrum R) := by
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

end ArcLocus

open ArcLocus in

theorem arc_abLocus_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb y χ hχ hT
  have hN : IsNoetherianRing O' := by
    rcases hb with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have hc : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨pt, hpt⟩ := exists_jK_eq_bot (PowerSeries O')
  have h0 : χ (⊥ : PrimeSpectrum (PowerSeries O')) = Y.j (y pt) := by
    rw [← hpt, ← Scheme.Hom.comp_apply, hχ, Scheme.Hom.comp_apply]
  have h1 : χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have hd : IsDominant (jK (PowerSeries O')) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap (PowerSeries O') (FractionRing (PowerSeries O')))).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (PowerSeries O') _)]; exact bot_le)
    refine ext_of_isDominant (jK (PowerSeries O')) ?_
    rw [← Category.assoc, hχ, Category.assoc, hT.1]
    have : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal := by
    intro x
    by_cases hx : x.asIdeal = ⊥
    · have e : x = (⊥ : PrimeSpectrum (PowerSeries O')) := PrimeSpectrum.ext hx
      refine iff_of_true ?_ ?_
      · rw [e, h0]; exact j_mem Y _
      · rw [hx]; exact PowerSeries.X_ne_zero
    obtain ⟨W, _, _, _, φ, gam, hW, hg, hφ⟩ := exists_trait (PowerSeries O') x hx
    have key : spMap gam ≫ jK (PowerSeries O') = jK W ≫ spMap φ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext hg
    have ht := hT.2 W hW φ gam hg (spMap φ ≫ χ) (by rw [← hχ, ← Category.assoc, key, Category.assoc])
    have hu : PowerSeries.X ∉ x.asIdeal ↔ IsUnit (φ PowerSeries.X) := by
      rw [← hφ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have hcl : spMap φ (IsLocalRing.closedPoint W) = x := PrimeSpectrum.ext hφ
    rw [hu]
    refine ⟨fun hab => ?_, fun h => ht.1 h ⟨IsLocalRing.closedPoint W, (Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)⟩⟩
    by_contra h
    obtain ⟨W', _, _, _, io, -, -, hfin, hA⟩ := ht.2 h
    refine closedPoint_notMem Y a _ _ _ hA ?_
    have hcl' : spMap io (IsLocalRing.closedPoint W') = IsLocalRing.closedPoint W := by
      refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' io hfin.to_isIntegral (IsLocalRing.maximalIdeal W')
    have e : (spMap io ≫ spMap φ ≫ χ) (IsLocalRing.closedPoint W') = χ x :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (spMap φ ≫ χ) hcl').trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)))
    rw [e]
    exact hab
  refine ⟨h1, h2, fun x hx => mem_range_j Y _ ((h2 x).2 fun h => hx (Ideal.mul_mem_left _ _ h)) (y pt) ?_⟩
  have hC : ∀ z : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ z.asIdeal →
      spMap (PowerSeries.C (R := O')) z = (⊥ : PrimeSpectrum O') := by
    intro z hz
    refine PrimeSpectrum.ext ?_
    change z.asIdeal.comap (PowerSeries.C (R := O')) = ⊥
    have hzp := z.isPrime
    rcases hb with h | h
    · letI := h.1.toField
      exact Ideal.eq_bot_of_prime _
    · have := h.1
      by_contra hne
      have hm := IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
      have : ϖ ∈ z.asIdeal.comap (PowerSeries.C (R := O')) := by
        rw [hm]; exact h.2.1.not_isUnit
      exact hz (Ideal.mul_mem_right _ _ this)
  have hb0 : spMap (PowerSeries.C (R := O')) (⊥ : PrimeSpectrum (PowerSeries O')) = (⊥ : PrimeSpectrum O') :=
    PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (PowerSeries.C_injective (R := O')))
  have h3 : ∀ z : Sp (PowerSeries O'), Y.s (χ z) = spMap b (spMap (PowerSeries.C (R := O')) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
  rw [← h0, h3, hC x hx]
  exact ((h3 _).trans (congrArg (spMap b) hb0)).symm

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  atlas_forward_decl GlobalTheory.arc_abLocus_of_traitData
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  first | exact @GlobalTheory.ArcData.hasArcData_of_traitData | exact GlobalTheory.ArcData.hasArcData_of_traitData | (intros; apply GlobalTheory.ArcData.hasArcData_of_traitData <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcClause

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_lift (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : V →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap V.subtype := by
    rw [Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F, PrimeSpectrum.comap g default = PrimeSpectrum.comap V.subtype q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact Subtype.ext h1
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap V.subtype = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap V.subtype) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (nonZeroDivisors V) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap V.subtype)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap V.subtype)).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap V.subtype)) (default : PrimeSpectrum K) = z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

theorem not_mem_generic {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (f : R →+* R') {r : R} (hr : f r ≠ 0)
    (p : PrimeSpectrum (FractionRing R')) : r ∉ ((jK R' ≫ spMap f) p).asIdeal := by
  intro h
  have h1 : algebraMap R' (FractionRing R') (f r) ∈ PrimeSpectrum.asIdeal p := h
  rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal p)] at h1
  exact hr (IsFractionRing.injective R' (FractionRing R') (h1.trans (map_zero _).symm))

theorem arc_clause : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hX hF E _ _ _ H D l Xo c W₀ Y p hN hA O' _ _ _ b ϖ a hB
  obtain ⟨m, Z, π, t, mt, hodd, hunit, hfin, hsurj, hAF⟩ := hA
  have hm : IsUnit (m : O') := by simpa using hunit.map b
  obtain ⟨R₁, _, _, g, y₁, hg, hgf, hR, hTD, hθ, hf⟩ := hF E H D l Xo c W₀ Y O' b ϖ a hB m hodd hm
  let gam : FractionRing (PowerSeries O') →+* FractionRing R₁ :=
    IsFractionRing.lift (g := (algebraMap R₁ (FractionRing R₁)).comp g) ((IsFractionRing.injective R₁ _).comp hg)
  have hgam : ∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r) := fun r =>
    IsFractionRing.lift_algebraMap _ r
  obtain ⟨y, hy, hTy⟩ := GlobalTheory.T.arcGenericPoint_descends_to_powerSeries h1 h2 h3 h4 h5 h6 E H D l Xo c W₀ Y O' b a ϖ hB R₁ g y₁ gam hgam hgf hR hTD
  have hys : y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have := hTy.1
    rwa [show spMap (RingHom.id (PowerSeries O')) = 𝟙 _ from Spec.map_id _, Category.id_comp] at this
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.arc_generic_point_extends_powerSeries h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB m Z π t mt hfin hsurj hAF R₁ g y₁ gam hgam hgf hR
    y hy hys hθ hf
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB y χ hχ hTy
  have c4 := GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData h1 h2 h3 h4 h5 h6 hE hU hP hX E H D l Xo c W₀ Y O' b a ϖ hB hN.2.2.1 y χ hχ hTy
  have hϖ : ϖ ≠ 0 := by
    rcases hB with ⟨-, rfl⟩ | ⟨-, h, -⟩
    exacts [one_ne_zero, h.ne_zero]
  refine ⟨χ, fun χ' => ⟨fun h => h ▸ ⟨c1, c2, c3, c4⟩, fun ⟨d1, _, d3, d4⟩ => ?_⟩, fun hirr y' ev hs hr hd hC hXv => ?_⟩
  · have hpid : IsPrincipalIdealRing O' ∧ IsLocalRing O' := by
      rcases hB with ⟨h, -⟩ | ⟨h, -⟩
      · letI := h.toField
        exact ⟨inferInstance, inferInstance⟩
      · exact ⟨inferInstance, inferInstance⟩
    obtain ⟨_, _⟩ := hpid
    have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (f := PowerSeries.C (R := O')) PowerSeries.C_injective
    obtain ⟨y', hy'⟩ := exists_lift (c.V W₀) Y (jK (PowerSeries O') ≫ χ') (by
      rintro _ ⟨q, rfl⟩
      refine d3 _ ?_
      have := not_mem_generic (RingHom.id (PowerSeries O')) (r := PowerSeries.C ϖ * PowerSeries.X)
        (mul_ne_zero (fun h => hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero) q
      exact this)
    exact GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a (PowerSeries O') (Ideal.span {PowerSeries.X})
      (PowerSeries.C (R := O')) PowerSeries.X ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
      (fun h => PowerSeries.X_prime.not_unit (Ideal.span_singleton_eq_top.1 h)) PowerSeries.C_injective
      χ' χ y' y hy' hχ.symm d1 c1 d4 c4
  · rcases hB with ⟨-, rfl⟩ | ⟨hdvr, -, hc⟩
    · exact absurd isUnit_one hirr.not_isUnit
    have hc' : IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
      rwa [hirr.maximalIdeal_eq]
    have hrg : Set.range (jK O' ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
      rintro _ ⟨q, rfl⟩
      refine c3 _ ?_
      have := not_mem_generic ev (r := PowerSeries.C ϖ * PowerSeries.X)
        (by rw [map_mul, hC, hXv]; exact mul_ne_zero hϖ hϖ) q
      exact this
    have c5 := GlobalTheory.T.arcData_specialise_at_uniformiser h1 h2 hT h4.unifBaseChange h5 E H D l Xo c _ _ Y O' b ϖ a hirr hc' ev hC hXv χ c1 hrg c4
    obtain ⟨z, hz⟩ := exists_lift (c.V W₀) Y _ hrg
    obtain ⟨z', hz'⟩ := exists_lift (c.V W₀) Y _ hr
    have hid : spMap (RingHom.id O') = 𝟙 _ := Spec.map_id _
    have hev : spMap ev ≫ spMap (PowerSeries.C (R := O')) = spMap (RingHom.id O') := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact hC x
    refine GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a O' (Ideal.span {ϖ}) (RingHom.id O') ϖ
      ⟨inferInstance, inferInstance, inferInstance, hc⟩
      (fun h => hirr.not_isUnit (Ideal.span_singleton_eq_top.1 h)) Function.injective_id
      _ y' z z' hz hz' ?_ ?_ c5 hd
    · rw [Category.assoc, c1, ← Category.assoc, hev]
    · rw [hid, Category.id_comp, hs]

end GlobalTheory.LN.ArcClause
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFamily_fourthCondition_invertible_pushforward : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  first | exact @GlobalTheory.LN.ArcClause.arc_clause | exact GlobalTheory.LN.ArcClause.arc_clause | (intros; apply GlobalTheory.LN.ArcClause.arc_clause <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN

theorem partI_of_inputs : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA hM h0
  refine ⟨h0, fun E _ _ _ H D hD Xo => ?_⟩
  obtain ⟨Y, hY, hgl⟩ := hM E H D hD Xo
  refine ⟨Y, fun p W hp hW => ⟨(hY p W hp hW).1, fun i => ⟨((hY p W hp hW).2 i).1, ?_, ?_⟩⟩, hgl⟩
  · exact GlobalTheory.T.model_uniformisation_of_abelianLocus_directImage h1 h2 h3 h4 h5 hE hU hP E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
  · exact GlobalTheory.T.arcFamily_fourthCondition_invertible_pushforward hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
      ((hY p W hp hW).2 i).2

end GlobalTheory.LN
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelSystems_jointProperties_of_laws : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  atlas_forward_decl GlobalTheory.LN.partI_of_inputs
end
