import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfCompatibleThickenings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_genericFibreIso_of_compatible_thickenings : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∃ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) := by
  first | exact @GlobalTheory.exists_genericFibre_iso_of_thickenings | exact GlobalTheory.exists_genericFibre_iso_of_thickenings | (intros; apply GlobalTheory.exists_genericFibre_iso_of_thickenings <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalExt

theorem hom_ext_of_flat_family {Y X : Scheme.{0}} (f g : Y ⟶ X)
    (h : ∀ y : Y, ∃ (Z : Scheme.{0}) (p : Z ⟶ Y), Flat p ∧ y ∈ Set.range p ∧ p ≫ f = p ≫ g) : f = g := by
  choose Z p hp hy he using h
  have : Surjective (Limits.Sigma.desc p) :=
    Surjective.sigmaDesc_of_union_range_eq_univ
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨y, hy y⟩)
  have : Epi (Limits.Sigma.desc p) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (Limits.Sigma.desc p)]
  refine Limits.Sigma.hom_ext _ _ fun y => ?_
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc_assoc, he]

theorem eq_of_isIso_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) [IsPreimmersion f] {Y X : Over S} (ψ : Y ⟶ X)
    [IsIso ((Over.pullback f).map ψ)] {x y : Y.left} (hx : Y.hom x ∈ Set.range f) (h : ψ.left x = ψ.left y) :
    x = y := by
  have w : ∀ z, X.hom (ψ.left z) = Y.hom z := fun z => by rw [← Scheme.Hom.comp_apply, Over.w]
  have hy : Y.hom y ∈ Set.range f := by rw [← w, ← h, w]; exact hx
  obtain ⟨x', rfl⟩ : x ∈ Set.range (pullback.fst Y.hom f) := by rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y', rfl⟩ : y ∈ Set.range (pullback.fst Y.hom f) := by rw [Scheme.Pullback.range_fst]; exact hy
  have e : ((Over.pullback f).map ψ).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have e' : ∀ z, pullback.fst X.hom f (((Over.pullback f).map ψ).left z) = ψ.left (pullback.fst Y.hom f z) :=
    fun z => congr($e z)
  rw [← e', ← e'] at h
  have h₁ := (pullback.fst X.hom f).isEmbedding.injective h
  have : IsIso ((Over.pullback f).map ψ).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback f).map ψ)))
  rw [((Over.pullback f).map ψ).left.isEmbedding.injective h₁]

variable {R : Type} [CommRing R] (I : Ideal R)

instance isClosedImmersion_thick (e : ℕ) : IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem range_thick (e : ℕ) (s : Spec (CommRingCat.of R)) : s ∈ Set.range (thick R I e) ↔ I ≤ s.asIdeal := by
  have h := _root_.range_comap_of_surjective _ (Ideal.Quotient.mk (I ^ (e + 1))) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at h
  refine (h.ge.antisymm h.le ▸ Iff.rfl : s ∈ Set.range (thick R I e) ↔ s ∈ PrimeSpectrum.zeroLocus (I ^ (e + 1) : Ideal R)).trans ?_
  have := s.isPrime
  exact Ideal.IsPrime.pow_le_iff (I := I) (P := s.asIdeal) (Nat.succ_ne_zero e)

theorem map_eq_iff (e : ℕ) {Y X : Over (Spec (CommRingCat.of R))} (ψ : Y ⟶ X)
    (j : thickObj R I e Y ⟶ thickObj R I e X) :
    (Over.pullback (thick R I e)).map ψ = j ↔ (fstG I e Y).left ≫ ψ.left = j.left ≫ (fstG I e X).left := by
  have e₁ : ((Over.pullback (thick R I e)).map ψ).left ≫ pullback.fst X.hom (thick R I e) =
      pullback.fst Y.hom (thick R I e) ≫ ψ.left := pullback.lift_fst _ _ _
  refine ⟨fun h => h ▸ e₁.symm, fun h => Over.OverMorphism.ext (pullback.hom_ext (e₁.trans h) ?_)⟩
  exact (Over.w _).trans (Over.w j).symm

theorem hom_ext_thick [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] {X : Over (Spec (CommRingCat.of R))}
    [IsSeparated X.hom] {a b : H ⟶ X}
    (h : ∀ e, (Over.pullback (thick R I e)).map a = (Over.pullback (thick R I e)).map b) : a = b :=
  (GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 X a b fun e =>
    ((map_eq_iff I e a _).1 (h e)).trans ((map_eq_iff I e b _).1 rfl).symm

theorem isMonHom_of_thick [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) {G' G : Over (Spec (CommRingCat.of R))}
    [GrpObj G'] [GrpObj G] [Smooth G'.hom] [GeometricallyConnected G'.hom] [IsSeparated G.hom] (ψ : G' ⟶ G)
    (h : ∀ e, IsMonHom ((Over.pullback (thick R I e)).map ψ)) : IsMonHom ψ := by
  have h1 : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (Smooth (𝟙 _))
  have h1' : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
    inferInstanceAs (GeometricallyConnected (𝟙 _))
  have h2 : Smooth (G' ⊗ G').hom := inferInstanceAs (Smooth (pullback.fst G'.hom G'.hom ≫ G'.hom))
  have h2' : GeometricallyConnected (G' ⊗ G').hom :=
    GeometricallyConnected.comp (pullback.fst G'.hom G'.hom) G'.hom
  constructor
  · refine hom_ext_thick I hI _ fun e => ?_
    have := (h e).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at this
    rw [Functor.map_comp, this]
  · refine hom_ext_thick I hI _ fun e => ?_
    have := (h e).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi] at this
    rw [Functor.map_comp, this, Functor.map_comp]

theorem exists_iso [IsDomain R] [IsDiscreteValuationRing R] (hI : I = IsLocalRing.maximalIdeal R)
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G) (hj : ∀ e, IsMonHom (j e).hom)
    (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (H : ∀ x : (thickObj R I 0 G').left, ∃ (T : Scheme.{0}) (g' : T ⟶ G'.left) (g : T ⟶ G.left), Flat g' ∧
      (fstG I 0 G').left x ∈ Set.range g' ∧ g ≫ G.hom = g' ≫ G'.hom ∧
      (∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left),
        r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g) :
    ∃ ψ : G' ≅ G, IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧
      ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := hG'.smooth
  have := hG'.separated
  have := hG'.quasiCompact
  have := hG'.geomConnected
  have := GlobalTheory.GenericExt.isOpenImmersion_jK R
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R (FractionRing R)
  have hint : IsIntegral G'.left :=
    (GlobalTheory.isIntegral_and_isNormalScheme_of_smooth_dvr R (FractionRing R) G' inferInstance
      (inferInstanceAs (ConnectedSpace ↥(pullback G'.hom (jK R))))).1
  have hx0 : ∀ x : G'.left, I ≤ (G'.hom x).asIdeal → x ∈ Set.range (fstG I 0 G').left := fun x hx => by
    show x ∈ Set.range (pullback.fst G'.hom (thick R I 0))
    rw [Scheme.Pullback.range_fst]
    exact (range_thick I 0 _).2 hx
  obtain ⟨ψ, hψ⟩ := GlobalTheory.GenericExt.main R G' G ΦK.hom fun x hx => by
    obtain ⟨x, rfl⟩ := hx0 x (by rw [hx, hI]; exact le_rfl)
    obtain ⟨T, g', g, h₁, h₂, -, h₄, -⟩ := H x
    exact ⟨T, g', g, h₁, h₂, h₄⟩
  have eψ : ΦK.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.left := by
    rw [← hψ]; exact pullback.lift_fst _ _ _
  have hth : ∀ e : ℕ, (fstG I e G').left ≫ ψ.left = (j e).hom.left ≫ (fstG I e G).left := fun e => by
    refine hom_ext_of_flat_family _ _ fun y => ?_
    obtain ⟨x, hx⟩ := hx0 ((fstG I e G').left y) ((range_thick I e _).1 (by
      have : (fstG I e G').left y ∈ Set.range (pullback.fst G'.hom (thick R I e)) := ⟨y, rfl⟩
      rw [Scheme.Pullback.range_fst] at this
      exact this))
    obtain ⟨T, g', g, h₁, h₂, h₃, h₄, h₅⟩ := H x
    have hg : g' ≫ ψ.left = g := by
      let a : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk (g' ≫ ψ.left) (by simp)
      let b : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk g h₃
      have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R)) := inferInstance
      have : IsSchemeTheoreticallyDominant (pullback.fst g' (pullback.fst G'.hom (jK R))) := inferInstance
      have := GlobalTheory.over_ext_of_schemeTheoreticallyDominant (a := a) (b := b)
        (pullback.fst g' (pullback.fst G'.hom (jK R))) (by
          have := h₄ _ _ (pullback.snd g' (pullback.fst G'.hom (jK R))) pullback.condition.symm
          rw [eψ] at this
          exact (pullback.condition_assoc _).trans this)
      exact congr(($this).left)
    refine ⟨_, pullback.snd g' (fstG I e G').left, inferInstance, ?_, ?_⟩
    · rw [Scheme.Pullback.range_snd]
      show (fstG I e G').left y ∈ Set.range g'
      rw [← hx]; exact h₂
    · rw [h₅ e _ _ _ pullback.condition.symm, ← pullback.condition_assoc, hg]
  have hth' : ∀ e, (Over.pullback (thick R I e)).map ψ = (j e).hom := fun e => (map_eq_iff I e ψ _).2 (hth e)
  have hmon : IsMonHom ψ := isMonHom_of_thick I (by rw [hI, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ψ
    fun e => hth' e ▸ hj e
  have hK : IsIso ((Over.pullback (jK R)).map ψ) := hψ ▸ inferInstance
  have h0 : IsIso ((Over.pullback (thick R I 0)).map ψ) := hth' 0 ▸ inferInstance
  have w : ψ.left ≫ G.hom = G'.hom := Over.w ψ
  have : IsSeparated (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : LocallyOfFiniteType (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : QuasiCompact (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : IsSeparated ψ.left := .of_comp _ G.hom
  have : LocallyOfFiniteType ψ.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ψ.left := .of_comp _ G.hom
  have : LocallyQuasiFinite ψ.left := LocallyQuasiFinite.of_injective fun x y h => by
    by_cases hx : G'.hom x ∈ Set.range (jK R)
    · exact eq_of_isIso_pullback (jK R) ψ hx h
    · refine eq_of_isIso_pullback (thick R I 0) ψ ((range_thick I 0 _).2 ?_) h
      rw [GlobalTheory.GenericExt.eq_closedPoint_of_not_mem_range R _ hx, hI]; exact le_rfl
  have : IsIso ψ := GlobalTheory.isIso_of_quasiFinite_of_isIso_genericFibre_dvr R (FractionRing R) G' G ψ hmon
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance hK
  exact ⟨asIso ψ, hmon, hψ, hth⟩

theorem main : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∃ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) := by
  intro l₁ l₂ R _ _ _ I hA hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj ΦK wK hw
  refine exists_iso I hI hG hG' j (fun e => (hj e).1) ΦK fun x => ?_
  obtain ⟨B, _, _, g', g, jL, jL', h₁, -, h₃, h₄, h₅, h₆, h₇⟩ :=
    GlobalTheory.exists_completed_point_of_thickenings R I hA hI D D' A A' G G' hG hG' U U' hD j hj x
  obtain ⟨v, hv, -⟩ := GlobalTheory.T.generic_iso_agrees_on_complete_points_alt l₁ l₂ R I hA hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hw B g' g jL jL' h₁
    ⟨h₅, h₆, h₇⟩
  exact ⟨_, g', g, h₃, h₄, h₆.trans h₅.symm, fun Z ρ r h => (hv Z ρ r h).1, h₇.2.2⟩

end GlobalTheory.FormalExt
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_extends_semiAbelian_dvr_inducing_formal : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∃ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) := by
  first | exact @GlobalTheory.FormalExt.main | exact GlobalTheory.FormalExt.main | (intros; apply GlobalTheory.FormalExt.main <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleIso_extending_generic_alt : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) → ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull ψ.hom.left), wL.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G').left) z jL jL' := by
  first | exact @GlobalTheory.exists_bundleIso_extending_generic | exact GlobalTheory.exists_bundleIso_extending_generic | (intros; apply GlobalTheory.exists_bundleIso_extending_generic <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pmaps_rig_of_thick_compat {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G) (hj : ∀ e, IsMonHom (j e))
    {F : G'.left ⟶ G.left} (he : eSec G' ≫ F = eSec G)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull F)) (hw : wL.IsGen)
    (H : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈
        D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left ((j e).left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
      Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') =
        Geo.Tor.gw (U.w e) (r ≫ (j e).left) z jM (fun _ => jL) *
          Geo.Tor.gw wL (r ≫ (fstG I e G').left) z jL jL') :
    PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig (𝟙 _) := by
  refine AbelianPartIso.pmaps_of_thickenings hI U.LG.isLB U'.LG.isLB wL hw _ _ he _ U'.LG.rigGen _ U.LG.rigGen
    fun e z p q hp hq => ?_
  have hs := Geo.Tor.specOf_id R
  have hB : eSec D'.toPre.P.A ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D.toPre.P.A := hD.he.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _))
  have hje : eSec (thickObj R I e G') ≫ (j e).left = eSec (thickObj R I e G) :=
    congrArg Over.Hom.left (hj e).one_hom
  obtain ⟨m, hm⟩ := Geo.Tor.exists_chart D.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D.toPre.P.A) z)
  obtain ⟨m', hm'⟩ := Geo.Tor.exists_chart D'.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z)
  have hm₂ : (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))
      ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z) ∈ D.toPre.P.L.U m :=
    (congrArg (fun g => (UnitValue.thU R I e ≫ g) z ∈ D.toPre.P.L.U m) hB).mpr hm
  have e₁ := UnitValue.wv_rig U e z m p hm hp
  have e₂ := UnitValue.wv_rig U' e z m' q hm' hq
  have e₃ := (Geo.Tor.maps_iff hD.w _ (fun _ => eSec D.toPre.P.A) _ D'.toPre.rig D.toPre.rig
    (specOf (RingHom.id R)) _ (rigPull_le _ _ hD.he D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig _
    (UnitValue.thU R I e) z (fun _ => m) (fun _ => m') (fun _ => hm₂) (fun _ => hm')
  have e₄ := H e _ (eSec (thickObj R I e G')) z m m' p q
    ((congrArg (fun g => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (g z) ∈
      D.toPre.P.L.U m) (UnitValue.eSec_pGl U' e)).mpr hm₂)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U m') (UnitValue.eSec_pGl U' e)).mpr hm')
    ((congrArg (fun g => g z ∈ U.LG.L.U p)
      (((congrArg (· ≫ (fstG I e G).left) hje)).trans (UnitValue.eSec_fGl (G := G) e))).mpr hp)
    ((congrArg (fun g => g z ∈ U'.LG.L.U q) (UnitValue.eSec_fGl (G := G') e)).mpr hq)
  have ht : UnitValue.thU R I e ≫ specOf (RingHom.id R) = UnitValue.thU R I e :=
    (congrArg (_ ≫ ·) hs).trans (Category.comp_id _)
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G') e, hje] at e₄
  rw [ht, Fintype.prod_unique, zpow_one] at e₃
  exact mul_left_cancel (e₁.trans (e₃.trans ((congrArg _ e₂.symm).trans ((mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄).trans (mul_assoc _ _ _))))))

theorem exists_iso_isPullUnif_of_isPullDeg : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  intro hL hL2 R _ _ _ I hR hI D D' A A' G G' _ _ _ _ hG hG' U U' hD
  obtain ⟨j, hj⟩ := exists_thick_iso_of_isPullDeg hL.globalFns R I hR hI D D' A A' G G' hG hG' U U' hD
  obtain ⟨ΦK, wK, hK⟩ := GlobalTheory.T.exists_genericFibreIso_of_compatible_thickenings hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.generic_iso_extends_semiAbelian_dvr_inducing_formal hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK
  obtain ⟨wL, hwL, H⟩ := GlobalTheory.T.exists_bundleIso_extending_generic_alt hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK ψ hψ
  obtain ⟨hm, -, hf⟩ := hψ
  have hs := Geo.Tor.specOf_id R
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso ((isGrpPullback_of_iso ψ).congr hs.symm rfl)
    (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have hbc' : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left := hbc
  have he₀ : eSec G' ≫ ψ.hom.left = eSec G := congrArg Over.Hom.left hm.one_hom
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G :=
    (congrArg (_ ≫ ·) hbc').trans (he₀.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _)).symm)
  have hI' : I ≠ ⊤ := hI ▸ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hr := pmaps_rig_of_thick_compat hI' U.toUnifPre U'.toUnifPre hD (fun e => (j e).hom) (fun e => (hj e).1)
    he₀ wL hwL H
  refine ⟨ψ, bc, hm, mbc, hbc', (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').2
    ⟨pullCongr hbc'.symm wL, (isGen_iff _).2 (pgen_pullCongr _ ((isGen_iff _).1 hwL)), he, ?_, fun e =>
      ⟨(j e).hom.left, (hf e).symm.trans (congrArg (_ ≫ ·) hbc'.symm), (hj e).2.2,
        fun Z r z jM jM' jL jL' h₁ h₂ h₃ h₄ => ?_⟩⟩⟩
  · refine (Geo.Tor.maps_iff _ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
      (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr _ ?_)
    exact (congrArg (PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig)
      hs).mpr hr
  · rw [gw_pullCongr]
    refine H e Z r z jM jM' jL jL' h₁ h₂ ?_ h₄
    rw [hbc'] at h₃
    exact (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (hf e)).mp h₃

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  first | exact @GlobalTheory.exists_iso_isPullUnif_of_isPullDeg | exact GlobalTheory.exists_iso_isPullUnif_of_isPullDeg | (intros; apply GlobalTheory.exists_iso_isPullUnif_of_isPullDeg <;> assumption)
end
