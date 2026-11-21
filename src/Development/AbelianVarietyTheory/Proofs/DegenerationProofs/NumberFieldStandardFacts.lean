import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineHomOfIsAffineHomPullbackSndOfFpqc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.IsTorus
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective

section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsoFinite

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [CommRing k] {C : Type} [CommRing C] [Algebra k C] {A A' : Over (Sp k)}

theorem comm_bcMap (R : Subalgebra k C)
    (f : (Over.pullback (spMap (algebraMap k C))).obj A ⟶ (Over.pullback (spMap (algebraMap k C))).obj A')
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A')
    (h : bcMap A.hom R.val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A'.hom R.val = bcMap A.hom R.val ≫ g.left := by
  have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (f.left ≫ ·) (bcMap_fst A'.hom R.val)).trans
      (h.symm.trans (Category.assoc _ _ _).symm))
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    have a₁ := congrArg (f.left ≫ ·) (bcMap_snd A'.hom R.val)
    have a₂ := congrArg (bcMap A.hom R.val ≫ ·) hg
    have a₃ := congrArg (· ≫ spMap R.val.toRingHom) hf
    exact a₁.trans ((Category.assoc _ _ _).symm.trans
      (a₃.trans ((bcMap_snd A.hom R.val).symm.trans a₂.symm)))

variable [GrpObj A] [GrpObj A']

theorem exists_fg_iso [QuasiCompact A.hom] [IsSeparated A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [QuasiCompact A'.hom] [IsSeparated A'.hom] [Flat A'.hom] [LocallyOfFinitePresentation A'.hom]
    (e : (Over.pullback (spMap (algebraMap k C))).obj A ≅ (Over.pullback (spMap (algebraMap k C))).obj A')
    [IsMonHom e.hom] :
    ∃ (R : Subalgebra k C)
      (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A'),
      R.FG ∧ IsMonHom g.hom := by
  obtain ⟨R₁, f₁, hR₁, _, h₁⟩ := exists_fg_isMonHom e.hom
  obtain ⟨R₂, f₂, hR₂, _, h₂⟩ := exists_fg_isMonHom e.inv
  let R : Subalgebra k C := R₁ ⊔ R₂
  obtain ⟨g₁, m₁, k₁⟩ := exists_specialise f₁ (Subalgebra.inclusion (le_sup_left : R₁ ≤ R))
  obtain ⟨g₂, m₂, k₂⟩ := exists_specialise f₂ (Subalgebra.inclusion (le_sup_right : R₂ ≤ R))
  have c₁ := comm_bcMap R e.hom g₁ ((congrArg (_ ≫ ·) k₁).trans
    ((bcMap_comp_of_eq_assoc A.hom _ _ R₁.val (fun _ => rfl) _).trans h₁))
  have c₂ := comm_bcMap R e.inv g₂ ((congrArg (_ ≫ ·) k₂).trans
    ((bcMap_comp_of_eq_assoc A'.hom _ _ R₂.val (fun _ => rfl) _).trans h₂))
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom R.val.toRingHom)
    Subtype.val_injective
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsIso g₁ := ExtUnique.isIso_of_isPullback (isGrpPullback_bcMap A R.val).1
    (isGrpPullback_bcMap A' R.val).1 e g₁ g₂ c₁ c₂
  exact ⟨R, asIso g₁, hR₁.sup hR₂, m₁⟩

theorem exists_iso_specialise {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A')
    [IsMonHom g.hom] (ρ : R →ₐ[k] S) :
    ∃ e : (Over.pullback (spMap (algebraMap k S))).obj A ≅ (Over.pullback (spMap (algebraMap k S))).obj A',
      IsMonHom e.hom := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_bcMap A ρ) (isGrpPullback_pullback _ _)
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback _ _) (isGrpPullback_bcMap A' ρ)
  exact ⟨a ≪≫ (Over.pullback (spMap ρ.toRingHom)).mapIso g ≪≫ b,
    inferInstanceAs (IsMonHom (a.hom ≫ (Over.pullback (spMap ρ.toRingHom)).map g.hom ≫ b.hom))⟩

theorem exists_finite_iso : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (T T' : Over (Spec (CommRingCat.of k))) [GrpObj T] [GrpObj T'], IsAffineHom T.hom → IsAffineHom T'.hom → LocallyOfFiniteType T.hom → LocallyOfFiniteType T'.hom → (∃ e : fieldBaseChange k Ω T ≅ fieldBaseChange k Ω T', IsMonHom e.hom) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k') (e : fieldBaseChange k k' T ≅ fieldBaseChange k k' T'), IsMonHom e.hom := by
  intro k Ω _ _ _ T T' _ _ _ _ _ _ ⟨e, he⟩
  have : LocallyOfFinitePresentation T.hom := inferInstance
  have : LocallyOfFinitePresentation T'.hom := inferInstance
  obtain ⟨R, g, hR, hg⟩ := exists_fg_iso (k := k) (C := Ω) (A := T) (A' := T') e
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := .of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  obtain ⟨e', he'⟩ := exists_iso_specialise g (Ideal.Quotient.mkₐ k m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, this, e', he'⟩

end GlobalTheory.IsoFinite
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem torus_isAffineHom_and_splits_finite : NaSt.{0} := by
  intro k _ T _ hT
  obtain ⟨Ω, _, _, X, _, _, _, e, he⟩ := hT.splits
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim (α := Spec (.of k)) _ _⟩⟩
  have haff : IsAffineHom T.hom := by
    refine isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ T.hom _ hsurj hflat inferInstance ?_
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h : IsAffineHom (e.hom.left ≫ (splitTorus (Spec (.of Ω)) X).hom) := inferInstance
    rw [Over.w] at h
    exact h
  refine ⟨haff, ?_⟩
  obtain ⟨k', _, _, _, e', he'⟩ := IsoFinite.exists_finite_iso k Ω T (splitTorus (Spec (.of k)) X)
    haff inferInstance hT.finiteType inferInstance
    ⟨e ≪≫ (Diag.baseChangeIso _ X).symm,
      inferInstanceAs (IsMonHom (e.hom ≫ (Diag.baseChangeIso _ X).inv))⟩
  exact ⟨k', inferInstance, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
    e' ≪≫ Diag.baseChangeIso _ X, inferInstanceAs (IsMonHom (e'.hom ≫ (Diag.baseChangeIso _ X).hom))⟩

end GlobalTheory
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SS

theorem exists_finite_torusExtension_of_torusExt : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  intro k _ G _ ⟨T⟩
  have := T.q_hom
  have := T.i_hom
  obtain ⟨-, k', _, _, hfin, X, _, hfree, hX, e, he⟩ := GlobalTheory.torus_isAffineHom_and_splits_finite k T.T₀ T.isTorus
  refine ⟨k', inferInstance, inferInstance, hfin, ?_⟩
  let f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hq := isPullback_overPullback_map_left f T.q
  have : IsMonHom e.inv := inferInstance
  refine ⟨{ X := X
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.inv ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  atlas_forward_decl GlobalTheory.SS.exists_finite_torusExtension_of_torusExt
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem geometricallyConnected_of_generic_of_special (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] {X : Scheme.{0}} (f : X ⟶ Sp W)
    (h₁ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W L))))
    (h₂ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W (IsLocalRing.ResidueField W))))) :
    GeometricallyConnected f := by
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      GeometricallyConnected (pullback.snd f (spMap a)) →
      ∀ (Z : Scheme.{0}) (fst : Z ⟶ X) (snd : Z ⟶ Sp Ω), IsPullback fst snd f (spMap (ψ.comp a)) →
      ConnectedSpace Z := by
    intro Ω F _ _ a ψ h Z fst snd hZ
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e] at hZ
    have sq : IsPullback (pullback.lift fst (snd ≫ spMap ψ) (hZ.w.trans (Category.assoc _ _ _).symm)) snd
        (pullback.snd f (spMap a)) (spMap ψ) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact hZ) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f (spMap a))
    exact GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd f (spMap a)) _ _ _ sq
  refine ⟨fun Ω _ q Z fst snd hZ => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change IsPullback fst snd f (spMap φ.hom) at hZ
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e] at hZ
    exact key Ω L _ _ h₁ Z fst snd hZ
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    let ψ : IsLocalRing.ResidueField W →+* Ω :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ.hom fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)
    have e : ψ.comp (algebraMap W (IsLocalRing.ResidueField W)) = φ.hom := RingHom.ext fun x => rfl
    rw [← e] at hZ
    exact key Ω _ _ _ h₂ Z fst snd hZ

theorem isSemiAbelian_of_abelian_generic_of_torusExt : NfSt := by
  intro W _ _ _ L _ _ _ A _ hA G _ hc hs hsep hqc ⟨e, _⟩ hT
  obtain ⟨k, _, _, _, ⟨E⟩⟩ := GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension _ _ hT
  have hw : (baseChange W L G).hom = e.hom.left ≫ A.hom := (Over.w e.hom).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hA.proper
  have := hA.geomConnected
  have hp : IsProper (baseChange W L G).hom := by rw [hw]; infer_instance
  have hg : GeometricallyConnected (baseChange W L G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨by rw [hw, Category.comp_id]⟩) hA.geomConnected
  have hk := (GlobalTheory.torusExtension_smooth_geometricallyConnected _ E).2.2.2.1
  have hsurj : Surjective (spMap (algebraMap (IsLocalRing.ResidueField W) k)) :=
    ⟨fun z => ⟨_, Subsingleton.elim (spMap (algebraMap (IsLocalRing.ResidueField W) k)
      (default : PrimeSpectrum _)) z⟩⟩
  have hsp : GeometricallyConnected (specialFibre W G).hom :=
    @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback (specialFibre W G).hom (spMap (algebraMap (IsLocalRing.ResidueField W) k)))
      hsurj hk
  have hgc : GeometricallyConnected G.hom := geometricallyConnected_of_generic_of_special W L G.hom hg hsp
  refine isSemiAbelian_of_proper_generic_of_torusExtension W L G ⟨hc, hs, hsep, hqc, hgc⟩ hp k
    ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) ?_ ?_ ?_
  · rw [RingHom.ker_comp_of_injective _ (algebraMap (IsLocalRing.ResidueField W) k).injective]
    exact IsLocalRing.ker_residue
  · refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective) ?_
    exact Algebra.IsIntegral.isIntegral
  · have e' : spMap ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) =
        spMap (algebraMap (IsLocalRing.ResidueField W) k) ≫ spMap (algebraMap W (IsLocalRing.ResidueField W)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e']
    have : IsMonHom (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso _ _ G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm E⟩

end GlobalTheory.SS
end
