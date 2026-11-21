import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoordReducedFibreClosedPointStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

open Polynomial in

theorem exists_etale_int_surjective_of_finite_field (K : Type) [Field K] [Finite K] :
    ∃ (A : Type) (_ : CommRing A) (β : A →+* K),
      (Int.castRingHom A).Etale ∧ Function.Surjective β := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  let f : ℤ[X] := X ^ (Fintype.card K - 1) - C 1
  let P : StandardEtalePair ℤ :=
    ⟨f, monic_X_pow_sub_C _ (by omega), derivative f, 1, 0, 1, by simp⟩
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := Kˣ)
  have h1 : (α : K) ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ α.ne_zero
  have hm : P.HasMap (α : K) := by
    refine ⟨by simp [P, f, h1], ?_⟩
    have : ((Fintype.card K - 1 : ℕ) : K) = -1 := by
      rw [Nat.cast_sub hq.le]; simp
    simp [P, f, derivative_X_pow, this]
  refine ⟨P.Ring, inferInstance, (P.lift _ hm).toRingHom, ?_, fun k => ?_⟩
  · have : Int.castRingHom P.Ring = algebraMap ℤ P.Ring := RingHom.ext_int _ _
    rw [this]
    exact RingHom.etale_algebraMap.mpr inferInstance
  · by_cases hk : k = 0
    · exact ⟨0, by simp [hk]⟩
    · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hα (Units.mk0 k hk)))
      refine ⟨P.X ^ n, ?_⟩
      have := congrArg Units.val hn
      simpa using this

theorem exists_factor_fromSpecResidueField {K : Type} [Field K] {X : Scheme.{0}}
    (a : Spec (.of K) ⟶ X) {x : X} (hx : a (IsLocalRing.closedPoint K) = x) :
    ∃ φ : X.residueField x ⟶ .of K, Spec.map φ ≫ X.fromSpecResidueField x = a := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X a⟩

theorem exists_factor_of_lift_fromSpecResidueField {Y W : Scheme.{0}} (h : Y ⟶ W) (w : W)
    (ξ : Spec (W.residueField w) ⟶ Y) (hξ : ξ ≫ h = W.fromSpecResidueField w)
    {K : Type} [Field K] (a : Spec (.of K) ⟶ Y)
    (ha : a (IsLocalRing.closedPoint K) = ξ (IsLocalRing.closedPoint (W.residueField w))) :
    ∃ σ : W.residueField w ⟶ .of K, Spec.map σ ≫ ξ = a := by
  obtain ⟨σ, hσ⟩ := exists_factor_fromSpecResidueField a ha
  generalize hy : ξ (IsLocalRing.closedPoint (W.residueField w)) = y at σ hσ
  obtain ⟨φ, hφ⟩ := exists_factor_fromSpecResidueField (K := W.residueField w) ξ hy
  obtain ⟨ψ, hψ⟩ := exists_factor_fromSpecResidueField (K := Y.residueField y)
    (Y.fromSpecResidueField y ≫ h) (x := w) (by
      refine (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg h (Scheme.fromSpecResidueField_apply y _)).trans ?_)
      rw [← hy, ← Scheme.Hom.comp_apply, hξ]
      exact Scheme.fromSpecResidueField_apply w _)
  have h1 : ψ ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono (W.fromSpecResidueField w), Spec.map_comp, Category.assoc, hψ,
      ← Category.assoc, hφ, hξ, Spec.map_id]
    exact (Category.id_comp _).symm
  have h2 : φ ≫ ψ = 𝟙 _ := by
    ext z
    apply φ.hom.injective
    exact congr($h1 (φ z))
  refine ⟨ψ ≫ σ, ?_⟩
  rw [← hσ, ← hφ, ← Spec.map_comp_assoc, ← Category.assoc φ, h2, Category.id_comp]

theorem apply_eq_genericPoint_of_generalizingMap {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [T0Space S] [QuasiSober T] [IrreducibleSpace T] {f : S → T}
    (hf : GeneralizingMap f) {s : S} (hs : s ∈ genericPoints S) : f s = genericPoint T := by
  obtain ⟨s', hs', e⟩ := hf (genericPoint_specializes (f s))
  have h : closure {s} ⊆ closure ({s'} : Set S) := specializes_iff_closure_subset.mp hs'
  have h' := hs.2 isIrreducible_singleton.closure h
  rw [← e, (hs'.antisymm (specializes_iff_closure_subset.mpr h')).eq]

theorem eq_of_specializes_of_locallyQuasiFinite {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {a b : X} (h : a ⤳ b) (e : f a = f b) : a = b := by
  have hd := (f.isDiscrete_preimage_singleton (f b)).to_subtype
  have : (⟨a, e⟩ : f ⁻¹' {f b}) ⤳ ⟨b, rfl⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val this.eq

theorem exists_opens_etale_of_finite_etale_localisation_of_isIntegral
    (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X)
    [LocallyOfFiniteType u] [IsDominant u] (w : W) (U : W.Opens) (hw : IsClosed ({w} : Set W))
    (hU : (U : Set W).Nonempty)
    (huniq : ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w →
      spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' →
        Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a')
    {T V : Scheme.{0}} [IsIntegral T] (g : T ⟶ X) [Etale g] (h : V ⟶ W) [Etale h] (f : V ⟶ T)
    [IsFinite f] (sq : h ≫ u = f ≫ g)
    (hmono : ∀ (Z : Scheme.{0}) (a b : Z ⟶ V), a ≫ h = b ≫ h → a ≫ f = b ≫ f → a = b)
    (v : V) (hv : h v = w)
    (hgeo : ∀ (K : Type) [Field K] (a b : Spec (.of K) ⟶ V), a ≫ f = b ≫ f →
      (a ≫ f) (IsLocalRing.closedPoint K) = f v →
        a ≫ h = b ≫ h ∧ (a ≫ h) (IsLocalRing.closedPoint K) = w) :
    ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian u
  have : LocallyOfFinitePresentation u :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have hNT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g hN
  have := geometricallyReduced_of_smooth h
  have : IsReduced V := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian h
  have : Nonempty V := ⟨v⟩
  have hgh : ∀ z ∈ genericPoints V, h z = genericPoint W := fun z hz =>
    apply_eq_genericPoint_of_generalizingMap (Flat.generalizingMap h) hz
  have hgT : g (genericPoint T) = genericPoint X :=
    apply_eq_genericPoint_of_generalizingMap (Flat.generalizingMap g) (by rw [genericPoints_eq_singleton]; rfl)
  have := TangentCrit.locallyQuasiFinite_of_formallyUnramified g
  have := TangentCrit.locallyQuasiFinite_of_formallyUnramified h
  have hgu : u (genericPoint W) = genericPoint X := by
    apply IsGenericPoint.eq _ (genericPoint_spec X)
    have := (genericPoint_spec W).image u.continuous
    rwa [Set.image_univ, u.denseRange.closure_range] at this
  have hgf : ∀ z ∈ genericPoints V, f z = genericPoint T := fun z hz => by
    refine (eq_of_specializes_of_locallyQuasiFinite g (genericPoint_specializes _) ?_).symm
    rw [← Scheme.Hom.comp_apply, ← sq, Scheme.Hom.comp_apply, hgh z hz, hgu, hgT]
  have hvc : IsClosed ({v} : Set V) :=
    isClosed_of_subset_discrete_closed (t := h ⁻¹' {w}) (by simpa using hv)
      (h.isDiscrete_preimage_singleton w) (hw.preimage h.continuous)
  have htc : IsClosed ({f v} : Set T) := by
    simpa using f.isClosedMap _ hvc
  let U' : T.Opens := ⟨(f '' (h ⁻¹ᵁ U : Set V)ᶜ)ᶜ,
    (f.isClosedMap _ (h ⁻¹ᵁ U).isOpen.isClosed_compl).isOpen_compl⟩
  have hU' : ∀ z : V, f z ∈ U' → h z ∈ U := fun z hz => by
    by_contra H
    exact hz ⟨z, H, rfl⟩
  have hU'ne : (U' : Set T).Nonempty := by
    refine ⟨genericPoint T, ?_⟩
    rintro ⟨z, hz, e⟩
    obtain ⟨z₀, hz₀, hs⟩ := exists_mem_genericPoints_specializes z
    obtain rfl : z₀ = z :=
      eq_of_specializes_of_locallyQuasiFinite f hs ((hgf z₀ hz₀).trans e.symm)
    apply hz
    change h z₀ ∈ U
    rw [hgh z₀ hz₀]
    exact ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hiso : IsIso f := by
    refine isIso_of_isFinite_of_unique_lift_of_classical_points T (g ≫ π) hNT V f hgf (f v) U'
      htc hU'ne fun p _ a a' e hc hr => ?_
    have hcl : spMap (IsLocalRing.residue (OO p))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField (OO p))) = cPt p :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    obtain ⟨h₁, h₂⟩ := hgeo (IsLocalRing.ResidueField (OO p))
      (spMap (IsLocalRing.residue (OO p)) ≫ a) (spMap (IsLocalRing.residue (OO p)) ≫ a')
      (by rw [Category.assoc, e, Category.assoc])
      (by rw [Category.assoc, Scheme.Hom.comp_apply, hcl, hc])
    have hran : ∀ b : Sp (OO p) ⟶ V, b ≫ f = a ≫ f → Set.range (gPt p ≫ b ≫ h) ⊆ U := by
      rintro b hb _ ⟨z, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      apply hU'
      rw [← Scheme.Hom.comp_apply, Category.assoc, hb]
      exact hr ⟨z, rfl⟩
    refine hmono _ a a' (huniq p (a ≫ h) (a' ≫ h) ?_ ?_ ?_ (hran a rfl) (hran a' e.symm)) e
    · rw [Category.assoc, Category.assoc, sq, reassoc_of% e]
    · rwa [Category.assoc, Scheme.Hom.comp_apply, hcl] at h₂
    · simpa only [Category.assoc] using h₁
  have : Etale (h ≫ u) := by rw [sq]; infer_instance
  obtain ⟨V', hV', hE⟩ := exists_opens_range_etale_of_comp V W X h u
  exact ⟨V', hV'.ge ⟨v, hv⟩, hE⟩

theorem exists_opens_etale_of_finite_etale_localisation
    (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X)
    [LocallyOfFiniteType u] [IsDominant u] (w : W) (U : W.Opens) (hw : IsClosed ({w} : Set W))
    (hU : (U : Set W).Nonempty)
    (huniq : ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w →
      spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' →
        Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a')
    {T V : Scheme.{0}} (g : T ⟶ X) [Etale g] (h : V ⟶ W) [Etale h] (f : V ⟶ T)
    [IsFinite f] (sq : h ≫ u = f ≫ g)
    (hmono : ∀ (Z : Scheme.{0}) (a b : Z ⟶ V), a ≫ h = b ≫ h → a ≫ f = b ≫ f → a = b)
    (v : V) (hv : h v = w)
    (hgeo : ∀ (K : Type) [Field K] (a b : Spec (.of K) ⟶ V), a ≫ f = b ≫ f →
      (a ≫ f) (IsLocalRing.closedPoint K) = f v →
        a ≫ h = b ≫ h ∧ (a ≫ h) (IsLocalRing.closedPoint K) = w) :
    ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ π)
  have := IsNormalScheme.of_pred hN
  have := isNormalScheme_of_smooth g
  let T' : T.Opens :=
    IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents (f v)⟩
  have hv' : v ∈ f ⁻¹ᵁ T' := mem_irreducibleComponent
  have hcomp : ∀ {Z : Scheme.{0}} {a b : Z ⟶ (f ⁻¹ᵁ T').toScheme}, a ≫ f ∣_ T' = b ≫ f ∣_ T' →
      (a ≫ (f ⁻¹ᵁ T').ι) ≫ f = (b ≫ (f ⁻¹ᵁ T').ι) ≫ f := fun e => by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e]
  refine exists_opens_etale_of_finite_etale_localisation_of_isIntegral X π hN W u w U hw hU huniq
    (T'.ι ≫ g) ((f ⁻¹ᵁ T').ι ≫ h) (f ∣_ T') ?_ (fun Z a b e₁ e₂ => ?_) ⟨v, hv'⟩ ?_
    fun K _ a b e hc => ?_
  · rw [Category.assoc, sq, morphismRestrict_ι_assoc]
  · rw [← cancel_mono (f ⁻¹ᵁ T').ι]
    exact hmono _ _ _ (by simpa only [Category.assoc] using e₁) (hcomp e₂)
  · rw [Scheme.Hom.comp_apply]
    exact hv
  · have := hgeo K _ _ (hcomp e) (by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_apply, hc,
        ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      rfl)
    simpa only [Category.assoc] using this

theorem exists_opens_etale_of_unique_classical_points :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X) [LocallyOfFiniteType u] [IsSeparated u] [IsDominant u] (w : W) (U : W.Opens), IsClosed ({w} : Set W) → u.QuasiFiniteAt w → (U : Set W).Nonempty → (∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w → spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' → Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a') → ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by
  intro X _ π _ _ hN W _ u _ _ _ w U hw hqf hU huniq

  let Q : W.Opens := u.quasiFiniteLocus
  let w₀ : Q := ⟨w, hqf⟩
  let u₀ : Q.toScheme ⟶ X := Q.ι ≫ u
  have hw₀ : IsClosed ({w₀} : Set Q) := by
    have := hw.preimage Q.ι.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff

  have : Finite (Q.toScheme.residueField w₀) :=
    (jacobson_closedPoints_tools_int Q (u₀ ≫ π)).2.1 w₀ hw₀
  obtain ⟨A, _, β, hA, hβ⟩ :=
    @exists_etale_int_surjective_of_finite_field (Q.toScheme.residueField w₀)
      (Scheme.instFieldCarrierResidueField _ _) this
  let ρ : Sp A ⟶ Sp ℤ := spMap (Int.castRingHom A)
  have : Etale ρ := HasRingHomProperty.Spec_iff.mpr hA
  let g₁ := pullback.fst π ρ
  let h₁ := pullback.fst u₀ g₁
  let f₁ := pullback.snd u₀ g₁
  let β' : Spec (Q.toScheme.residueField w₀) ⟶ Sp A := spMap β
  let ξ₀ : Spec (Q.toScheme.residueField w₀) ⟶ pullback π ρ :=
    pullback.lift (Q.toScheme.fromSpecResidueField w₀ ≫ u₀) β' (specZIsTerminal.hom_ext _ _)
  let ξ : Spec (Q.toScheme.residueField w₀) ⟶ pullback u₀ g₁ :=
    pullback.lift (Q.toScheme.fromSpecResidueField w₀) ξ₀ (pullback.lift_fst _ _ _).symm
  have hξ : ξ ≫ h₁ = Q.toScheme.fromSpecResidueField w₀ := pullback.lift_fst _ _ _
  have hξ' : ξ ≫ f₁ ≫ pullback.snd π ρ = β' := by
    rw [pullback.lift_snd_assoc, pullback.lift_snd]
  let w₁ := ξ (IsLocalRing.closedPoint (Q.toScheme.residueField w₀))
  have hw₁ : h₁ w₁ = w₀ := by
    rw [← Scheme.Hom.comp_apply, hξ, Scheme.fromSpecResidueField_apply]
  have hgeo₁ : ∀ (K : Type) [Field K] (a b : Spec (.of K) ⟶ pullback u₀ g₁), a ≫ f₁ = b ≫ f₁ →
      a (IsLocalRing.closedPoint K) = w₁ → b (IsLocalRing.closedPoint K) = w₁ → a = b := by
    intro K _ a b e ha hb
    obtain ⟨σ, rfl⟩ := exists_factor_of_lift_fromSpecResidueField h₁ w₀ ξ hξ a ha
    obtain ⟨τ, rfl⟩ := exists_factor_of_lift_fromSpecResidueField h₁ w₀ ξ hξ b hb
    have e' := congr($e ≫ pullback.snd π ρ)
    simp only [Category.assoc, hξ'] at e'
    have e'' : CommRingCat.ofHom β ≫ σ = CommRingCat.ofHom β ≫ τ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp]
      exact e'
    have : σ = τ := by
      ext z
      obtain ⟨z, rfl⟩ := hβ z
      exact congr($e'' z)
    rw [this]

  obtain ⟨O, hO, hOw⟩ : ∃ O : Set ↥(pullback u₀ g₁), IsOpen O ∧ O ∩ f₁ ⁻¹' {f₁ w₁} = {w₁} :=
    isDiscrete_iff_forall_exists_isOpen.mp (f₁.isDiscrete_preimage_singleton (f₁ w₁)) w₁ rfl
  let O' : (pullback u₀ g₁).Opens := ⟨O, hO⟩
  let w₂ : O' := ⟨w₁, (hOw.ge rfl).1⟩
  let f₂ := O'.ι ≫ f₁
  obtain ⟨T, g, _, -, V, -, v, -, _, hv⟩ :=
    exists_etale_isCompl_of_quasiFiniteAt f₂ (x := w₂) rfl (f₂.quasiFiniteAt w₂)
  let k : V.toScheme ⟶ pullback u₀ g₁ := V.ι ≫ pullback.fst f₂ g ≫ O'.ι
  let f : V.toScheme ⟶ T := V.ι ≫ pullback.snd f₂ g
  have hk : k ≫ f₁ = f ≫ g := by
    simp only [k, f, Category.assoc]
    rw [← pullback.condition]
  have hkv : k v = w₁ := by
    simp only [k, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hv]
    rfl
  have hfib : ∀ z : V.toScheme, f z = f v → k z = w₁ := fun z hz => by
    refine hOw.le ⟨(pullback.fst f₂ g (V.ι z)).2, ?_⟩
    change f₁ (k z) = f₁ w₁
    rw [← hkv, ← Scheme.Hom.comp_apply k f₁, ← Scheme.Hom.comp_apply k f₁, hk,
      Scheme.Hom.comp_apply f g, Scheme.Hom.comp_apply f g, hz]
  refine exists_opens_etale_of_finite_etale_localisation X π hN W u w U hw hU huniq
    (g ≫ g₁) (k ≫ h₁ ≫ Q.ι) f ?_ (fun Z a b e₁ e₂ => ?_) v ?_ fun K _ a b e hc => ?_
  · rw [← reassoc_of% hk, ← pullback.condition (f := u₀) (g := g₁)]
    simp only [Category.assoc]
    rfl
  · have e₃ : a ≫ k = b ≫ k := by
      apply pullback.hom_ext
      · rw [← cancel_mono Q.ι]
        simpa only [Category.assoc] using e₁
      · rw [Category.assoc a k, Category.assoc b k, hk, reassoc_of% e₂]
    rw [← cancel_mono V.ι]
    apply pullback.hom_ext
    · rw [← cancel_mono O'.ι]
      simpa only [Category.assoc] using e₃
    · simpa only [Category.assoc] using e₂
  · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkv, hw₁]
    rfl
  · have ha : (a ≫ k) (IsLocalRing.closedPoint K) = w₁ := hfib _ hc
    have hb : (b ≫ k) (IsLocalRing.closedPoint K) = w₁ := hfib _ (e ▸ hc :
      (b ≫ f) (IsLocalRing.closedPoint K) = f v)
    have := hgeo₁ K _ _ (by
      rw [Category.assoc a k, Category.assoc b k, hk, reassoc_of% e]) ha hb
    refine ⟨by rw [reassoc_of% this], ?_⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply, ha, Scheme.Hom.comp_apply, hw₁]
    rfl

end GlobalTheory
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem isOpen_singleton_of_isClosed_of_generization {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → y = x) : IsOpen ({x} : Set X) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  have hemb := (X.affineCover.f i).isOpenEmbedding
  rw [← Set.image_singleton, ← hemb.isOpen_iff_image_isOpen]
  have hN : IsLocallyNoetherian (X.affineCover.X i) := isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
  have hA : IsAffine (X.affineCover.X i) := inferInstance
  have : IsNoetherian (X.affineCover.X i) := {}
  have hcl : IsClosed ({y} : Set (X.affineCover.X i)) := by
    have := hx.preimage hemb.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ hemb.injective] at this
  have hgen : ∀ z, z ⤳ y → z = y := fun z hz => hemb.injective (h _ (hz.map hemb.continuous))
  clear hx h hemb
  generalize X.affineCover.X i = Y at *
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hc : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents Y | y ∉ Z}, Z) :=
    (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  convert hc.isOpen_compl using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
  constructor
  · rintro rfl Z hZ hz
    exact hZ.2 hz
  · intro H
    have hm := irreducibleComponent_mem_irreducibleComponents z
    have hy : y ∈ irreducibleComponent z := by
      by_contra hy
      exact H _ ⟨hm, hy⟩ mem_irreducibleComponent
    have hg := (isIrreducible_irreducibleComponent (x := z)).isGenericPoint_genericPoint
      isClosed_irreducibleComponent
    have e := hgen _ (hg.specializes hy)
    rw [e] at hg
    have : z ∈ closure {y} := by
      rw [hg.def]; exact mem_irreducibleComponent
    rwa [hcl.closure_eq] at this

theorem quasiFiniteAt_of_isClosed_of_generization {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → f y = f x → y = x) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have hemb := (f.fiberι (f x)).isEmbedding
  have hx' : f.fiberι (f x) (f.asFiber x) = x := by simp
  apply isOpen_singleton_of_isClosed_of_generization
  · have := hx.preimage hemb.continuous
    convert this using 1
    ext z
    exact ⟨fun hz => by rw [hz]; exact hx', fun hz => hemb.injective (hz.trans hx'.symm)⟩
  · intro y hy
    apply hemb.injective
    rw [hx']
    apply h
    · have := hy.map hemb.continuous
      rwa [hx'] at this
    · have : f.fiberι (f x) y ∈ f ⁻¹' {f x} := by
        rw [← f.range_fiberι]; exact ⟨y, rfl⟩
      exact this

theorem eq_of_specializes_of_basicOpen {X : Scheme.{0}} {y x : X} (h : y ⤳ x)
    (H : ∀ (U : X.Opens) (_ : x ∈ U) (s : Γ(X, U)), y ∈ X.basicOpen s → x ∈ X.basicOpen s) : y = x := by
  refine (h.antisymm ?_).eq
  rw [specializes_iff_forall_open]
  intro V hV hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  obtain ⟨s, hs, hys⟩ := IsAffineOpen.exists_basicOpen_le hU (V := ⟨V, hV⟩) ⟨y, hy⟩ hyU
  exact hs (H U hxU s hys)

theorem quasiFiniteAt_homOfVector_of_coord : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  intro C w W hw u hcl hco
  have := C.proper
  have hlft : LocallyOfFiniteType C.GG.hom := inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom))
  unfold Core.Coord at hco
  change IsLocalRing.maximalIdeal (C.GG.left.presheaf.stalk w) = _ at hco
  set f := AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i)) with hf
  have hover : f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z) = W.ι ≫ C.GG.hom := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType (f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z)) := by
    rw [hover]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have hemb := W.ι.isOpenEmbedding
  apply quasiFiniteAt_of_isClosed_of_generization
  · have := hcl.preimage hemb.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  intro y hy hfy
  have hy' : y.1 ⤳ w := hy.map hemb.continuous
  have hg : C.GG.hom y.1 = C.GG.hom w := by
    have e : ∀ t : W.toScheme, C.GG.hom t.1 = (𝔸(Fin C.g; C.Z) ↘ C.Z) (f t) := by
      intro t
      rw [← Scheme.Hom.comp_apply, hover]; rfl
    rw [e y, hfy, ← e ⟨w, hw⟩]
  apply Subtype.ext
  let P : Ideal (C.G.toScheme.presheaf.stalk w) :=
    (IsLocalRing.maximalIdeal _).comap (C.G.toScheme.presheaf.stalkSpecializes hy').hom
  have hP : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ P ↔ y.1 ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s y.1 (hy'.mem_open U.2 hU), Ideal.mem_comap,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
  have hm : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ IsLocalRing.maximalIdeal _ ↔
        w ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s w hU, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) ≤ P := by
    refine hco.le.trans (sup_le ?_ ?_)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : w ∉ C.G.toScheme.basicOpen (u i) := by
        rw [← hm W hw]
        exact hco.ge (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      have e : ∀ t : W.toScheme, t.1 ∈ C.G.toScheme.basicOpen (u i) ↔
          f t ∈ Scheme.basicOpen _ (AffineSpace.coord C.Z i) := by
        intro t
        have e1 : f ⁻¹ᵁ Scheme.basicOpen _ (AffineSpace.coord C.Z i) =
            W.toScheme.basicOpen (W.topIso.inv.hom (u i)) := by
          rw [Scheme.preimage_basicOpen_top, hf, AffineSpace.homOfVector_appTop_coord]
        have e2 := W.ι_image_basicOpen_topIso_inv (u i)
        rw [← e2, ← e1]
        exact Scheme.Hom.apply_mem_image_iff W.ι (x := t)
      refine (hP W hw (u i)).2 ?_
      rw [e y, hfy, ← e ⟨w, hw⟩]
      exact h1
    · refine (Ideal.IsPrime.radical_le_iff inferInstance).2 ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨V, hV, s, rfl⟩ := C.Z.presheaf.exists_germ_eq a
      rw [Ideal.mem_comap, Scheme.Hom.germ_stalkMap_apply]
      refine (hP _ _ _).2 ?_
      have h1 : C.GG.hom w ∉ C.Z.basicOpen s := by
        rw [C.Z.mem_basicOpen s _ hV]
        exact ha
      rw [← hg] at h1
      intro h2
      apply h1
      have e := Scheme.preimage_basicOpen C.GG.hom s
      exact e.ge h2
  apply eq_of_specializes_of_basicOpen hy'
  intro U hU s hs
  by_contra hn
  exact (hP U hU s).1 (hle ((hm U hU s).2 hn)) hs

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  atlas_forward_decl GlobalTheory.quasiFiniteAt_homOfVector_of_coord
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension {R B : Type} [CommRing R]
    [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B] {g : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension g R B] (ψ : MvPolynomial (Fin g) R →ₐ[R] B)
    (hψ : ψ.toRingHom.QuasiFinite) : Function.Injective ψ := by
  have key : FaithfulSMul R B ∧ Algebra.trdeg R B = g := by
    obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial g R B
    letI : Algebra (MvPolynomial (Fin g) R) B := e.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin g) R) B := he
    haveI : IsScalarTower R (MvPolynomial (Fin g) R) B :=
      IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
    obtain ⟨_, _⟩ :=
      AffinePoints.faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin g) R) B
    refine ⟨FaithfulSMul.trans R (MvPolynomial (Fin g) R) B, ?_⟩
    rw [trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin g) R) B, MvPolynomial.trdeg_of_isDomain]
    simp
  obtain ⟨_, htr⟩ := key
  let x : Fin g → B := fun i => ψ (MvPolynomial.X i)
  have hx : ψ = MvPolynomial.aeval x := MvPolynomial.aeval_unique ψ
  have hr : ψ.range = Algebra.adjoin R (Set.range x) := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hx]
  have h1 : (algebraMap ψ.range B).QuasiFinite :=
    RingHom.QuasiFinite.of_comp (f := algebraMap ψ.range B) (g := ψ.rangeRestrict.toRingHom) hψ
  rw [RingHom.quasiFinite_algebraMap] at h1
  have h2 : Algebra.IsAlgebraic ψ.range B := isAlgebraic_of_quasiFiniteAt ψ.range B ⊥
  rw [hr] at h2
  have h3 := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite R x (by simp [htr])
  rw [hx]
  exact h3.1

theorem isDominant_of_locallyQuasiFinite_affineSpace {Z : Scheme.{0}} [IsIntegral Z]
    {R B : CommRingCat.{0}} [IsDomain R] [IsDomain B] {g : ℕ} (φ : R ⟶ B)
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension g) (i : Spec R ⟶ Z) [IsOpenImmersion i]
    (f : Spec B ⟶ 𝔸(Fin g; Z)) [LocallyQuasiFinite f]
    (hf : f ≫ 𝔸(Fin g; Z) ↘ Z = Spec.map φ ≫ i) : IsDominant f := by
  have hp := AffineSpace.isPullback_map (n := Fin g) i
  have : IsOpenImmersion (AffineSpace.map (Fin g) i) :=
    MorphismProperty.of_isPullback hp.flip ‹_›
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    (hp.lift f (Spec.map φ) hf ≫ (AffineSpace.SpecIso (Fin g) R).hom)
  have e : f = Spec.map ψ ≫ (AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i := by
    rw [hψ]; simp
  have e2 : CommRingCat.ofHom MvPolynomial.C ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← AffineSpace.SpecIso_inv_over, Category.assoc, Iso.hom_inv_id_assoc,
      IsPullback.lift_snd]
  have hq : LocallyQuasiFinite (Spec.map ψ) := by
    rw [e] at ‹LocallyQuasiFinite f›
    exact .of_comp _ ((AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  letI : Algebra R B := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  have hinj := injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension
    (R := R) (B := B) (g := g) { ψ.hom with commutes' := fun r => congr($e2 r) } hq
  have : IsDominant (Spec.map ψ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).1 hinj]; exact bot_le)⟩
  have : IsDominant (AffineSpace.map (Fin g) i) :=
    ⟨(AffineSpace.map (Fin g) i).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  rw [e]
  infer_instance

theorem isDominant_homOfVector_of_quasiFiniteAt :
    ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  intro X Z _ _ t _ g U hU hs u w hw
  have hf := AffineSpace.homOfVector_over t u
  generalize AffineSpace.homOfVector t u = f at hf hw
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ 𝔸(Fin g; Z) ↘ Z) := by rw [hf]; infer_instance
    exact locallyOfFiniteType_of_comp f (𝔸(Fin g; Z) ↘ Z)
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen f.quasiFiniteLocus.isOpen hU
    ⟨w, hw⟩
  let W : X.Opens := U ⊓ f.quasiFiniteLocus
  have h1 : SmoothOfRelativeDimension (0 + g) (X.homOfLE (inf_le_left : W ≤ U) ≫ U.ι ≫ t) :=
    inferInstance
  have h2 : LocallyQuasiFinite (X.homOfLE (inf_le_right : W ≤ f.quasiFiniteLocus) ≫
    f.quasiFiniteLocus.ι ≫ f) := inferInstance
  rw [Scheme.homOfLE_ι_assoc] at h1 h2
  rw [zero_add] at h1
  obtain ⟨Z', hZ', V, hV, hx, e, hsm⟩ := h1.exists_isStandardSmoothOfRelativeDimension ⟨x, hxU, hxV⟩
  have : Nonempty W := ⟨⟨x, hxU, hxV⟩⟩
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  have : Nonempty Z' := ⟨⟨_, e hx⟩⟩
  have : IsDominant (hV.fromSpec ≫ W.ι ≫ f) :=
    isDominant_of_locallyQuasiFinite_affineSpace _ hsm hZ'.fromSpec _ (by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ hZ' hV e]; simp [hf, W])
  have : IsDominant (W.ι ≫ f) := .of_comp hV.fromSpec _
  exact .of_comp W.ι _

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' : ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  atlas_forward_decl GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algHom_eq_of_reduction_eq_of_coords_eq :
    ∀ (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [Algebra.FiniteType O B] (s s' : B →ₐ[O] O) (g : ℕ) (u : Fin g → B), (∀ b, s b - s' b ∈ IsLocalRing.maximalIdeal O) → (∀ i, s (u i) = s' (u i)) → (∀ b, s b = 0 → ∃ t : B, IsUnit (s t) ∧ t * b ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ⊔ (IsLocalRing.maximalIdeal O).map (algebraMap O B)) → s = s' := by
  intro O B _ _ _ _ hft s s' g u hred hu hgen
  classical
  obtain ⟨S, hS⟩ := hft.out
  let N : Ideal O := Ideal.span ((S.image fun b => s' b - s b : Finset O) : Set O)
  have hNfg : N.FG := ⟨_, rfl⟩
  have h1 : ∀ b, s' b - s b ∈ N := by
    intro b
    have hb : b ∈ Algebra.adjoin O (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      exact Ideal.subset_span (by
        simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | algebraMap r => simp
    | add x y _ _ hx hy =>
      have : s' (x + y) - s (x + y) = (s' x - s x) + (s' y - s y) := by
        simp only [map_add]; ring
      rw [this]; exact N.add_mem hx hy
    | mul x y _ _ hx hy =>
      have : s' (x * y) - s (x * y) = s' x * (s' y - s y) + s y * (s' x - s x) := by
        simp only [map_mul]; ring
      rw [this]; exact N.add_mem (N.mul_mem_left _ hy) (N.mul_mem_left _ hx)
  have h2 : ∀ y ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O B),
      ∀ c : B, s' (c * y) - s (c * y) ∈ IsLocalRing.maximalIdeal O * N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      have : s' (c * algebraMap O B a) - s (c * algebraMap O B a) = a * (s' c - s c) := by
        simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]; ring
      rw [this]; exact Ideal.mul_mem_mul ha (h1 c)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have : s' (c * (x + y)) - s (c * (x + y))
          = (s' (c * x) - s (c * x)) + (s' (c * y) - s (c * y)) := by
        simp only [map_add, map_mul]; ring
      rw [this]; exact Ideal.add_mem _ (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      have := hx (c * a)
      rwa [_root_.mul_assoc] at this
  have h3 : ∀ j ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))),
      s j = 0 ∧ s' j = 0 := by
    intro j hj
    have a1 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    have a2 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s' : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, hu i]
    exact ⟨a1 hj, a2 hj⟩
  have h4 : ∀ x, s' x - s x ∈ IsLocalRing.maximalIdeal O * N := by
    intro x
    have hb : s (x - algebraMap O B (s x)) = 0 := by simp
    have hb' : s' (x - algebraMap O B (s x)) = s' x - s x := by simp
    obtain ⟨t, ht, hmem⟩ := hgen _ hb
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hmem
    have ht' : IsUnit (s' t) := by
      by_contra hn
      have m1 : s' t ∈ IsLocalRing.maximalIdeal O := hn
      have m2 := Ideal.add_mem _ (hred t) m1
      rw [sub_add_cancel] at m2
      exact m2 ht
    obtain ⟨j1, j2⟩ := h3 j hj
    have e1 := congrArg s hjy
    have e2 := congrArg s' hjy
    rw [map_add, map_mul, hb, j1] at e1
    rw [map_add, map_mul, hb', j2] at e2
    have h5 := h2 y hy 1
    rw [_root_.one_mul] at h5
    have : s' y - s y = s' t * (s' x - s x) := by
      linear_combination e2 - e1
    rw [this] at h5
    exact (Ideal.unit_mul_mem_iff_mem _ ht').1 h5
  have hN : N = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) N hNfg ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Finset.coe_image] at hz
      obtain ⟨x, _, rfl⟩ := hz
      exact h4 x
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  ext b
  have := h1 b
  rw [hN, Ideal.mem_bot, sub_eq_zero] at this
  exact this.symm

end GlobalTheory
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ

theorem sub_const_mem_span {S L k : Type} [CommRing S] [IsLocalRing S] [CommRing L] [_root_.IsReduced L]
    [Field k] (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1)
    (κ : k →+* L) (ε : L →+* k) (hεκ : ∀ x, ε (κ x) = x) (hu : ∀ x, ε x ≠ 0 → IsUnit x)
    (ψ : S →+* L) {g : ℕ} (v : Fin g → S) (J : Ideal S) (hJ : ∀ x ∈ J, ψ x = 0)
    (hm : IsLocalRing.maximalIdeal S = Ideal.span (Set.range v) ⊔ J.radical) (a : S) :
    ψ a - κ (ε (ψ a)) ∈ Ideal.span (Set.range fun i => ψ (v i)) := by
  have h0 : ∀ b : S, ε (ψ b) = 0 → ψ b ∈ Ideal.span (Set.range fun i => ψ (v i)) := by
    intro b hb
    have hbm : b ∈ IsLocalRing.maximalIdeal S := by
      intro hub
      exact ((hub.map ψ).map ε).ne_zero hb
    have hle : IsLocalRing.maximalIdeal S ≤ (Ideal.span (Set.range fun i => ψ (v i))).comap ψ := by
      rw [hm]
      refine sup_le (Ideal.span_le.2 ?_) ?_
      · rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨i, rfl⟩
      · rintro x ⟨n, hn⟩
        have : IsNilpotent (ψ x) := ⟨n, by rw [← map_pow]; exact hJ _ hn⟩
        rw [Ideal.mem_comap, this.eq_zero]
        exact Ideal.zero_mem _
    exact hle hbm
  by_cases ha : ε (ψ a) = 0
  · rw [ha, map_zero, sub_zero]
    exact h0 a ha
  obtain ⟨n, hn, hn'⟩ := hk _ ha
  have hfin : IsOfFinOrder (ε (ψ a)) := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hn'⟩
  have hpos := hfin.orderOf_pos
  have hprim := IsPrimitiveRoot.orderOf (ε (ψ a))
  have h1 := pow_orderOf_eq_one (ε (ψ a))
  generalize orderOf (ε (ψ a)) = m at hpos hprim h1
  have : NeZero m := ⟨hpos.ne'⟩
  have hm0 : (m : k) ≠ 0 := hprim.neZero'.ne
  have h2 := h0 (a ^ m - 1) (by simp [h1])
  have h3 := Commute.mul_geom_sum₂ (Commute.all (ψ a) (κ (ε (ψ a)))) m
  have h4 : IsUnit (∑ i ∈ Finset.range m, ψ a ^ i * κ (ε (ψ a)) ^ (m - 1 - i)) := by
    apply hu
    simp only [map_sum, map_mul, map_pow, hεκ]
    rw [geom_sum₂_self]
    exact mul_ne_zero hm0 (pow_ne_zero _ ha)
  rw [← Ideal.mul_unit_mem_iff_mem _ h4, h3, ← map_pow κ, h1]
  simpa using h2

theorem exists_reduced_fibre_localRing {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
    [Algebra.Smooth O B] (s : B →ₐ[O] O) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : _root_.IsReduced L) (π : B →+* L)
      (κ : IsLocalRing.ResidueField O →+* L) (ε : L →+* IsLocalRing.ResidueField O),
      π.comp (algebraMap O B) = κ.comp (IsLocalRing.residue O) ∧
      ε.comp π = (IsLocalRing.residue O).comp s ∧ (∀ x, ε (κ x) = x) ∧ (∀ x, ε x ≠ 0 → IsUnit x) ∧
      ∀ (I : Ideal B) (b : B), π b ∈ I.map π → ∃ t : B, IsUnit (s t) ∧
        t * b ∈ I ⊔ (IsLocalRing.maximalIdeal O).map (algebraMap O B) := by
  let M : Ideal B := (IsLocalRing.maximalIdeal O).map (algebraMap O B)
  let D := B ⧸ M
  have hD : _root_.IsReduced D := by
    have : _root_.IsReduced (TensorProduct O (IsLocalRing.ResidueField O) B) :=
      GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (IsLocalRing.ResidueField O) _
    have e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal O)
    have e' := Algebra.TensorProduct.comm O B (IsLocalRing.ResidueField O)
    exact isReduced_of_injective (e.toRingEquiv.trans e'.toRingEquiv) (RingEquiv.injective _)
  let ε₀ : D →+* IsLocalRing.ResidueField O :=
    Ideal.Quotient.lift M ((IsLocalRing.residue O).comp s) (by
      intro b hb
      have : M ≤ RingHom.ker ((IsLocalRing.residue O).comp (s : B →+* O)) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simpa [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff] using hx
      exact this hb)
  let q : Ideal D := RingHom.ker ε₀
  have hq : q.IsPrime := RingHom.ker_isPrime _
  let L := Localization.AtPrime q
  have hε : ∀ y : q.primeCompl, IsUnit (ε₀ y) := fun y => Ne.isUnit y.2
  let ε : L →+* IsLocalRing.ResidueField O := IsLocalization.lift hε
  let κ₀ : IsLocalRing.ResidueField O →+* D :=
    Ideal.quotientMap M (algebraMap O B) Ideal.le_comap_map
  refine ⟨L, inferInstance, inferInstance, inferInstance, (algebraMap D L).comp (Ideal.Quotient.mk M),
    (algebraMap D L).comp κ₀, ε, rfl, ?_, ?_, ?_, ?_⟩
  · ext b
    simp only [ε, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  · intro x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    have : κ₀ (IsLocalRing.residue O x) = Ideal.Quotient.mk M (algebraMap O B x) := rfl
    simp only [ε, RingHom.comp_apply, IsLocalization.lift_eq, this]
    exact congrArg (IsLocalRing.residue O) (s.commutes x)
  · intro x hx
    obtain ⟨⟨d, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff L q]
    intro hd
    apply hx
    simp only [ε]
    rw [IsLocalization.lift_mk'_spec]
    rw [mul_zero]
    exact hd
  · intro I b hb
    rw [← Ideal.map_map, RingHom.comp_apply,
      IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl] at hb
    obtain ⟨t, ht, hb⟩ := hb
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨t, ?_, ?_⟩
    · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact ht
    · rw [← map_mul, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at hb
      simpa [← RingHom.ker_eq_comap_bot] using hb

def ptVal {X : Scheme.{0}} (W : X.Opens) {L : CommRingCat.{0}} (m : Spec L ⟶ W.toScheme) : Γ(X, W) ⟶ L :=
  W.topIso.inv ≫ m.appTop ≫ (Scheme.ΓSpecIso L).hom

theorem ptVal_comp {X : Scheme.{0}} (W : X.Opens) {L L' : CommRingCat.{0}} (m : Spec L ⟶ W.toScheme)
    (φ : L ⟶ L') : ptVal W (Spec.map φ ≫ m) = ptVal W m ≫ φ := by
  simp only [ptVal, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]

theorem comp_toSpecΓ_eq {X : Scheme.{0}} (W : X.Opens) {L : CommRingCat.{0}} (m : Spec L ⟶ W.toScheme) :
    m ≫ W.toSpecΓ = Spec.map (ptVal W m) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ptVal,
    Spec.map_comp, Spec.map_comp, Category.assoc]

theorem exists_stalk_hom {X : Scheme.{0}} (W : X.Opens) (w : X) (hw : w ∈ W) {L : CommRingCat.{0}}
    [IsLocalRing L] (m : Spec L ⟶ W.toScheme) (hm : (m ≫ W.ι) (IsLocalRing.closedPoint L) = w) :
    ∃ ψ : X.presheaf.stalk w ⟶ L, IsLocalHom ψ.hom ∧ Spec.map ψ ≫ X.fromSpecStalk w = m ≫ W.ι ∧
      X.presheaf.germ W w hw ≫ ψ = ptVal W m := by
  subst hm
  have h := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (m ≫ W.ι)
  refine ⟨Scheme.stalkClosedPointTo (m ≫ W.ι), inferInstance, h, ?_⟩
  apply Spec.map_injective
  rw [← comp_toSpecΓ_eq, Spec.map_comp, ← Scheme.Opens.fromSpecStalkOfMem_toSpecΓ, ← Category.assoc]
  congr 1
  rw [← cancel_mono W.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, h]

theorem const_mod_coord {G Z : Scheme.{0}} (q : G ⟶ Z) (W : G.Opens) (w : G) (hw : w ∈ W) {g : ℕ}
    (u : Fin g → Γ(G, W))
    (hc : IsLocalRing.maximalIdeal (G.presheaf.stalk w) =
      Ideal.span (Set.range fun i => (G.presheaf.germ W w hw).hom (u i)) ⊔
      ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom).radical)
    {L k : Type} [CommRing L] [IsLocalRing L] [_root_.IsReduced L]
    [Field k] (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1)
    (κ : k →+* L) (ε : L →+* k) (hεκ : ∀ x, ε (κ x) = x) (hu : ∀ x, ε x ≠ 0 → IsUnit x)
    (m : Sp L ⟶ W.toScheme) (hm : (m ≫ W.ι) (IsLocalRing.closedPoint L) = w)
    (t : Sp k ⟶ Z) (ht : m ≫ W.ι ≫ q = spMap κ ≫ t) (I : Ideal L)
    (hI : I = Ideal.span (Set.range fun i => (ptVal W m).hom (u i))) :
    spMap (Ideal.Quotient.mk I) ≫ m ≫ W.ι =
      spMap (Ideal.Quotient.mk I) ≫ spMap κ ≫ spMap ε ≫ m ≫ W.ι := by
  obtain ⟨ψ, hψ, h1, h2⟩ := exists_stalk_hom W w hw (L := .of L) m hm
  have hκε : spMap ε ≫ spMap κ = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact hεκ x
  have h3 : q.stalkMap w ≫ ψ =
      q.stalkMap w ≫ ψ ≫ CommRingCat.ofHom ε ≫ CommRingCat.ofHom κ := by
    apply Spec.map_injective
    rw [← cancel_mono (Z.fromSpecStalk (q w))]
    simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [reassoc_of% h1, ht, reassoc_of% hκε]
  have h4 : ∀ x ∈ (IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom,
      ψ.hom x = 0 := by
    intro x hx
    have : (IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom ≤ RingHom.ker ψ.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      have e : ψ.hom ((q.stalkMap w).hom r) = κ (ε (ψ.hom ((q.stalkMap w).hom r))) :=
        congr(($h3).hom r)
      change ψ.hom ((q.stalkMap w).hom r) = 0
      by_cases h0 : ε (ψ.hom ((q.stalkMap w).hom r)) = 0
      · rw [e, h0, map_zero]
      · exact absurd (IsUnit.of_map _ _ (IsUnit.of_map _ _ (hu _ h0))) hr
    exact this hx
  have h5 := sub_const_mem_span hk κ ε hεκ hu ψ.hom _ _ h4 hc
  rw [← h1]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change Ideal.Quotient.mk I (ψ.hom a) = Ideal.Quotient.mk I (κ (ε (ψ.hom a)))
  rw [Ideal.Quotient.eq, hI, ← h2]
  exact h5 a

theorem spMap_comp_closedPoint {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] {X : Scheme.{0}} (d : Sp R ⟶ X) :
    (spMap φ ≫ d) (IsLocalRing.closedPoint S) = d (IsLocalRing.closedPoint R) :=
  (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg d (Spec_closedPoint (R := .of R) (S := .of S) (f := CommRingCat.ofHom φ)))

theorem section_eq_of_coord {G Z X : Scheme.{0}} (q : G ⟶ Z) (W : G.Opens) (w : G) (hw : w ∈ W) {g : ℕ}
    (u : Fin g → Γ(G, W))
    (hc : IsLocalRing.maximalIdeal (G.presheaf.stalk w) =
      Ideal.span (Set.range fun i => (G.presheaf.germ W w hw).hom (u i)) ⊔
      ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom).radical)
    {O : Type} [CommRing O] [IsLocalRing O]
    (hk : ∀ x : IsLocalRing.ResidueField O, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1)
    (x : X ⟶ Sp O) [Smooth x] (F : X ⟶ G) (y : Sp O ⟶ Z) (hF : F ≫ q = x ≫ y)
    (hmono : ∀ (T : Scheme.{0}) (α β : T ⟶ X) (r : T ⟶ Sp (IsLocalRing.ResidueField O)),
      α ≫ x = r ≫ spMap (IsLocalRing.residue O) → β ≫ x = r ≫ spMap (IsLocalRing.residue O) →
      α ≫ F = β ≫ F → α = β)
    (c c' : Sp O ⟶ X) (hcx : c ≫ x = 𝟙 _) (hcx' : c' ≫ x = 𝟙 _) (a a' : Sp O ⟶ W.toScheme)
    (ha : c ≫ F = a ≫ W.ι) (ha' : c' ≫ F = a' ≫ W.ι)
    (hw' : (a ≫ W.ι) (IsLocalRing.closedPoint O) = w)
    (hr : spMap (IsLocalRing.residue O) ≫ a = spMap (IsLocalRing.residue O) ≫ a')
    (hu : ∀ i, (ptVal W a).hom (u i) = (ptVal W a').hom (u i)) : c = c' := by
  have hcr : spMap (IsLocalRing.residue O) ≫ c = spMap (IsLocalRing.residue O) ≫ c' :=
    hmono _ _ _ (𝟙 _) (by simp [hcx]) (by simp [hcx']) (by simp only [Category.assoc, ha, ha', reassoc_of% hr])
  have hpt : ∀ d : Sp O ⟶ X, d (IsLocalRing.closedPoint O) =
      (spMap (IsLocalRing.residue O) ≫ d) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) :=
    fun d => (spMap_comp_closedPoint _ d).symm
  have hcc : c' (IsLocalRing.closedPoint O) = c (IsLocalRing.closedPoint O) := by
    rw [hpt, hpt, hcr]
  obtain ⟨B, jj, _, hjj, hjjW⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := c (IsLocalRing.closedPoint O)) (U := F ⁻¹ᵁ W) (by
      change F (c _) ∈ W
      have e : F (c (IsLocalRing.closedPoint O)) = w :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans (by rw [ha]; exact hw')
      exact e ▸ hw)
  have hrange : ∀ d : Sp O ⟶ X, d (IsLocalRing.closedPoint O) ∈ Set.range jj → Set.range d ⊆ Set.range jj := by
    rintro d hd _ ⟨z, rfl⟩
    have := Scheme.preimage_eq_top_of_closedPoint_mem (R := .of O) d (U := jj.opensRange) hd
    have hz : z ∈ d ⁻¹ᵁ jj.opensRange := by rw [this]; trivial
    exact hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (jj ≫ x)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift jj c (hrange c hjj))
  obtain ⟨σ', hσ'⟩ := Spec.map_surjective (IsOpenImmersion.lift jj c' (hrange c' (hcc ▸ hjj)))
  replace hσ : Spec.map σ ≫ jj = c := by rw [hσ, IsOpenImmersion.lift_fac]
  replace hσ' : Spec.map σ' ≫ jj = c' := by rw [hσ', IsOpenImmersion.lift_fac]
  let n : Spec B ⟶ W.toScheme := IsOpenImmersion.lift W.ι (jj ≫ F) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hjjW ⟨z, rfl⟩)
  have hn : n ≫ W.ι = jj ≫ F := IsOpenImmersion.lift_fac _ _ _
  have hna : Spec.map σ ≫ n = a := by
    rw [← cancel_mono W.ι, Category.assoc, hn, reassoc_of% hσ, ha]
  have hna' : Spec.map σ' ≫ n = a' := by
    rw [← cancel_mono W.ι, Category.assoc, hn, reassoc_of% hσ', ha']
  let _ : Algebra O B := φ.hom.toAlgebra
  have hsm : Algebra.Smooth O B := by
    have : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).1 this
  have hsec : ∀ (τ : B ⟶ CommRingCat.of O) (d : Sp O ⟶ X), Spec.map τ ≫ jj = d → d ≫ x = 𝟙 _ →
      ∀ r : O, τ.hom (φ.hom r) = r := by
    intro τ d h1 h2 r
    have : φ ≫ τ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, reassoc_of% h1, h2, Spec.map_id]
    exact congr(($this).hom r)
  let s : B →ₐ[O] O := ⟨σ.hom, hsec σ c hσ hcx⟩
  let s' : B →ₐ[O] O := ⟨σ'.hom, hsec σ' c' hσ' hcx'⟩
  obtain ⟨L, _, _, _, π, κ, ε, h1, h2, h3, h4, h5⟩ := exists_reduced_fibre_localRing s
  have e1 : Spec.map (CommRingCat.ofHom π : B ⟶ .of L) ≫ Spec.map φ =
      spMap κ ≫ spMap (IsLocalRing.residue O) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) h1
  have e2 : spMap ε ≫ Spec.map (CommRingCat.ofHom π : B ⟶ .of L) =
      spMap (IsLocalRing.residue O) ≫ Spec.map σ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) h2
  have e3 : spMap ε ≫ spMap κ = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact h3 x
  have hεloc : IsLocalHom ε := ⟨fun z hz => h4 z hz.ne_zero⟩
  have hm : ((Spec.map (CommRingCat.ofHom π : B ⟶ .of L) ≫ n) ≫ W.ι) (IsLocalRing.closedPoint L) = w := by
    refine (spMap_comp_closedPoint ε _).symm.trans ?_
    rw [Category.assoc, reassoc_of% e2, reassoc_of% hna]
    exact (spMap_comp_closedPoint _ _).trans hw'
  let uB : Fin g → B := fun i => (ptVal W n).hom (u i)
  have hI : (Ideal.span (Set.range uB)).map π = Ideal.span (Set.range fun i =>
      (ptVal W (Spec.map (CommRingCat.ofHom π : B ⟶ .of L) ≫ n)).hom (u i)) := by
    rw [Ideal.map_span, ← Set.range_comp, ptVal_comp]
    rfl
  have key := const_mod_coord q W w hw u hc hk κ ε h3 h4 _ hm (spMap (IsLocalRing.residue O) ≫ y)
    (by rw [Category.assoc, reassoc_of% hn, hF, reassoc_of% hφ.symm, reassoc_of% e1]) _ hI
  generalize hI' : (Ideal.span (Set.range uB)).map π = I at key
  have key2 : spMap (Ideal.Quotient.mk I) ≫ Spec.map (CommRingCat.ofHom π : B ⟶ .of L) =
      spMap (Ideal.Quotient.mk I) ≫ spMap κ ≫ spMap ε ≫ Spec.map (CommRingCat.ofHom π : B ⟶ .of L) := by
    rw [← cancel_mono jj]
    refine hmono _ _ _ (spMap (Ideal.Quotient.mk I) ≫ spMap κ) ?_ ?_ ?_
    · simp only [Category.assoc, ← hφ, e1]
    · simp only [Category.assoc, ← hφ, e1, reassoc_of% e3]
    · simpa only [Category.assoc, hn] using key
  have key3 : ∀ b : B, π b - κ (ε (π b)) ∈ I := by
    intro b
    simp only [← Spec.map_comp] at key2
    rw [← Ideal.Quotient.eq]
    exact congr(($(Spec.map_injective key2)).hom b)
  have hsu : ∀ i, s (uB i) ∈ IsLocalRing.maximalIdeal O := by
    intro i
    obtain ⟨ψ, hψ, -, h⟩ := exists_stalk_hom W w hw (L := .of O) a hw'
    have e : s (uB i) = ψ.hom ((G.presheaf.germ W w hw).hom (u i)) := by
      have := ptVal_comp W n σ
      rw [hna, ← h] at this
      exact (congr(($this).hom (u i))).symm
    rw [e]
    refine map_nonunit ψ.hom _ ?_
    rw [hc]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  have hss : s = s' := by
    refine GlobalTheory.algHom_eq_of_reduction_eq_of_coords_eq O B s s' g uB ?_ ?_ ?_
    · intro b
      have : σ ≫ CommRingCat.ofHom (IsLocalRing.residue O) = σ' ≫ CommRingCat.ofHom (IsLocalRing.residue O) := by
        apply Spec.map_injective
        rw [← cancel_mono jj]
        simp only [Spec.map_comp, Category.assoc, hσ, hσ', hcr]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact congr(($this).hom b)
    · intro i
      have := hu i
      rw [← hna, ← hna', ptVal_comp, ptVal_comp] at this
      exact this
    · intro b hb
      have hb' : ε (π b) = 0 := by
        have : ε (π b) = IsLocalRing.residue O (s b) := congr($h2 b)
        rw [this, hb, map_zero]
      have := key3 b
      rw [hb', map_zero, sub_zero, ← hI'] at this
      obtain ⟨t, ht, htb⟩ := h5 _ _ this
      refine ⟨t, ht, SetLike.le_def.1 ?_ htb⟩
      refine sup_le (Ideal.span_le.2 ?_) le_sup_right
      rintro _ ⟨i, rfl⟩
      have : uB i = (uB i - algebraMap O B (s (uB i))) + algebraMap O B (s (uB i)) := by ring
      rw [SetLike.mem_coe, this]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, ?_⟩))
        (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_))
      · simp
      · simpa using hsu i
  have : σ = σ' := by
    ext b
    exact congr($hss b)
  rw [← hσ, ← hσ', this]

theorem classical_eq_of_coord : ∀ C : Core, C.HasTests → C.Fib → ∀ (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), C.Coord w W hw u → ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme), C.Cl (a ≫ W.ι ≫ C.GG.hom) → a ≫ W.ι ≫ C.GG.hom = a' ≫ W.ι ≫ C.GG.hom → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' → (∀ i, a.appTop.hom (W.topIso.inv.hom (u i)) = a'.appTop.hom (W.topIso.inv.hom (u i))) → a = a' := by
  intro C hT _ w W hw u hC p _ a a' hcl hy hx hr hu
  obtain ⟨τ⟩ := hT p _ hcl
  obtain ⟨c, hc1, hc2⟩ := τ.lift (a ≫ W.ι) (Category.assoc _ _ _)
  obtain ⟨c', hc1', hc2'⟩ := τ.lift (a' ≫ W.ι) ((Category.assoc _ _ _).trans hy.symm)
  have := τ.smooth
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  have hfac := τ.fac
  have hfo := τ.f_over
  have himm := τ.imm
  have key := section_eq_of_coord C.GG.hom W w hw u hC (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).2.1
    (pullback.snd τ.H.hom (spMap τ.j)) (pullback.fst _ _ ≫ τ.f) (a ≫ W.ι ≫ C.GG.hom)
    (by rw [Category.assoc, hfo, pullback.condition_assoc, hfac]) ?_
    (pullback.lift c (𝟙 _) (by simp [hc1])) (pullback.lift c' (𝟙 _) (by simp [hc1']))
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) a a'
    (by rw [pullback.lift_fst_assoc, hc2]) (by rw [pullback.lift_fst_assoc, hc2'])
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Subtype.val hx)) hr
    (fun i => congrArg (Scheme.ΓSpecIso (.of (OO p))).hom.hom (hu i))
  · have : c = c' := by simpa only [pullback.lift_fst] using congr($key ≫ pullback.fst _ _)
    rw [← cancel_mono W.ι, ← hc2, ← hc2', this]
  · intro T α β r hα hβ hF
    let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (rPt p ≫ a ≫ W.ι ≫ C.GG.hom) :=
      pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
        rw [Category.assoc, hfo, pullback.condition_assoc, Category.assoc, hfac])
    have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
    have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have := himm h h1 h2
    have e : pullback.lift (f := τ.H.hom) (g := rPt p ≫ spMap τ.j) (α ≫ pullback.fst _ _) r
          (by rw [Category.assoc, pullback.condition, reassoc_of% hα]) =
        pullback.lift (β ≫ pullback.fst _ _) r
          (by rw [Category.assoc, pullback.condition, reassoc_of% hβ]) := by
      rw [← cancel_mono h]
      apply pullback.hom_ext
      · simp only [Category.assoc, h1, pullback.lift_fst_assoc, hF]
      · simp only [Category.assoc, h2, pullback.lift_snd]
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using congr($e ≫ pullback.fst _ _)
    · rw [hα, hβ]

end GlobalTheory.ZJ
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.classical_point_eq_of_reduction_coords : ∀ C : Core, C.HasTests → C.Fib → ∀ (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), C.Coord w W hw u → ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme), C.Cl (a ≫ W.ι ≫ C.GG.hom) → a ≫ W.ι ≫ C.GG.hom = a' ≫ W.ι ≫ C.GG.hom → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' → (∀ i, a.appTop.hom (W.topIso.inv.hom (u i)) = a'.appTop.hom (W.topIso.inv.hom (u i))) → a = a' := by
  atlas_forward_decl GlobalTheory.ZJ.classical_eq_of_coord
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_fin (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_affineSpace_fin (S : Scheme.{0}) (n : ℕ) :
    SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
    (isStandardSmoothOfRelativeDimension_mvPolynomial_fin (ULift ℤ) n)

namespace ZJ

theorem Core.exists_opens_smoothOfRelativeDimension (C : Core) (hT : C.HasTests) (hF : C.Fib)
    (w : C.G.toScheme) (hc : IsClosed ({w} : Set C.G.toScheme)) :
    ∃ V : C.G.toScheme.Opens, w ∈ V ∧ SmoothOfRelativeDimension C.g (V.ι ≫ C.GG.hom) := by
  obtain ⟨hsep, hlft, -, hint, -, -, ha, hcart, -, -, -, hdom, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  obtain ⟨W, hw, u, -, hu⟩ := GlobalTheory.T.exists_coord_reducedFibre_closedPoint C hT hF w hc
  have hqf := GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord C w W hw u hc hu
  have huniq := GlobalTheory.T.classical_point_eq_of_reduction_coords C hT hF w W hw u hu
  have hint' : IsIntegral C.G.toScheme := hint
  have : Nonempty W.toScheme := ⟨⟨w, hw⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let t : W.toScheme ⟶ C.Z := W.ι ≫ C.GG.hom
  let u' : Fin C.g → Γ(W.toScheme, ⊤) := fun i => W.topIso.inv.hom (u i)
  let v : W.toScheme ⟶ 𝔸(Fin C.g; C.Z) := AffineSpace.homOfVector t u'
  have hv : v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z = t := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ C.GG.hom))
  have : IsSeparated t := inferInstanceAs (IsSeparated (W.ι ≫ C.GG.hom))
  have : IsDominant W.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact W.isOpen.dense ⟨w, hw⟩⟩
  have : IsDominant t := inferInstanceAs (IsDominant (W.ι ≫ C.GG.hom))
  have hA := smoothOfRelativeDimension_affineSpace_fin C.Z C.g
  have : Smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) := SmoothOfRelativeDimension.smooth C.g _
  have : LocallyOfFiniteType v := by
    have : LocallyOfFiniteType (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact locallyOfFiniteType_of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have : IsSeparated v := by
    have : IsSeparated (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact IsSeparated.of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  let U' : W.toScheme.Opens := t ⁻¹ᵁ C.U
  have hU' : (U' : Set W.toScheme).Nonempty := by
    obtain ⟨x, hx⟩ := t.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨x, hx⟩
  have hsm : SmoothOfRelativeDimension C.g (U'.ι ≫ t) := by
    let l : U'.toScheme ⟶ C.A.left := hcart.lift (U'.ι ≫ W.ι) (t ∣_ C.U)
      (by rw [morphismRestrict_ι, Category.assoc])
    have h1 : l ≫ C.a = U'.ι ≫ W.ι := hcart.lift_fst _ _ _
    have h2 : l ≫ C.A.hom = t ∣_ C.U := hcart.lift_snd _ _ _
    have : IsOpenImmersion (l ≫ C.a) := by rw [h1]; infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l C.a
    have h3 : U'.ι ≫ t = l ≫ C.A.hom ≫ C.U.ι := by
      rw [reassoc_of% h2, morphismRestrict_ι]
    have := C.dim
    have h4 : SmoothOfRelativeDimension (0 + (C.g + 0)) (l ≫ C.A.hom ≫ C.U.ι) := inferInstance
    rw [h3]
    simpa using h4
  have : IsDominant v := GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' W.toScheme C.Z t C.g U' hU' hsm u' ⟨w, hw⟩ hqf
  have := C.flat
  have := C.lft
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔸(Fin C.g; C.Z) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) C.normal
  have hc' : IsClosed ({⟨w, hw⟩} : Set W.toScheme) := by
    have := hc.preimage W.ι.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  obtain ⟨V, hV, hE⟩ := exists_opens_etale_of_unique_classical_points 𝔸(Fin C.g; C.Z)
    (𝔸(Fin C.g; C.Z) ↘ C.Z ≫ C.π) hN W.toScheme v ⟨w, hw⟩ U' hc' hqf hU' (by
      intro p _ a a' h hp hr hg _
      refine huniq p a a' ?_ ?_ hp hr fun i => ?_
      · rintro _ ⟨z, rfl⟩
        exact hg ⟨z, rfl⟩
      · change a ≫ t = a' ≫ t
        rw [← hv, reassoc_of% h]
      · have e : ∀ b : Sp (OO p) ⟶ W.toScheme,
            b.appTop.hom (u' i) = (b ≫ v).appTop.hom (AffineSpace.coord C.Z i) := fun b => by
          rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
          exact congrArg _ (AffineSpace.homOfVector_appTop_coord t u' i).symm
        exact (e a).trans ((congrArg (fun c : Sp (OO p) ⟶ 𝔸(Fin C.g; C.Z) =>
          c.appTop.hom (AffineSpace.coord C.Z i)) h).trans (e a').symm))
  have h5 : SmoothOfRelativeDimension (0 + C.g) ((V.ι ≫ v) ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) :=
    inferInstance
  rw [Category.assoc, hv, zero_add] at h5
  refine ⟨(V.ι ≫ W.ι).opensRange, ⟨⟨⟨w, hw⟩, hV⟩, rfl⟩, ?_⟩
  have h6 : SmoothOfRelativeDimension (0 + C.g)
      ((V.ι ≫ W.ι).isoOpensRange.inv ≫ V.ι ≫ t) := inferInstance
  rw [zero_add] at h6
  convert h6 using 1
  rw [← (V.ι ≫ W.ι).isoOpensRange_inv_comp]
  simp only [Category.assoc, t]

theorem Core.smoothOfRelativeDimension_of_hasTests :
    ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  intro C hT hF
  obtain ⟨-, hlft, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  choose V hV hs using C.exists_opens_smoothOfRelativeDimension hT hF
  let V' : {w : C.G.toScheme // IsClosed ({w} : Set C.G.toScheme)} → C.G.toScheme.Opens :=
    fun w => V w.1 w.2
  have htop : iSup V' = ⊤ :=
    (jacobson_closedPoints_tools_int C.G.toScheme (C.GG.hom ≫ C.π)).2.2.1 _ _ fun x hx =>
      ⟨fun _ => trivial, fun _ => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hV x hx⟩⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} C.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} C.g) V' htop
    fun w => hs w.1 w.2

end ZJ
end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests : ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  atlas_forward_decl GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem eq_of_injective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') (h ≫ s) q) (w : a ≫ h = h' ≫ b)
    (hinj : Function.Injective h') {x y : H} (hxy : h x = h y) (hx : s (h x) ∈ Set.range q) : x = y := by
  have sq : IsPullback a h' h b := IsPullback.of_bot hH w hX
  obtain ⟨t, ht⟩ := hx
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hX (h x) t ht.symm
  obtain ⟨x', rfl, hx'⟩ := Scheme.exists_preimage_of_isPullback sq x z hz.symm
  obtain ⟨y', rfl, hy'⟩ := Scheme.exists_preimage_of_isPullback sq y z (hxy.symm.trans hz.symm)
  rw [hinj (hx'.trans hy'.symm)]

theorem mem_range_of_surjective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (w : a ≫ h = h' ≫ b)
    (hsurj : Function.Surjective h') {z : X} (hz : s z ∈ Set.range q) : z ∈ Set.range h := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨z', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hX z t ht.symm
  obtain ⟨x, rfl⟩ := hsurj z'
  exact ⟨a x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩

theorem surjective_of_isClosedImmersion_of_points {k : Type} [Field k] [IsAlgClosed k] {H X : Scheme.{0}}
    (h : H ⟶ X) [IsClosedImmersion h] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hs : ∀ x : Sp k ⟶ X, x ≫ s = 𝟙 _ → ∃ c : Sp k ⟶ H, c ≫ h = x) : Function.Surjective h := by
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.range_eq_univ]
  by_contra hne
  obtain ⟨x, hx, hx'⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
    h.isClosedEmbedding.isClosed_range.isOpen_compl.isLocallyClosed
  obtain ⟨c, hc⟩ := hs _ (pointOfClosedPoint_comp s x hx')
  let a : Sp k := IsLocalRing.closedPoint k
  refine hx ⟨c a, ?_⟩
  rw [← Scheme.Hom.comp_apply, hc]
  exact pointOfClosedPoint_apply s x hx' _

theorem eq_closedPoint_or_mem_range (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp T) :
    x = IsLocalRing.closedPoint T ∨ x ∈ Set.range (spMap (algebraMap T K)) := by
  by_cases hx : PrimeSpectrum.asIdeal x = ⊥
  · refine Or.inr ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)
  · refine Or.inl (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime x).isMaximal hx)

theorem isIso_of_genericFibre_of_specialFibre (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K]
    {H X S' H' X' : Scheme.{0}} (h : H ⟶ X) (s : X ⟶ Sp T) (u : H ⟶ Sp T) (hu : h ≫ s = u)
    [Smooth s] [IsSeparated s] [Smooth u] [IsSeparated u] [QuasiCompact u]
    [ConnectedSpace ↥(pullback u (spMap (algebraMap T K)))]
    (hK : IsPullback (pullback.fst u (spMap (algebraMap T K)) ≫ h) (pullback.snd u (spMap (algebraMap T K)))
      s (spMap (algebraMap T K)))
    {q : S' ⟶ Sp T} (hq : IsLocalRing.closedPoint T ∈ Set.range q)
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') u q) (w : a ≫ h = h' ≫ b)
    (hbij : Function.Bijective h') : IsIso h := by
  subst hu
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have : ConnectedSpace ↥(pullback s t) :=
    hK.isoPullback.hom.surjective.connectedSpace hK.isoPullback.hom.continuous
  obtain ⟨hXi, hN⟩ := isIntegral_and_isNormalScheme_of_smooth T K s
  obtain ⟨hHi, -⟩ := isIntegral_and_isNormalScheme_of_smooth T K (h ≫ s)
  have : IsSeparated h := IsSeparated.of_comp h s
  have : QuasiCompact h := QuasiCompact.of_comp h s
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h s
  let j := pullback.fst (h ≫ s) t
  have hj : IsPullback j (𝟙 _ ≫ pullback.snd (h ≫ s) t) (h ≫ s) t := by
    rw [Category.id_comp]; exact .of_hasPullback _ _
  have hinj : Function.Injective h := fun x y hxy ↦ by
    rcases eq_closedPoint_or_mem_range T K (s (h x)) with hx | hx
    · exact eq_of_injective_baseChange hX hH w hbij.1 hxy (hx ▸ hq)
    · exact eq_of_injective_baseChange hK hj (Category.id_comp _).symm
        (fun _ _ e ↦ e) hxy hx
  have hsurj : Function.Surjective h := fun z ↦ by
    rcases eq_closedPoint_or_mem_range T K (s z) with hx | hx
    · exact mem_range_of_surjective_baseChange hX w hbij.2 (hx ▸ hq)
    · exact mem_range_of_surjective_baseChange (h' := 𝟙 _) hK (Category.id_comp _).symm
        (fun e ↦ ⟨e, rfl⟩) hx
  have : LocallyQuasiFinite h := LocallyQuasiFinite.of_injective hinj
  have : IsOpenImmersion (j ≫ h) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip ‹_›
  have : IsOpenImmersion (j.opensRange.ι ≫ h) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance
  have : IsOpenImmersion h :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict h (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective h).mpr ⟨this, ⟨hsurj⟩⟩

theorem isPullback_of_comp_mono {𝒞 : Type*} [Category 𝒞] {A G P U Z : 𝒞} {a : A ⟶ G} {i : G ⟶ P} [Mono i]
    {s : A ⟶ U} {t : P ⟶ Z} {u : U ⟶ Z} (h : IsPullback (a ≫ i) s t u) : IsPullback a s (i ≫ t) u :=
  ⟨⟨by rw [← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift (c.fst ≫ i) c.snd (by rw [Category.assoc, c.condition]))
    (fun c ↦ by rw [← cancel_mono i, Category.assoc, h.lift_fst]) (fun c ↦ h.lift_snd _ _ _)
    (fun c m h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, ← Category.assoc, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

theorem isAlgClosed_residueField_OO (p : ℕ) [Fact p.Prime] : IsAlgClosed (kb p) :=
  GlobalTheory.NormIntegers.isAlgClosed_residueField
    (Valuation.valuationSubring.integers (Valued.v : Valuation (PadicAlgCl p) NNReal))

theorem Core.testCart_of_fib :
    ∀ C : Core, C.Fib → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart := by
  intro C hF hS p _ y τ
  have := isAlgClosed_residueField_OO p
  have := C.proper
  have := τ.smooth
  have := τ.sep
  have := τ.qc
  have := τ.j_loc
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  let K := FractionRing τ.V
  let t : Sp K ⟶ Sp τ.V := spMap (algebraMap τ.V K)
  let q : Sp (kb p) ⟶ Sp τ.V := rPt p ≫ spMap τ.j
  have hqy : q ≫ τ.y₀ = rPt p ≫ y := by rw [Category.assoc, τ.fac]
  let h : τ.H.left ⟶ pullback C.GG.hom τ.y₀ := pullback.lift τ.f τ.H.hom τ.f_over
  have h₁ : h ≫ pullback.fst _ _ = τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = τ.H.hom := pullback.lift_snd _ _ _

  have hA : IsPullback C.a C.A.hom C.GG.hom C.U.ι :=
    isPullback_of_comp_mono C.cart
  have hφ : IsPullback τ.φ (pullback.snd τ.H.hom t) C.A.hom τ.yK := τ.φ_cart.1
  have := C.ab.geomConnected
  have : ConnectedSpace ↥(pullback τ.H.hom t) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ hφ
  have hK : IsPullback (pullback.fst τ.H.hom t ≫ h) (pullback.snd τ.H.hom t) (pullback.snd C.GG.hom τ.y₀) t := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, h₂, pullback.condition])
      (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    have := hφ.paste_horiz hA
    rw [τ.φ_f, τ.yK_fac] at this
    rw [Category.assoc, h₁]
    exact this

  let h' : pullback τ.H.hom q ⟶ pullback C.GG.hom (rPt p ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
      rw [Category.assoc, τ.f_over, pullback.condition_assoc, hqy])
  have h₁' : h' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂' : h' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion h' := τ.imm h' h₁' h₂'
  let b : pullback C.GG.hom (rPt p ≫ y) ⟶ pullback C.GG.hom τ.y₀ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by
      rw [Category.assoc, hqy, pullback.condition])
  have b₁ : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have b₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q := pullback.lift_snd _ _ _
  have hX : IsPullback b (pullback.snd _ _) (pullback.snd C.GG.hom τ.y₀) q := by
    refine IsPullback.of_right ?_ b₂ (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    rw [b₁, hqy]
    exact .of_hasPullback _ _
  have hsurj : Function.Surjective h' := by
    refine surjective_of_isClosedImmersion_of_points h' (pullback.snd _ _) fun x hx ↦ ?_
    obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
    refine ⟨pullback.lift c (𝟙 _) (by rw [Category.id_comp]; exact hc₁), pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, h₁', pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂', pullback.lift_snd, hx]
  have hq : IsLocalRing.closedPoint τ.V ∈ Set.range q := by
    refine ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    exact IsLocalRing.comap_closedPoint ((IsLocalRing.residue (OO p)).comp τ.j)
  have : IsIso h := isIso_of_genericFibre_of_specialFibre τ.V K h (pullback.snd _ _) τ.H.hom h₂ hK hq hX
    (a := pullback.fst _ _) (h' := h') (by rw [h₂']; exact .of_hasPullback _ _)
    (pullback.hom_ext (by simp only [Category.assoc, h₁, b₁, h₁'])
      (by simp only [Category.assoc, h₂, b₂, reassoc_of% h₂', pullback.condition]))
    ⟨h'.isClosedEmbedding.injective, hsurj⟩
  exact IsPullback.of_iso_pullback ⟨τ.f_over⟩ (asIso h) h₁ h₂

end GlobalTheory.ZJ
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.testCart_of_specialFibre_surjective : ∀ C : Core, C.Fib → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart := by
  atlas_forward_decl GlobalTheory.ZJ.Core.testCart_of_fib
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.fibreLaw_of_testCartesian : ∀ C : Core, C.TestCart → C.FibLaw := by
  first | exact @GlobalTheory.ZJ.Core.fibLaw_of_testCart | exact GlobalTheory.ZJ.Core.fibLaw_of_testCart | (intros; apply GlobalTheory.ZJ.Core.fibLaw_of_testCart <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_mul_of_isSquare_of_fibLaw : ∀ C : Core, C.HasTests → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → C.FibLaw → ∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a := by
  first | exact @GlobalTheory.ZJ.Core.exists_add_extension | exact GlobalTheory.ZJ.Core.exists_add_extension | (intros; apply GlobalTheory.ZJ.Core.exists_add_extension <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_inverse_extension_properClosure : ∀ C : Core, C.HasTests → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → C.FibLaw → ∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a := by
  first | exact @GlobalTheory.exists_inv_extension | exact GlobalTheory.exists_inv_extension | (intros; apply GlobalTheory.exists_inv_extension <;> assumption)
end

section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGrpPullback_of_dominant {W S Z : Scheme.{0}} (j : W ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {H : Over S} [GrpObj H] [Flat H.hom] {G : Over Z} [GrpObj G]
    [IsSeparated G.hom] {y : S ⟶ Z} {f : H.left ⟶ G.left} (hf : IsPullback f H.hom G.hom y)
    (h : IsGrpPullback ((Over.pullback j).obj H) G (j ≫ y) (pullback.fst H.hom j ≫ f)) :
    IsGrpPullback H G y f := by
  let e : H ≅ (Over.pullback y).obj G :=
    Over.isoMk hf.isoPullback hf.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom y = f := hf.isoPullback_hom_fst
  have hs : IsSeparated ((Over.pullback y).obj G).hom := by
    change IsSeparated (pullback.snd G.hom y)
    infer_instance
  have h₁ : IsGrpPullback ((Over.pullback j).obj H) ((Over.pullback y).obj G) j
      (pullback.fst H.hom j ≫ e.hom.left) :=
    (isGrpPullback_pullback G y).cancel (h.congr rfl (by rw [Category.assoc, he]))
      (by rw [Category.assoc, Over.w]; exact pullback.condition)
  have h₂ : IsMonHom e.hom :=
    ExtUnique.isMonHom_of_isGrpPullback (isGrpPullback_pullback H j) h₁ (𝟙 _) e.hom
      (by rw [Over.id_left, Category.id_comp])
  exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G y)).congr (Category.id_comp _) he

theorem Core.nonempty_law : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  rintro C hsm hcart ⟨m, hm⟩ ⟨i, hi⟩
  have := C.proper
  have hsep : IsSeparated C.GG.hom := by
    change IsSeparated (C.G.ι ≫ C.P.hom)
    infer_instance
  have hsmooth : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have hne : Nonempty C.U.toScheme := C.ne.to_subtype
  have hpb : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
    have w : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by
      rw [← C.cart.w, Category.assoc]; rfl
    refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => C.cart.lift (s.fst ≫ C.G.ι) s.snd (by rw [Category.assoc]; exact s.condition))
      (fun s => ?_) (fun s => C.cart.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
    · rw [← cancel_mono C.G.ι, Category.assoc]
      exact C.cart.lift_fst _ _ _
    · apply C.cart.hom_ext
      · rw [C.cart.lift_fst, ← h₁, Category.assoc]
      · rw [C.cart.lift_snd, h₂]
  let e : 𝟙_ (Over C.Z) ⟶ C.GG := Over.homMk C.e C.e_sec
  obtain ⟨grp, -, hη, -, comm, pull⟩ :=
    grpObj_of_dense_open C.Z C.U.toScheme C.U.ι C.GG C.A C.a hpb m i e hm hi C.e_zero
  refine ⟨{ smooth := hsm, zero := congrArg (fun z => z.left) hη, pull := pull, test := fun p _ y τ => ?_ }⟩
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing τ.V (FractionRing τ.V)
  have := τ.smooth
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  exact isGrpPullback_of_dominant (Out.jK τ.V) (hcart p y τ) ((τ.φ_cart.comp pull).congr τ.yK_fac τ.φ_f)

end GlobalTheory.ZJ
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.nonempty_law_abelianSchemeProperClosure : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  first | exact @GlobalTheory.ZJ.Core.nonempty_law | exact GlobalTheory.ZJ.Core.nonempty_law | (intros; apply GlobalTheory.ZJ.Core.nonempty_law <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep C hI
  have hS := GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests C hT hF
  have hC : C.TestCart := GlobalTheory.T.testCart_of_specialFibre_surjective C hF hS
  have hL : C.FibLaw := GlobalTheory.T.fibreLaw_of_testCartesian C hC
  exact GlobalTheory.T.nonempty_law_abelianSchemeProperClosure C hS hC (GlobalTheory.T.exists_mul_of_isSquare_of_fibLaw C hT hS hC hL) (GlobalTheory.T.exists_inverse_extension_properClosure C hT hS hC hL)

end GlobalTheory.ZJ
end
