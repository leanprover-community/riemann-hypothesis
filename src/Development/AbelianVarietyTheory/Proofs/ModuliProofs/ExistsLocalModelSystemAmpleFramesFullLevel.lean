import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsOpenImmersionQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftOfUniqueOfSimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteOrderAutomorphismFixingLevelTrivialOnFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isDominant_pullback_fst_of_flat_of_injective {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (hβ : Function.Injective β) {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap β)) := by
  constructor
  intro x
  have hη : (spMap β) (IsLocalRing.closedPoint F) ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O)
      (PrimeSpectrum.comap β (IsLocalRing.closedPoint F)) (s x)).mp ?_
    intro a ha
    have ha' : β a ∈ IsLocalRing.maximalIdeal F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha'
    have : a = 0 := hβ (by rw [ha', map_zero])
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap s hη
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) hy.mem_closure
  rw [Scheme.Pullback.range_fst]
  exact ⟨_, hy'.symm⟩

theorem isPrimitiveRoot_map_of_isUnit {O k : Type} [CommRing O] [IsDomain O] [Field k] (ψ : O →+* k)
    {z : O} {A : ℕ} (hA : 0 < A) (hz : IsPrimitiveRoot z A) (hu : IsUnit (A : O)) :
    IsPrimitiveRoot (ψ z) A := by
  have : NeZero (A : k) := ⟨by simpa using (hu.map ψ).ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic A ψ]
  exact (hz.isRoot_cyclotomic hA).map

theorem galoisPart_eq_refl_of_fixes_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ρ : C.X ≅ C.X) (σ : KA l ≃+* KA l), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → ∀ (k : Type) [Field k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → σ = RingEquiv.refl _ := by
  intro E _ _ _ H D l Xo S β C r ρ σ hinc hS ⟨e, he⟩ hj hρ hr k _ x hx
  have hA := l.A_pos
  have : NeZero l.A := ⟨hA.ne'⟩
  have hβ : Function.Injective β := fun a b h => Subtype.ext (by
    have h1 := hinc a
    rw [h, hinc b] at h1
    exact h1.symm)
  let z : RZ H S l.A := ⟨zeta l.A, Subring.subset_closure (by simp)⟩
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hβz : β z = (baseKA l).ζ := Subtype.ext (hinc z)
  have hζ : IsPrimitiveRoot (baseKA l).ζ l.A := (baseKA l).ζ_prim
  have hz : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (hβz ▸ hζ) hβ
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have := C.flat
  have hd₁ := isDominant_pullback_fst_of_flat_of_injective β hβ C.s
  have hd₂ : IsDominant C.jQ := ⟨C.jQ_dense⟩
  have hd : IsDominant C.j := by unfold Cpt.j; infer_instance
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s = Xo.s ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  let ev : RZ H S l.A → (Polynomial ℤ →+* RZ H S l.A) := fun y => (Polynomial.aeval y).toRingHom
  have hev : σ.toRingHom.comp (β.comp (ev z)) = β.comp (ev (z ^ a)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [ev, hβz, ha]
  have key : ρ.hom ≫ C.s ≫ spMap (ev z) = C.s ≫ spMap (ev (z ^ a)) := by
    refine ext_of_isDominant C.j ?_
    rw [reassoc_of% hj, reassoc_of% hjs, reassoc_of% hjs, reassoc_of% hr]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← hev]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ C.s)
  have key₂ : CommRingCat.ofHom (ev z) ≫ ψ = CommRingCat.ofHom (ev (z ^ a)) ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, Category.assoc, Category.assoc, ← key, reassoc_of% hx]
  have key₃ : ψ.hom z = ψ.hom z ^ a := by
    have := congrArg (fun f => f.hom Polynomial.X) key₂
    simpa [ev] using this
  have hp : IsPrimitiveRoot (ψ.hom z) l.A := isPrimitiveRoot_map_of_isUnit ψ.hom hA hz hAu
  have hmod : a ≡ 1 [MOD l.A] := by
    have hfin : IsOfFinOrder (ψ.hom z) := hp.isOfFinOrder hA.ne'
    rw [hp.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one]
    exact key₃.symm
  have hσζ : σ (baseKA l).ζ = (baseKA l).ζ := by
    rw [← ha]
    have hfin : IsOfFinOrder (baseKA l).ζ := hζ.isOfFinOrder hA.ne'
    rw [hζ.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one] at hmod
    exact hmod
  have hfinal : σ.toRingHom.toRatAlgHom = AlgHom.id ℚ (KA l) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) (s := {H.rt0, zeta l.A}) rfl ?_
    rintro y (rfl | rfl)
    · exact hρ
    · exact hσζ
  ext1 y
  exact DFunLike.congr_fun hfinal y

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

private theorem exists_monoidHom_aut_of_lies {𝒞 : Type*} [Category 𝒞] {U X : 𝒞} (j : U ⟶ X)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).hom ≫ j)
    (lies : Γ → (X ⟶ X) → Prop) (h1 : lies 1 (𝟙 X)) (hrl : ∀ g, lies g (r g))
    (hml : ∀ g h, lies (g * h) (r h ≫ r g))
    (hj : ∀ g a b, lies g a → lies g b → j ≫ a = j ≫ b → a = b) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).hom = r g := by
  have hone : r 1 = 𝟙 X := by
    refine hj 1 _ _ (hrl 1) h1 ?_
    rw [hr 1, map_one, Category.comp_id]
    exact Category.id_comp j
  have hmul : ∀ g h, r (g * h) = r h ≫ r g := by
    intro g h
    refine hj (g * h) _ _ (hrl _) (hml g h) ?_
    have hm : ∀ a b : Aut U, (a * b).hom = b.hom ≫ a.hom := fun _ _ => rfl
    rw [hr (g * h), map_mul, hm, Category.assoc, reassoc_of% (hr h), hr g]
  have hinv : ∀ g, r g ≫ r g⁻¹ = 𝟙 X ∧ r g⁻¹ ≫ r g = 𝟙 X := fun g =>
    ⟨by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩
  exact ⟨{ toFun := fun g => ⟨r g, r g⁻¹, (hinv g).1, (hinv g).2⟩
           map_one' := Aut.ext hone
           map_mul' := fun g h => Aut.ext (hmul g h) }, fun g => rfl⟩

theorem exists_action_of_extends {U X : Scheme.{0}} (j : U ⟶ X) (hj : ∀ a b : X ⟶ X, j ≫ a = j ≫ b → a = b)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).hom ≫ j) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).hom = r g :=
  exists_monoidHom_aut_of_lies j ρ₀ r hr (fun _ _ => True) trivial (fun _ => trivial) (fun _ _ => trivial)
    (fun _ a b _ _ h => hj a b h)

theorem exists_action_model_of_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) {Z : Scheme.{0}}
    (q : C.X ⟶ Z) {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left)
    (ν : ∀ g, SABMap t t (ρ₀ g).hom) (hβ : IsDedFrac β) (hq : IsIntegralHom q) (hν : ∀ g, (ν g).φ = (τ₀ g).hom)
    (hZ : ∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).hom ≫ C.j ≫ q)
    (hext : ∀ (r : U ⟶ U) (n : SABMap t t r) (f : C.X ⟶ C.X), C.j ≫ f = r ≫ C.j →
      ∃ mu : SABMap C.t C.t f, C.m.φ ≫ mu.φ = n.φ ≫ C.m.φ) :
    ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).hom),
      ∀ g, (mu g).φ = (τ g).hom ∧ C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j ∧
        C.m.φ ≫ (τ g).hom = (τ₀ g).hom ≫ C.m.φ := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have : IsFractionRing O F := hfr
  obtain ⟨hnoeth, _, hsep, hpre, hflat, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have := hnoeth
  have := hsep
  have : QuasiCompact C.j := hqc
  have : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨-, -, hsd, -⟩ := densePart_basic C.X U C.j hpre hflat hdom hqc
  have : IsSchemeTheoreticallyDominant C.j := hsd ‹_›
  have hj1 : ∀ a b : C.X ⟶ C.X, C.j ≫ a = C.j ≫ b → a = b := fun a b h =>
    ExtUnique.hom_ext_of_dominant (terminal.from C.X) (terminal.hom_ext _ _) C.j h
  have hlift : ∀ g, ∃ a : C.X ⟶ C.X, C.j ≫ a = (ρ₀ g).hom ≫ C.j := by
    intro g
    obtain ⟨ρZ, hρZ⟩ := hZ g
    obtain ⟨a, ⟨ha, -⟩, -⟩ := existsUnique_lift_of_densePart C.X U Z C.X C.j C.normal hpre hflat hdom hqc
      q (q ≫ ρZ) ((ρ₀ g).hom ≫ C.j) hq (by rw [Category.assoc, hρZ])
    exact ⟨a, ha⟩
  choose r hr using hlift
  obtain ⟨ρ, hρ⟩ := exists_action_of_extends C.j hj1 ρ₀ r hr
  have hjρ : ∀ g, C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j := fun g => by rw [hρ]; exact hr g
  have hmu : ∀ g, ∃ mu : SABMap C.t C.t (ρ g).hom, C.m.φ ≫ mu.φ = (ν g).φ ≫ C.m.φ :=
    fun g => hext _ (ν g) _ (hjρ g)
  choose mu hmu using hmu
  obtain ⟨hGf, hGs⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian C.t.G C.t.semi
  have := hGf
  have := hGs
  have hcan : ∀ (e : C.X ≅ C.X) (a b : C.t.G.left ⟶ C.t.G.left), a ≫ C.t.G.hom = C.t.G.hom ≫ e.hom →
      b ≫ C.t.G.hom = C.t.G.hom ≫ e.hom → C.m.φ ≫ a = C.m.φ ≫ b → a = b := by
    intro e a b ha hb hab
    have : IsSeparated (Over.mk (C.t.G.hom ≫ e.inv)).hom := by
      show IsSeparated (C.t.G.hom ≫ e.inv)
      infer_instance
    have key := ExtUnique.over_hom_ext_of_isPullback (j := C.j) (X := C.t.G)
      (Y := Over.mk (C.t.G.hom ≫ e.inv)) C.m.cart.1
      (f := Over.homMk a (by simp [reassoc_of% ha])) (g := Over.homMk b (by simp [reassoc_of% hb])) hab
    exact congrArg (fun k => k.left) key
  have hw : ∀ g, (mu g).φ ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).hom := fun g => (mu g).cart.1.w
  obtain ⟨τ, hτ⟩ := exists_monoidHom_aut_of_lies C.m.φ τ₀ (fun g => (mu g).φ)
    (fun g => by rw [hmu, hν]) (fun g a => a ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).hom)
    (by rw [map_one]; exact (Category.id_comp _).trans (Category.comp_id _).symm) hw
    (fun g h => by
      show ((mu h).φ ≫ (mu g).φ) ≫ C.t.G.hom = C.t.G.hom ≫ (ρ (g * h)).hom
      have hm : ∀ a b : Aut C.X, (a * b).hom = b.hom ≫ a.hom := fun _ _ => rfl
      rw [map_mul, hm, Category.assoc, hw g, reassoc_of% (hw h)])
    (fun g a b ha hb hab => hcan (ρ g) a b ha hb hab)
  refine ⟨ρ, τ, mu, fun g => ⟨(hτ g).symm, hjρ g, ?_⟩⟩
  rw [hτ]
  exact (hmu g).trans (by rw [hν])

theorem exists_action_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (C : Cpt c t β) (Z : Scheme.{0}) (q : C.X ⟶ Z) (Γ : Type) [Group Γ] [Finite Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ν : ∀ g, SABMap t t (ρ₀ g).hom), IsDedFrac β → Algebra.FiniteType ℤ O → IsProper t.G.hom → IsIntegralHom q → (∀ g, (ν g).φ = (τ₀ g).hom) → (∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).hom ≫ C.j ≫ q) → ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).hom), ∀ g, (mu g).φ = (τ g).hom ∧ C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j ∧ C.m.φ ≫ (τ g).hom = (τ₀ g).hom ≫ C.m.φ := by
  intro hN E _ _ _ H U F O _ _ c t β C Z q Γ _ _ ρ₀ τ₀ ν hβ hfin hprop hq hν hZ
  exact exists_action_model_of_ext C q ρ₀ τ₀ ν hβ hq hν hZ
    (fun r n f h => Models.exists_sabMap_extending hN E H U F O c t β U F O c t β C C r n f hβ hfin hprop h)

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChange_extends_base_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (h : l₁.A = N) (O₀ O₁ : Type) [CommRing O₀] [CommRing O₁] (β₀ : O₀ →+* KA l₀) (β₁ : O₁ →+* KA l₁) (C : Cpt (Xo l₀).s (Xo l₀).univ.t β₀) (C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁) (b : O₀ →+* O₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (_ : C₁.Above C b r ν) (b' : RZ H n N →+* O₁) (q : C₁.X ⟶ T.Z) (hq : q ≫ T.s = C₁.s ≫ spMap b'), IsDedFrac β₀ → IsDedFrac β₁ → Algebra.FiniteType ℤ O₀ → IsFinite (spMap b) → IsFinite (pullback.lift q C₁.s hq) → C₁.j ≫ q = T.a l₁ h → l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → N.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → Surjective r → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k ∧ β₁.comp b = k.comp β₀) → ∀ (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → C.ExtendsAut r₀ ν₀ := by
  first | exact @GlobalTheory.Models.extendsAut_of_above | exact GlobalTheory.Models.extendsAut_of_above | (intros; apply GlobalTheory.Models.extendsAut_of_above <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevQuot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem over_of_fix (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) {l₀ l₁ : Level H} {X₀ : Moduli D l₀}
    {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r} (hA : l₀.A = 1)
    (hc : LevComp X₁.univ X₀.univ r ν) {f : X₁.X ⟶ X₁.X} (m : SABMap X₁.univ.t X₁.univ.t f)
    (hm : ∀ a, (X₁.univ.eta a).left ≫ m.φ = f ≫ (X₁.univ.eta a).left) (hs : (f ≫ r) ≫ X₀.s = r ≫ X₀.s) :
    f ≫ r = r ∧ m.φ ≫ ν.φ = ν.φ := by
  obtain ⟨n, hn⟩ := LevelCover.sab_comp m ν rfl
  rw [← hn]
  refine LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ n ν (isReduced_moduli X₁) hs
    ⟨fun a => ?_, fun a => ?_⟩ hc
  · rw [hn, ← Category.assoc, LevelCover.sec_pow m _ _ (hm a), Category.assoc, hc.1, Category.assoc]
  · have e : X₁.univ.etaA a ^ (l₁.A / l₀.A) = X₁.univ.eta 0 ^ 0 := by
      rw [hA, Nat.div_one, pow_zero, ← Moduli.LevelAction.map_nsmul_of_add X₁.univ.etaA_add, X₁.univ.etaA_ker]
    rw [hn, Category.assoc, ← hc.2, e, ← Category.assoc, LevelCover.sec_pow m _ _ (hm 0), Category.assoc]

theorem exists_twist_of_fibre (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) (hN : ToroidalLevelCompatibility (H := H) (D := D))
    {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r}
    {j : KA l₀ →+* KA l₁} (hd : l₀.Dvd l₁) (hM : l₁.M = l₀.M) (hMb : l₁.Mb = l₀.Mb)
    (hj : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom j) (hr : r ≫ X₀.s = X₁.s ≫ spMap j)
    (hc : LevComp X₁.univ X₀.univ r ν) {k : Type} [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X₁.X)
    (h₁ : y ≫ r = y' ≫ r) (h₂ : y ≫ X₁.s = y' ≫ X₁.s) :
    ∃ (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La),
      SemiTwist X₁ ρ.hom m.φ g (RingHom.id _) ∧ y' = y ≫ ρ.hom := by
  let c := LevelExist.minCoeff l₁
  have hM' : 0 < l₁.M' := LevelExist.M'_pos l₁
  have hz : ∀ a, a ∣ l₁.M' → zeta a ∈ c.F := fun a ha => by
    rw [LevelCover.zeta_dvd hM' ha]
    exact pow_mem c.zeta_mem _
  have hle : KA l₀ ≤ c.F := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x (rfl | rfl)
    · exact c.le (baseKA l₁).ρ.2
    · exact hz _ (hd.2.2.trans (Nat.dvd_lcm_right _ _))
  let c₀ : Coeff l₀ := ⟨c.F, c.fin, c.conj, hz _ (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _))
    (hd.2.2.trans (Nat.dvd_lcm_right _ _))), hle⟩
  obtain ⟨r', j', ν', hj', hr', e₁, e₂, -, hF⟩ := hN l₀ l₁ X₀ X₁ hd
  obtain rfl : j = j' := RingHom.ext fun x => Subtype.ext ((hj x).trans (hj' x).symm)
  obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ ν ν'
    (isReduced_moduli X₁) (hr.trans hr'.symm) hc ⟨e₁, e₂⟩).1
  obtain ⟨rF, a₁, a₂, -, -, -, htr⟩ := hF c₀ c rfl
  obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ X₁.s)
  obtain ⟨θ, hθ⟩ : ∃ θ : c.F →+* k, θ.comp (IntermediateField.inclusion c.le).toRingHom = β := by
    letI : Algebra (KA l₁) k := β.toAlgebra
    letI : Algebra (KA l₁) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
    haveI := c.fin
    haveI : IsScalarTower ℚ (KA l₁) c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.IsAlgebraic (KA l₁) c.F := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l₁)
    exact ⟨(IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).toRingHom,
      (IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).comp_algebraMap⟩
  have w : y ≫ X₁.s = spMap θ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [LevCover.spMap_comp'', hθ, hβ]
  obtain ⟨⟨g, ρ, hg, ⟨hs, m, b₁, b₂⟩, -, hy⟩, -⟩ := htr k (pullback.lift y (spMap θ) w)
    (pullback.lift y' (spMap θ) (h₂ ▸ w)) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, a₁, pullback.lift_fst_assoc, pullback.lift_fst_assoc, h₁]
      · rw [Category.assoc, Category.assoc, a₂, pullback.lift_snd_assoc, pullback.lift_snd_assoc])
  rw [pullback.lift_fst, pullback.lift_fst_assoc] at hy
  refine ⟨ρ, m, g.f l₁.A, ⟨by rw [hs, LevelCover.spMap_id', Category.comp_id], fun a => ?_, b₂⟩, hy⟩
  rw [← b₁, Moduli.LevelAction.eta_congr X₁.univ (x := g.f l₁.M a) (y := a) (by rw [hM, hMb]; exact hg.2.1 a)]

theorem exists_finite_invariant {l : Level H} (Xo : Moduli D l) :
    ∃ (κ : Type) (_ : Finite κ) (q : (D.La →ₗ[𝓞 E] D.La) → κ), ∀ g g', q g = q g' →
      ∀ x, Xo.univ.etaA (g x) = Xo.univ.etaA (g' x) := by
  obtain ⟨_, _⟩ := LevCover.datum_free D
  obtain ⟨κ, _, q, hq⟩ := LevCover.exists_finite_mod D.La l.A_pos
  haveI : Nonempty D.La := ⟨0⟩
  refine ⟨κ → κ, inferInstance, fun g c => q (g (Function.invFun q c)), fun g g' h x => ?_⟩
  obtain ⟨c, hc⟩ := hq _ _ (Function.invFun_eq (f := q) ⟨x, rfl⟩)
  obtain ⟨c', hc'⟩ := hq _ _ (congrFun h (q x))
  generalize Function.invFun q (q x) = y at hc hc'
  subst hc
  simp only [map_add, map_nsmul, hc', Xo.univ.etaA_add, Xo.univ.etaA_ker, _root_.mul_one]

section

variable {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X}

def twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left) : Submonoid (autOver r) :=
  { carrier := {ω | ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧
      SemiTwist X₁ ω.1.hom (τ ω).hom g σ.toRingHom}
    mul_mem' := by
      rintro a b ⟨g, σ, h₁, h₂⟩ ⟨g', σ', h₁', h₂'⟩
      refine ⟨g' ∘ₗ g, σ.trans σ', by rw [RingEquiv.trans_apply, h₁, h₁'], ?_⟩
      have e₁ : (a * b).1.hom = b.1.hom ≫ a.1.hom := rfl
      have e₂ : (τ (a * b)).hom = (τ b).hom ≫ (τ a).hom := by rw [map_mul]; rfl
      have e₃ : (σ.trans σ').toRingHom = σ'.toRingHom.comp σ.toRingHom := RingHom.ext fun _ => rfl
      rw [e₁, e₂, e₃, LinearMap.coe_comp]
      exact h₂'.comp h₂
    one_mem' := by
      refine ⟨LinearMap.id, RingEquiv.refl _, rfl, ?_⟩
      rw [map_one]
      exact ⟨(Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg _ (LevelCover.spMap_id' _).symm)),
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm,
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm⟩ }

theorem inv_comp_square {X P : Scheme.{0}} (a : X ≅ X) (t : P ≅ P) {b : X ⟶ X} {u : P ⟶ P} {x y : X ⟶ P}
    (p₁ : y ≫ t.hom = a.hom ≫ x) (p₂ : y ≫ u = b ≫ x) : x ≫ t.inv ≫ u = (a.inv ≫ b) ≫ x := by
  rw [Category.assoc, ← p₂, Iso.eq_inv_comp, ← Category.assoc, ← p₁, Category.assoc, Iso.hom_inv_id_assoc]

theorem finite_twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left)
    (mu : ∀ ω : autOver r, SABMap X₁.univ.t X₁.univ.t ω.1.hom) (hmu : ∀ ω, (mu ω).φ = (τ ω).hom) :
    Finite (twistMonoid τ) := by
  obtain ⟨κ, _, q, hq⟩ := exists_finite_invariant X₁
  haveI := finite_fieldAut l₁
  have hch : ∀ ω : twistMonoid τ, ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁),
      SemiTwist X₁ ω.1.1.hom (τ ω.1).hom g σ.toRingHom := fun ω => by
    obtain ⟨g, σ, -, h⟩ := ω.2
    exact ⟨g, σ, h⟩
  choose g σ hg using hch
  refine Finite.of_injective (fun ω => (q (g ω), σ ω)) fun a b hab => ?_
  have h₁ := hq _ _ (congrArg Prod.fst hab)
  have h₂ : σ a = σ b := congrArg Prod.snd hab
  have e₀ : (b.1 * a.1⁻¹).1.hom = a.1.1.inv ≫ b.1.1.hom := rfl
  have e₁ : (τ (b.1 * a.1⁻¹)).hom = (τ a.1).inv ≫ (τ b.1).hom := by rw [map_mul, map_inv]; rfl
  have key : ∀ {x y : X₁.X ⟶ X₁.univ.t.G.left}, y ≫ (τ a.1).hom = a.1.1.hom ≫ x →
      y ≫ (τ b.1).hom = b.1.1.hom ≫ x → x ≫ (mu (b.1 * a.1⁻¹)).φ = (b.1 * a.1⁻¹).1.hom ≫ x := by
    intro x y p₁ p₂
    rw [hmu, e₀, e₁]
    exact inv_comp_square (a.1.1 : X₁.X ≅ X₁.X) (τ a.1) p₁ p₂
  have hid : (b.1 * a.1⁻¹).1.hom = 𝟙 _ :=
    SemiTwist.eq_id (g := id) (σ := RingHom.id _) (mu (b.1 * a.1⁻¹)) ⟨by
      rw [e₀, Category.assoc, (hg b).1, ← h₂, ← (hg a).1, LevelCover.spMap_id', Category.comp_id]
      exact Iso.inv_hom_id_assoc (a.1.1 : X₁.X ≅ X₁.X) _,
      fun x => key ((hg a).2.1 x) ((hg b).2.1 x),
      fun x => key ((hg a).2.2 x) (h₁ x ▸ (hg b).2.2 x)⟩ rfl fun _ => rfl
  have : b.1 * a.1⁻¹ = 1 := Subtype.ext (Iso.ext hid)
  exact Subtype.ext (mul_inv_eq_one.1 this).symm

theorem exists_mem_twistMonoid (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3)
    {ν : SABMap X₁.univ.t X₀.univ.t r} {k : KA l₀ →+* KA l₁} (hA : l₀.A = 1)
    (hk : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k) (hr : r ≫ X₀.s = X₁.s ≫ spMap k)
    (hc : LevComp X₁.univ X₀.univ r ν) (τ : autOver r →* Aut X₁.univ.t.G.left)
    (hτ : ∀ ω, (τ ω).hom ≫ ν.φ = ν.φ ∧ (τ ω).hom ≫ X₁.univ.t.G.hom = X₁.univ.t.G.hom ≫ ω.1.hom)
    (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁)
    (h₁ : σ (baseKA l₁).ρ = (baseKA l₁).ρ) (h₂ : SemiTwist X₁ ρ.hom m.φ g σ.toRingHom) :
    ∃ ω ∈ twistMonoid τ, ω.1.hom = ρ.hom := by
  have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
  have hz : (baseKA l₀).ζ = 1 := by
    have := (baseKA l₀).ζ_prim.pow_eq_one
    rwa [hA, pow_one] at this
  have hσ : σ.toRingHom.comp k = k := field_hom_ext l₀ _ _ (by rw [RingHom.comp_apply, hkρ]; exact h₁)
    (by rw [hz, map_one, map_one])
  obtain ⟨o₁, o₂⟩ := over_of_fix hL hL2 hL3 hA hc m h₂.2.1 (by
    rw [Category.assoc, hr, ← Category.assoc, h₂.1, Category.assoc, LevCover.spMap_comp'', hσ])
  have e : m.φ = (τ ⟨ρ, o₁⟩).hom :=
    ν.cart.1.hom_ext (o₂.trans (hτ _).1.symm) (m.cart.1.w.trans (hτ ⟨ρ, o₁⟩).2.symm)
  exact ⟨⟨ρ, o₁⟩, ⟨g, σ, h₁, e ▸ h₂⟩, rfl⟩

end

theorem exists_level_quotient : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).hom ∧ (τ ω).hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).hom = (ρ ω).hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).hom = (ρ ω).hom ≫ ((Xo l₁).univ.etaA x).left := by
  intro hL hL2 hL3 E _ _ _ H D Xo hpq hN l₀ l₁ r ν k hA hM hMb hk hr hc
  have hd : l₀.Dvd l₁ := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ one_dvd _⟩
  obtain ⟨hfin, het, hsur⟩ : IsFinite r ∧ Etale r ∧ Surjective r := by
    obtain ⟨k', r', ν', hr', hk', hc', -, -, -, h⟩ := LevelMap.exists_levelMap E H D Xo hN l₀ l₁ hd
    obtain rfl : k = k' := RingHom.ext fun x => Subtype.ext ((hk x).trans (hk' x).symm)
    obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ _ _ _ _ _ (Xo l₁).univ _ _ ν ν'
      (isReduced_moduli _) (hr.trans hr'.symm) hc hc').1
    exact h
  obtain ⟨τ, hτ⟩ := exists_liftAut ν.cart.1
  have hmu : ∀ ω : autOver r, ∃ m : SABMap (Xo l₁).univ.t (Xo l₁).univ.t ω.1.hom, m.φ = (τ ω).hom := fun ω => by
    obtain ⟨m, hm⟩ := LevelCover.sab_cancel ν ν ω.1.hom ω.2
    exact ⟨m, ν.cart.1.hom_ext (hm.trans (hτ ω).1.symm) (m.cart.1.w.trans (hτ ω).2.symm)⟩
  choose mu hmu using hmu
  let S := twistMonoid τ
  have hS := exists_mem_twistMonoid hL hL2 hL3 hA hk hr hc τ hτ
  haveI : Finite S := finite_twistMonoid τ mu hmu
  obtain ⟨T, hT⟩ := exists_subgroup_of_finite S
  refine ⟨T, inferInstance, Finite.of_injective (fun t : T => (⟨t.1, (hT _).1 t.2⟩ : S))
      fun a b h => Subtype.ext (congrArg (fun s : S => s.1) h),
    (autOver r).subtype.comp T.subtype, τ.comp T.subtype, fun t => mu t.1,
    Subtype.val_injective.comp Subtype.val_injective, ⟨inferInstance, fun t => t.1.2, ?_⟩, fun t => ?_⟩
  · refine invariant_descends r (fun t : T => t.1.1.hom) (fun t => t.1.2) fun F _ _ y y' hy => ?_
    obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ (Xo l₁).s)
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (y' ≫ (Xo l₁).s)
    have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
    have hb : β.comp k = β'.comp k := LevCover.spMap_inj' (by
      rw [← LevCover.spMap_comp'', ← LevCover.spMap_comp'', ← hβ, ← hβ', Category.assoc, Category.assoc, ← hr,
        ← Category.assoc, hy, Category.assoc])
    obtain ⟨σ, h₁, h₂⟩ := exists_fieldAut l₁ β β' (hkρ ▸ DFunLike.congr_fun hb (baseKA l₀).ρ)
    obtain ⟨ρ, m, g, h₃⟩ := exists_semiTwist_iso hpq l₀ hA hM hMb (Xo l₁) σ h₁
    obtain ⟨a, ha, ea⟩ := hS ρ m g σ h₁ h₃
    obtain ⟨ρ', m', g', h₄, h₅⟩ := exists_twist_of_fibre hL hL2 hL3 hN hd hM hMb hk hr hc (y ≫ ρ.hom) y'
      (by rw [Category.assoc, ← ea, show a.1.hom ≫ r = r from a.2, hy])
      (by rw [Category.assoc, h₃.1, ← Category.assoc, hβ, hβ', LevCover.spMap_comp'', h₂])
    obtain ⟨b, hb', eb⟩ := hS ρ' m' g' (RingEquiv.refl _) rfl h₄
    refine ⟨⟨b * a, (hT _).2 (S.mul_mem hb' ha)⟩, ?_⟩
    rw [h₅, Category.assoc, ← ea, ← eb]
    rfl
  · obtain ⟨g, σ, h₁, h₂⟩ := (hT _).1 t.2
    exact ⟨hmu _, (hτ _).1, h₂.2.1, g, σ, h₁, h₂.1, h₂.2.2⟩

end GlobalTheory.LevQuot
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_level_quotient_by_finite_group : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).hom ∧ (τ ω).hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).hom = (ρ ω).hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).hom = (ρ ω).hom ≫ ((Xo l₁).univ.etaA x).left := by
  atlas_forward_decl GlobalTheory.LevQuot.exists_level_quotient
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_tame_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (s : X ⟶ Sp R) (τ : Γ →* Aut t.G.left) (mu : ∀ g, SABMap t t (ρ g).hom), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (t.G.hom ≫ s) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → (∀ g, (mu g).φ = (τ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst t.G.hom x ≫ (τ g).hom = pullback.fst t.G.hom x) → ∃ (t' : SAB H X') (ν : SABMap t t' π), (∀ g, (τ g).hom ≫ ν.φ = ν.φ) ∧ (Good t → PushInvertible t.G t.PP.L → Good t') := by
  first | exact @GlobalTheory.exists_sab_descent_of_tame_quotient | exact GlobalTheory.exists_sab_descent_of_tame_quotient | (intros; apply GlobalTheory.exists_sab_descent_of_tame_quotient <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).hom ≫ t.G.hom = t.G.hom ≫ (ρ g).hom ∧ (τ g).hom ≫ ν.φ = ν.φ ∧ (τ g).hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  first | exact @GlobalTheory.exists_sabMap_of_quotient | exact GlobalTheory.exists_sabMap_of_quotient | (intros; apply GlobalTheory.exists_sabMap_of_quotient <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.QuotModel

theorem injective_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Function.Injective β := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  exact IsFractionRing.injective O F

theorem mono_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) : Mono (spMap β) := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  have : Epi (CommRingCat.ofHom β) := ⟨fun {Z} g₁ g₂ hg => by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (j := g₁.hom) (k := g₂.hom) ?_
    have e := congrArg CommRingCat.Hom.hom hg
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    exact e⟩
  exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom β).op

theorem mem_range_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : Function.Injective β) (p : Sp O) :
    p ∈ Set.range (spMap β) ↔ p.asIdeal = ⊥ := by
  have hk : RingHom.ker β = ⊥ := (RingHom.injective_iff_ker_eq_bot β).mp h
  constructor
  · rintro ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    show Ideal.comap β q.asIdeal = ⊥
    rw [hq, ← RingHom.ker_eq_comap_bot, hk]
  · intro hp
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap β ⊥ = p.asIdeal
    rw [hp, ← RingHom.ker_eq_comap_bot, hk]

theorem densePart {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) {X U : Scheme.{0}}
    (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (h₁ : Flat s) (h₂ : IsProjOver s) (h₃ : IsOpenImmersion jQ)
    (h₄ : Dense (Set.range jQ)) :
    IsLocallyNoetherian X ∧ genericPoints X ⊆ Set.range (jQ ≫ pullback.fst _ _ : U ⟶ X) ∧
      ∀ u : U, IsIso ((jQ ≫ pullback.fst _ _ : U ⟶ X).stalkMap u) := by
  obtain ⟨⟨hdom, hded⟩, -, hfr⟩ := h
  let _ := β.toAlgebra
  obtain ⟨hN, -, -, hpre, hfl, hdo, hqc⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ h₁ h₂ h₃ h₄
  obtain ⟨hg, hst, -⟩ := GlobalTheory.densePart_basic X U _ hpre hfl hdo hqc
  exact ⟨hN, hg, hst⟩

private theorem isReduced_of_isNormalScheme' (X : Scheme.{0}) (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

end GlobalTheory.QuotModel

open GlobalTheory.QuotModel in

theorem GlobalTheory.Models.exists_quotient_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).hom ∧ C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j ∧ C.m.φ ≫ (τ g).hom = (τ₀ g).hom ≫ C.m.φ ∧ (τ₀ g).hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).hom = x → pullback.fst C.t.G.hom x ≫ (τ g).hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' Γ _ _ C b k r ν ρ₀ τ₀ ρ τ mu hβ hβ' hcomp hfin hrc hr hprop hmu hqp
    htame hin hgood hpush

  have sq : ∀ {S S' : Scheme.{0}} {ta : SAB H S} {tb : SAB H S'} {f : S ⟶ S'} (m : SABMap ta tb f),
      m.φ ≫ tb.G.hom = ta.G.hom ≫ f := fun m => m.cart.1.w
  have sqm : C.m.φ ≫ C.t.G.hom = t.G.hom ≫ C.j := sq C.m

  obtain ⟨X', π, s', jQ, hπ, hπfin, hπs, hnorm, hproj, hflat, hjover, hjopen, hjdense, hjc, hgen⟩ :=
    GlobalTheory.exists_quotient_model_scheme E H U F O c t β Γ C U' F' O' c' β' b k r ρ₀ ρ hβ hβ' hcomp hfin hrc hr
      (fun g => (hmu g).2.1)
  obtain ⟨hN', -, -⟩ := densePart hβ' s' jQ hflat hproj hjopen hjdense
  obtain ⟨-, hgenC, hstC⟩ := densePart hβ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hredX : IsReduced C.X := isReduced_of_isNormalScheme' _ C.normal
  have hgab : genericPoints C.X ⊆ abLocus C.t.G := by
    intro x hx
    obtain ⟨u, rfl⟩ := hgenC hx
    have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
      rw [C.ab_gen]; exact ⟨u, rfl⟩
    exact hu

  obtain ⟨t₁, ν', hν'τ, hgood'⟩ :=
    GlobalTheory.T.exists_semiAbelian_descent_tame_quotient E H Γ O C.X X' ρ π C.t C.s τ mu hπ hπfin hqp ⟨hredX, hgab⟩ (fun g => (hmu g).1) htame hin
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' C.m
  have key : ∀ (f : U ⟶ X') (n : SABMap t t₁ f), f = r ≫ jQ ≫ pullback.fst _ _ →
      ∃ n' : SABMap t t₁ (r ≫ jQ ≫ pullback.fst _ _), n'.φ = n.φ := by
    rintro f n rfl; exact ⟨n, rfl⟩
  obtain ⟨n₂, hn₂⟩ := key _ n hjc.symm

  have hredU : IsReduced U := by
    have : ∀ u : U, _root_.IsReduced (U.presheaf.stalk u) := by
      intro u
      have hI : IsIso ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u) := hstC u
      exact isReduced_of_injective (inv ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u)).hom
        (ConcreteCategory.bijective_of_isIso _).1
    exact isReduced_of_isReduced_stalk U
  have hmono : Mono C.j := by
    have := mono_spMap hβ
    have := C.jQ_open
    dsimp only [Cpt.j]; infer_instance
  have hτ : ∀ g, (τ₀ g).hom ≫ t.G.hom = t.G.hom ≫ (ρ₀ g).hom ∧ (τ₀ g).hom ≫ ν.φ = ν.φ ∧
      (τ₀ g).hom ≫ n₂.φ = n₂.φ := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hmu g
    refine ⟨(cancel_mono C.j).mp ?_, h4, ?_⟩
    · calc ((τ₀ g).hom ≫ t.G.hom) ≫ C.j = ((τ₀ g).hom ≫ C.m.φ) ≫ C.t.G.hom := by
            simp only [Category.assoc]; rw [← sqm]
        _ = (C.m.φ ≫ (mu g).φ) ≫ C.t.G.hom := by rw [← h3, h1]
        _ = C.m.φ ≫ C.t.G.hom ≫ (ρ g).hom := by simp only [Category.assoc]; rw [sq (mu g)]
        _ = t.G.hom ≫ C.j ≫ (ρ g).hom := by rw [← Category.assoc, sqm, Category.assoc]
        _ = (t.G.hom ≫ (ρ₀ g).hom) ≫ C.j := by rw [h2, Category.assoc]
    · rw [hn₂, hn, ← Category.assoc, ← h3, Category.assoc, hν'τ g]
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient E H Γ U U' X' ρ₀ r t t' t₁ τ₀ ν _ n₂ hr hredU hprop hτ

  have hπsurj : Function.Surjective π := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ C.X X' ρ π hπ).2.1.surj
  have hrsurj : Function.Surjective r := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ U U' ρ₀ r hr).2.1.surj
  have habπ : ∀ x, π x ∈ abLocus t₁.G ↔ x ∈ abLocus C.t.G := fun x =>
    abLocus_pullback abLocusOne t₁.semi ν'.cart.1 x

  have hbint : ∀ p : Sp O, (spMap b p).asIdeal = ⊥ → p.asIdeal = ⊥ := by
    intro p hp
    obtain ⟨⟨hdO, -⟩, -, -⟩ := hβ
    obtain ⟨⟨hdO', -⟩, -, -⟩ := hβ'
    let _ := b.toAlgebra
    have h2 : IsFinite (Spec.map (CommRingCat.ofHom b)) := hfin
    rw [IsFinite.SpecMap_iff] at h2
    have : Module.Finite O' O := h2
    have : Algebra.IsIntegral O' O := inferInstance
    exact Ideal.eq_bot_of_comap_eq_bot (R := O') hp
  have hpre : Function.Injective (pullback.fst s' (spMap β')) := by
    obtain ⟨-, -, hfr'⟩ := hβ'
    let _ := β'.toAlgebra
    have : IsPreimmersion (spMap β') := IsPreimmersion.of_isLocalization (nonZeroDivisors O')
    exact (pullback.fst s' (spMap β')).isEmbedding.injective
  have hab : pullback.fst s' (spMap β') ⁻¹' abLocus t₁.G = Set.range jQ := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx⟩ := hπsurj (pullback.fst s' (spMap β') w)
      have hxab : x ∈ abLocus C.t.G := (habπ x).1 (by rw [hx]; exact hw)
      have hs' : (s' (pullback.fst s' (spMap β') w)).asIdeal = ⊥ := by
        have e : s' (pullback.fst s' (spMap β') w) = spMap β' (pullback.snd s' (spMap β') w) := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        rw [e]
        exact (mem_range_spMap (injective_of_isDedFrac hβ') _).1 ⟨_, rfl⟩
      have hsx : (C.s x).asIdeal = ⊥ := by
        apply hbint
        have e : spMap b (C.s x) = s' (π x) := by
          rw [← Scheme.Hom.comp_apply, ← hπs, Scheme.Hom.comp_apply]
        rw [e, hx]
        exact hs'
      obtain ⟨q, hq⟩ := (mem_range_spMap (injective_of_isDedFrac hβ) (C.s x)).2 hsx
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.s) (g := spMap β) x q hq.symm
      have hz : z ∈ Set.range C.jQ := by
        rw [← C.ab_gen]
        show pullback.fst C.s (spMap β) z ∈ abLocus C.t.G
        rw [hz1]
        exact hxab
      obtain ⟨u, rfl⟩ := hz
      obtain ⟨u', hu'⟩ := (hgen x).2 ⟨u, hz1⟩
      exact ⟨u', hpre (hu'.trans hx)⟩
    · rintro ⟨u', rfl⟩
      obtain ⟨u, rfl⟩ := hrsurj u'
      have e : pullback.fst s' (spMap β') (jQ (r u)) = π (C.j u) := by
        have h5 := congrArg (fun f : U ⟶ X' => f u) hjc
        simpa only [Scheme.Hom.comp_apply] using h5
      show pullback.fst s' (spMap β') (jQ (r u)) ∈ abLocus t₁.G
      rw [e, habπ]
      have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
        rw [C.ab_gen]; exact ⟨u, rfl⟩
      exact hu
  refine ⟨⟨X', s', hnorm, hproj, hflat, jQ, hjover, hjopen, hjdense, t₁, m', hab⟩, hgood' hgood hpush,
    ⟨⟨π, hπs, ?_, ν', hjc.symm, ?_⟩⟩⟩
  · refine MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _ (pullback.fst s' (spMap b))
      inferInstance ?_
    rw [pullback.lift_fst]
    exact hπfin
  · rw [hm', hn₂, hn]

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_model_by_tame_finite_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).hom ∧ C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j ∧ C.m.φ ≫ (τ g).hom = (τ₀ g).hom ≫ C.m.φ ∧ (τ₀ g).hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).hom = x → pullback.fst C.t.G.hom x ≫ (τ g).hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  atlas_forward_decl GlobalTheory.Models.exists_quotient_model
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelLabel_extends_of_orthogonal_to_extended : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsUnit (l.A : Γ(X, ⊤)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (a : D.La), (∀ a', (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a').left ≫ μ₀.φ) → (l.A : ℤ) ∣ D.EF a a') → (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) := by
  first | exact @GlobalTheory.extends_of_orthogonal_to_extended | exact GlobalTheory.extends_of_orthogonal_to_extended | (intros; apply GlobalTheory.extends_of_orthogonal_to_extended <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.StabTame

theorem act_natCast {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) (n : ℕ) :
    a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

theorem exists_geomPoint (S : Scheme.{0}) [Nonempty S] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k), Nonempty (Sp k ⟶ S) := by
  obtain ⟨z⟩ : Nonempty S := inferInstance
  exact ⟨AlgebraicClosure (S.residueField z), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom (algebraMap (S.residueField z) _)) ≫ S.fromSpecResidueField z⟩⟩

theorem iterate_modN {V : Type} [AddCommGroup V] (N : ℕ) (e : LinearMap.BilinForm ℤ V) (P : V → Prop) (g : V →+ V)
    (hg : ∀ v w, (N : ℤ) ∣ e (g v) (g w) - e v w) (hP : ∀ v, P v → ∃ c, g v - v = N • c)
    (hco : ∀ v, (∀ w, P w → (N : ℤ) ∣ e v w) → P v) (v : V) : ∃ c, g^[N] v - v = N • c := by
  have h1 : P (g v - v) := by
    refine hco _ fun w hw => ?_
    obtain ⟨c, hc⟩ := hP w hw
    have e1 : e (g v - v) w = (e (g v) (g w) - e v w) - (N : ℤ) * e (g v) c := by
      have : g w = w + N • c := by rw [← hc]; abel
      rw [this]
      simp only [map_sub, map_add, map_nsmul, LinearMap.sub_apply, nsmul_eq_mul]
      ring
    rw [e1]
    exact dvd_sub (hg v w) (dvd_mul_right _ _)
  obtain ⟨d, hd⟩ := hP _ h1
  have key : ∀ n : ℕ, ∃ c, g^[n] v = v + n • (g v - v) + N • c := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨g c + n • d, ?_⟩
      have : g (g v - v) = (g v - v) + N • d := by rw [← hd]; abel
      rw [Function.iterate_succ_apply', hc, map_add, map_add, map_nsmul, map_nsmul, this]
      simp only [nsmul_add, succ_nsmul, smul_comm N n d]
      abel
  obtain ⟨c, hc⟩ := key N
  exact ⟨g v - v + c, by rw [hc, nsmul_add]; abel⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section

variable {B : Type} [CommRing B] {b : Base l B} {U : Scheme.{0}} {s : U ⟶ Sp B}

theorem modN_of_point_eq (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) {a a' : D.La}
    (h : u ≫ (o.etaA a').left = u ≫ (o.etaA a).left) : ∃ c, a' - a = l.A • c := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, -, hA, -⟩ := o.geom k u β.hom hβ.symm
  have h1 : I.ev l.A a' = I.ev l.A a := by
    rw [← hA, ← hA]
    exact Over.OverMorphism.ext h
  have h2 := I.add l.A (a' - a) a
  rw [sub_add_cancel, h1] at h2
  exact (I.ker l.A l.A_pos _).1 (right_eq_mul.1 h2)

theorem isometry_modN (o : Obj D l b s) [Nonempty U] (r : U ⟶ U) (ν : SABMap o.t o.t r) (hr : r ≫ s = s)
    {a a' c c' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    (hc : (o.etaA c').left ≫ ν.φ = r ≫ (o.etaA c).left) : (l.A : ℤ) ∣ D.EF a' c' - D.EF a c := by
  obtain ⟨k, _, _, ⟨u⟩⟩ := exists_geomPoint U
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, hζ, hA, -⟩ := o.geom k u β.hom hβ.symm
  obtain ⟨-, J, hζ', hA', -⟩ := o.geom k (u ≫ r) β.hom (by rw [Category.assoc, hr]; exact hβ.symm)
  have hz : I.ζ l.A = J.ζ l.A := Units.ext (hζ.trans hζ'.symm)
  have hL : LBIso o.t.PP.L (o.t.PP.L.pull ν.φ) := ν.lin.imp fun _ h => h.1
  have mv : ∀ {x x' : D.La}, (o.etaA x').left ≫ ν.φ = r ≫ (o.etaA x).left →
      (J.ev l.A x).left = (I.ev l.A x').left ≫ ν.φ := by
    intro x x' h
    rw [← hA, ← hA']
    show (u ≫ r) ≫ (o.etaA x).left = (u ≫ (o.etaA x').left) ≫ ν.φ
    rw [Category.assoc, Category.assoc, h]
  have w := (weilIs_grpPullback_of_comm U U o.t.G o.t.G r ν.φ o.t.PP.L o.t.PP.L o.t.PP.isLB o.t.PP.isLB ν.cart hL
    (Over.mk u) l.A _ _ (J.ev l.A a) (J.ev l.A c) _ (mv ha) (mv hc)).1 (I.isom l.A l.A_pos a' c')
  have e := weilIs_unique_fieldPoint U o.t.G o.t.PP.L o.t.PP.isLB k (u ≫ r) l.A _ _ _ _ w (J.isom l.A l.A_pos a c)
  rw [hz] at e
  rw [← (J.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, e, mul_inv_cancel]

end

theorem modN_of_extends {B : Type} [CommRing B] {b : Base l B} {X U : Scheme.{0}} [IsReduced X] {s : U ⟶ Sp B}
    (j : U ⟶ X) [IsDominant j] (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j) (hN : IsUnit (l.A : Γ(X, ⊤)))
    (r : U ⟶ U) (ν : SABMap o.t o.t r) (ρ : X ⟶ X) (mu : SABMap t t ρ) (hj : j ≫ ρ = r ≫ j)
    (hφ : μ₀.φ ≫ mu.φ = ν.φ ≫ μ₀.φ) {a a' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    {k : Type} [Field k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x)
    (hfib : pullback.fst t.G.hom x ≫ mu.φ = pullback.fst t.G.hom x)
    (W : X.Opens) (σ : W.toScheme ⟶ t.G.left) (hxW : Set.range x ⊆ W) (hσ : σ ≫ t.G.hom = W.ι)
    (hσj : pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) : ∃ c, a' - a = l.A • c := by
  have pn : IsPullback μ₀.φ o.t.G.hom t.G.hom j := μ₀.cart.1
  have pm : IsPullback mu.φ t.G.hom t.G.hom ρ := mu.cart.1
  have sec : ∀ y : 𝟙_ (Over U) ⟶ o.t.G, y.left ≫ o.t.G.hom = 𝟙 U := fun y => Over.w y
  have ext : ∀ {Z : Scheme.{0}} (w : Z ⟶ W.toScheme) (u : Z ⟶ U), w ≫ W.ι = u ≫ j →
      w ≫ σ = u ≫ (o.etaA a).left ≫ μ₀.φ := by
    intro Z w u h
    have := pullback.lift w u h ≫= hσj
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  let T := pullback W.ι (W.ι ≫ ρ)
  let p₁ : T ⟶ W.toScheme := pullback.fst _ _
  let p₂ : T ⟶ W.toScheme := pullback.snd _ _
  have hp : p₁ ≫ W.ι = p₂ ≫ W.ι ≫ ρ := pullback.condition
  have : IsOpenImmersion p₂ := inferInstanceAs (IsOpenImmersion (pullback.snd W.ι (W.ι ≫ ρ)))
  let i : T ⟶ X := p₂ ≫ W.ι
  have : IsReduced T := isReduced_of_isOpenImmersion i
  have w₂ : (p₁ ≫ σ) ≫ t.G.hom = i ≫ ρ := by rw [Category.assoc, hσ, hp, Category.assoc]
  let σ₁ : T ⟶ t.G.left := p₂ ≫ σ
  let σ₂ : T ⟶ t.G.left := pm.lift (p₁ ≫ σ) i w₂
  have s₁ : σ₁ ≫ t.G.hom = i := by rw [Category.assoc, hσ]
  have s₂ : σ₂ ≫ t.G.hom = i := pm.lift_snd _ _ _
  have s₃ : σ₂ ≫ mu.φ = p₁ ≫ σ := pm.lift_fst _ _ _
  let x₀ : Sp k ⟶ W.toScheme := IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι])
  have hx₀ : x₀ ≫ W.ι = x := IsOpenImmersion.lift_fac _ _ _
  let xT : Sp k ⟶ T := pullback.lift x₀ x₀ (by rw [← Category.assoc, hx₀, hx])
  have x₁ : xT ≫ p₁ = x₀ := pullback.lift_fst _ _ _
  have x₂ : xT ≫ p₂ = x₀ := pullback.lift_snd _ _ _
  have hxT : xT ≫ σ₁ = xT ≫ σ₂ := by
    have w : (xT ≫ σ₂) ≫ t.G.hom = 𝟙 _ ≫ x := by
      rw [Category.assoc, s₂, ← Category.assoc, x₂, hx₀, Category.id_comp]
    have h := pullback.lift (xT ≫ σ₂) (𝟙 _) w ≫= hfib
    rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, s₃, ← Category.assoc, x₁] at h
    rw [← h, ← Category.assoc, x₂]
  let q₁ := pullback.fst i j
  let q₂ := pullback.snd i j
  have hq : q₁ ≫ i = q₂ ≫ j := pullback.condition
  have : IsDominant q₁ := isDominant_pullback_fst_of_isOpenMap j i i.isOpenEmbedding.isOpenMap
  have v₁ : q₁ ≫ σ₁ = q₂ ≫ (o.etaA a).left ≫ μ₀.φ := by
    rw [← Category.assoc]
    exact ext _ _ (by rw [Category.assoc]; exact hq)
  have v₂ : q₁ ≫ σ₂ = q₂ ≫ (o.etaA a').left ≫ μ₀.φ := by
    refine pm.hom_ext ?_ ?_
    · rw [Category.assoc, s₃, Category.assoc, Category.assoc, hφ, reassoc_of% ha, ← Category.assoc,
        ← Category.assoc q₂ r]
      refine ext _ _ ?_
      rw [Category.assoc, hp, Category.assoc, ← hj, ← Category.assoc q₂, ← hq, Category.assoc, Category.assoc]
    · rw [Category.assoc, s₂, hq, Category.assoc, Category.assoc, pn.w, ← Category.assoc (o.etaA a').left, sec]
      exact congrArg (q₂ ≫ ·) (Category.id_comp j).symm
  have tor : ∀ y : D.La, (o.etaA y).left ≫ μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left =
      (1 : 𝟙_ (Over U) ⟶ o.t.G).left ≫ μ₀.φ := by
    intro y
    have h : μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left = (o.t.act.act (l.A : 𝓞 E)).left ≫ μ₀.φ := (μ₀.act _).symm
    rw [h, ← Category.assoc, ← Over.comp_left, act_natCast, MonObj.comp_pow, Category.comp_id,
      ← LiftAut.etaA_nsmul, o.etaA_ker]
  have := t.semi.separated
  have := t.semi.smooth
  have : Etale (t.act.act (l.A : 𝓞 E)).left := by
    rw [act_natCast]
    exact GrpTangent.etale_id_pow t.G hN
  have hmul : σ₁ ≫ (t.act.act (l.A : 𝓞 E)).left = σ₂ ≫ (t.act.act (l.A : 𝓞 E)).left := by
    refine ext_of_isDominant_of_isSeparated t.G.hom ?_ q₁ ?_
    · rw [Category.assoc σ₁, Category.assoc σ₂, Over.w, s₁, s₂]
    · rw [reassoc_of% v₁, reassoc_of% v₂, tor, tor]
  have := isOpenImmersion_equalizer_ι_of_unramified _ hmul
  let e := equalizer.ι σ₁ σ₂
  have he : e ≫ σ₁ = e ≫ σ₂ := equalizer.condition _ _
  have : IsDominant (pullback.fst e q₁) := isDominant_pullback_fst_of_isOpenMap q₁ e e.isOpenEmbedding.isOpenMap
  have : Nonempty ↑(equalizer σ₁ σ₂) := ⟨equalizer.lift xT hxT (⊥ : PrimeSpectrum k)⟩
  have : Nonempty ↑(pullback e q₁) := (pullback.fst e q₁).denseRange.nonempty
  obtain ⟨K, _, _, ⟨y⟩⟩ := exists_geomPoint (pullback e q₁)
  refine modN_of_point_eq o (y ≫ pullback.snd e q₁ ≫ q₂) (pn.hom_ext ?_ ?_)
  · simp only [Category.assoc]
    rw [← v₁, ← v₂, ← pullback.condition_assoc, ← pullback.condition_assoc, he]
  · simp only [Category.assoc]
    rw [sec, sec]

theorem exists_sabMap_iterate (Xo : Moduli D l) (r : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r)
    (hr : r ≫ Xo.s = Xo.s) (h : ∀ x, (Xo.univ.eta x).left ≫ ν.φ = r ≫ (Xo.univ.eta x).left) (g : D.La → D.La)
    (hg : ∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r ≫ (Xo.univ.etaA x).left) (n : ℕ) :
    ∃ (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f), f = (fun f : Xo.X ⟶ Xo.X => f ≫ r)^[n] (𝟙 _) ∧
      f ≫ Xo.s = Xo.s ∧ (∀ x, (Xo.univ.eta x).left ≫ m.φ = f ≫ (Xo.univ.eta x).left) ∧
      ∀ x, (Xo.univ.etaA (g^[n] x)).left ≫ m.φ = f ≫ (Xo.univ.etaA x).left := by
  induction n with
  | zero =>
    obtain ⟨m, hm⟩ := ObjMaps.exists_sab_id Xo.univ.t
    exact ⟨𝟙 _, m, rfl, Category.id_comp _, fun _ => by rw [hm, Category.comp_id, Category.id_comp],
      fun _ => by rw [hm, Category.comp_id, Category.id_comp]; rfl⟩
  | succ n ih =>
    obtain ⟨f, m, hf, hs, h₁, h₂⟩ := ih
    obtain ⟨m', hm⟩ := ObjMaps.exists_sab_comp ν m
    refine ⟨f ≫ r, m', by rw [Function.iterate_succ_apply', ← hf], by rw [Category.assoc, hr, hs], fun x => ?_,
      fun x => ?_⟩
    · rw [hm, reassoc_of% (h₁ x), h, Category.assoc]
    · rw [hm, Function.iterate_succ_apply, reassoc_of% (h₂ (g x)), hg, Category.assoc]

theorem iterate_eq_id_of_fixes_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  intro h₁ h₂ h₃ E _ _ _ H D l Xo S β C r ν ρ mu hinc hS ⟨e, he⟩ hj hφ hr hη g hg k _ _ x hx hfib
  obtain ⟨⟨_, hded⟩, -, hfrac⟩ := (BaseRing.isDedFrac_RZ E H l S e hS he).2.2 β hinc
  letI := β.toAlgebra
  obtain ⟨hnoeth, -, -, hpre, hflat, hdom, hqc⟩ := genericPart_dense_proOpen (RZ H S l.A) (KA l) C.X Xo.X C.s C.jQ
    C.flat C.proj C.jQ_open C.jQ_dense
  have hd : IsDominant C.j := hdom
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  have hN : IsUnit (l.A : Γ(C.X, ⊤)) := by
    have := (hAu.map (Scheme.ΓSpecIso (CommRingCat.of (RZ H S l.A))).inv.hom).map C.s.appTop.hom
    rwa [map_natCast, map_natCast] at this
  have : Nonempty C.X := ⟨x (⊥ : PrimeSpectrum k)⟩
  have : Nonempty Xo.X := C.j.denseRange.nonempty
  have hmod := iterate_modN l.A D.EF _ g.toAddMonoidHom
    (fun v w => isometry_modN Xo.univ r.hom ν hr (hg v) (hg w))
    (fun v ⟨W, σ, hW, hσ, hσj⟩ =>
      modN_of_extends C.j Xo.univ C.t C.m hN r.hom ν ρ.hom mu hj hφ (hg v) x hx hfib W σ hW hσ hσj)
    (GlobalTheory.T.levelLabel_extends_of_orthogonal_to_extended h₁ h₂ h₃ E H D l (KA l) (baseKA l) C.X Xo.X C.j Xo.s Xo.univ C.t C.m C.normal hpre hflat hdom hqc
      hN k x)
  obtain ⟨f, m, hf, hs, e₁, e₂⟩ := exists_sabMap_iterate Xo r.hom ν hr hη g.toAddMonoidHom hg l.A
  rw [← hf]
  refine LiftAut.eq_id Xo f m hs e₁ fun a => ?_
  rw [← e₂, LiftAut.etaA_congr Xo.univ (hmod a)]

end GlobalTheory.StabTame
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  atlas_forward_decl GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Top.exists_cpt_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  intro E _ _ _ H D Xo n N T l h S e β b hS _ hN hβ hb
  subst h
  obtain ⟨⟨_, _⟩, _, hfr⟩ := (GlobalTheory.BaseRing.isDedFrac_RZ E H l S e hS hN).2.2 β hβ
  let _ := β.toAlgebra
  obtain ⟨W, f₀, hW₀, hfin, -, fa, fs⟩ := T.fin l rfl (β.comp b) (fun x => (hβ (b x)).trans (hb x))
  have hsm := (Xo l).smooth
  have hnor : Geo.Tor.IsNormalScheme (Xo l).X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let s₁ := pullback.snd T.s (spMap b)
  have hp : IsPullback (pullback.fst s₁ (spMap β) ≫ pullback.fst T.s (spMap b)) (pullback.snd s₁ (spMap β)) T.s
      (spMap (β.comp b)) := by
    rw [spMap_comp]
    exact (IsPullback.of_hasPullback s₁ (spMap β)).paste_horiz (IsPullback.of_hasPullback T.s (spMap b))
  let g := W.ι ≫ hp.isoPullback.inv
  have g₁ : (g ≫ pullback.fst _ _) ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, hp.isoPullback_inv_fst]
  have g₂ : g ≫ pullback.snd _ _ = W.ι ≫ pullback.snd _ _ := by
    rw [Category.assoc, hp.isoPullback_inv_snd]
  have hW : (f₀ ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = f₀ ≫ g := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open _ (KA l) _ (Xo l).X s₁ (Xo l).s (f₀ ≫ g ≫ pullback.fst _ _) g.opensRange (f₀ ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b T.proj) hnor inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans (Category.assoc _ _ _))
      (by
        rw [← Category.assoc]
        exact (congrArg (· ≫ _) hW).trans ((Category.assoc _ _ _).trans ((congrArg (f₀ ≫ ·) g₂).trans fs)))
  obtain ⟨_, _, _, _, _, mu, -⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst T.s (spMap b)) T.t
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b) = T.a l rfl := by
    rw [← fa, ← g₁, ← Category.assoc f₀, ← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap (Xo l).univ.t T.t
      ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b)), n'.φ = (T.m l rfl).φ := by
    rw [hj]; exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) ∈ abLocus T.t.G := by
    intro p
    have e : pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) =
        pullback.fst T.s (spMap (β.comp b)) (hp.isoPullback.hom p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp.isoPullback_hom_fst]
    rw [e]
    change p ∈ Set.range g ↔ hp.isoPullback.hom p ∈ pullback.fst T.s (spMap (β.comp b)) ⁻¹' abLocus T.t.G
    rw [← hW₀]
    constructor
    · rintro ⟨z, rfl⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact z.2
    · intro hz
      refine ⟨⟨_, hz⟩, ?_⟩
      refine (Scheme.Hom.comp_apply _ _ _).trans ?_
      change hp.isoPullback.inv (hp.isoPullback.hom p) = p
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩, π ≫ pullback.fst _ _, ?_, mu, ?_, hj,
    hm.symm.trans hn', ?_⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne T.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β) ⟶ pullback s₁ (spMap β) :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β) (w y) = π (pullback.fst (π ≫ s₁) (spMap β) y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst T.s (spMap b) z ∈ abLocus T.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _
  · have P₁ := IsPullback.of_hasPullback T.t.G.hom (pullback.fst T.s (spMap b))
    have Q := GlobalTheory.isQProjOver_of_isPullback (P₁.paste_vert (IsPullback.of_hasPullback T.s (spMap b))) T.qproj
    have P₀ := IsPullback.of_hasPullback T.t.G.hom (π ≫ pullback.fst T.s (spMap b))
    let ψ := P₁.lift (pullback.fst T.t.G.hom (π ≫ pullback.fst T.s (spMap b))) (pullback.snd _ _ ≫ π)
      (by rw [Category.assoc]; exact P₀.w)
    have ψ₁ : ψ ≫ _ = _ := P₁.lift_fst _ _ _
    have ψ₂ : ψ ≫ _ = _ := P₁.lift_snd _ _ _
    have P₂ : IsPullback ψ (pullback.snd T.t.G.hom (π ≫ pullback.fst T.s (spMap b)))
        (pullback.snd T.t.G.hom (pullback.fst T.s (spMap b))) π :=
      IsPullback.of_right (by rw [ψ₁]; exact P₀) ψ₂ P₁
    have : IsFinite ψ := MorphismProperty.of_isPullback (P := @IsFinite) P₂.flip hπ
    have R := GlobalTheory.isQProjOver_comp_of_isFinite ψ Q
    rw [← Category.assoc, ψ₂, Category.assoc] at R
    exact R

end GlobalTheory.Models
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactModel_above_fullLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  atlas_forward_decl GlobalTheory.Models.Top.exists_cpt_above
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.BaseModelEx

theorem natCast_ne_zero_of_pt {R k : Type} [CommRing R] [Field k] (y : Sp k ⟶ Sp R) {S : ℕ} (h : IsUnit (S : R)) :
    (S : k) ≠ 0 := by
  have := h.map (Spec.preimage y).hom
  rw [map_natCast] at this
  exact this.ne_zero

theorem natCast_notMem {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (f : X ⟶ Sp R) (g : X ⟶ Sp R')
    {S : ℕ} (h : IsUnit (S : R')) (x : X) : (S : R) ∉ (f x).asIdeal := by
  have h1 : (S : X.residueField x) ≠ 0 := natCast_ne_zero_of_pt (X.fromSpecResidueField x ≫ g) h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  have h2 : f x = (Spec.map φ) (IsLocalRing.closedPoint _) := by
    rw [hφ]
    exact (congrArg f (Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint _))).symm
  rw [h2]
  intro hS
  have h3 : φ.hom (S : R) ∈ IsLocalRing.maximalIdeal (X.residueField x) := hS
  rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero] at h3
  exact h3 h1

theorem isUnit_RZ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S : ℕ} (A : ℕ) (hS : 0 < S) :
    IsUnit (S : RZ H S A) := by
  refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩ (Subtype.ext ?_)
  have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  simp [this]

theorem exists_restrict {Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (s : Z ⟶ Sp R) (b : R →+* R') {S : ℕ}
    [IsOpenImmersion (spMap b)] (hS : IsUnit (S : R'))
    (hr : ∀ x : Sp R, x ∈ Set.range (spMap b) ↔ (S : R) ∉ x.asIdeal) (ρ : Z ⟶ Z) :
    ∃ ρ' : pullback s (spMap b) ⟶ pullback s (spMap b), ρ' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ρ := by
  refine ⟨IsOpenImmersion.lift (pullback.fst s (spMap b)) (pullback.fst _ _ ≫ ρ) ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Pullback.range_fst]
  have := natCast_notMem (pullback.fst s (spMap b) ≫ ρ ≫ s) (pullback.snd s (spMap b)) hS w
  rw [Set.mem_preimage, hr]
  simpa using this

theorem pow_hom_eq_iterate {X : Scheme.{0}} (r : Aut X) (m : ℕ) :
    (r ^ m).hom = (fun f : X ⟶ X => f ≫ r.hom)^[m] (𝟙 _) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ← ih, pow_succ']; rfl

theorem card_stab_ne_zero {X Y : Scheme.{0}} {Γ : Type} [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (x : Y ⟶ X) {n J : ℕ}
    (hn : n.Prime) (h : ∀ g, x ≫ (ρ g).hom = x → g ^ n ^ J = 1) {k : Type} [Field k] (hk : (n : k) ≠ 0) :
    (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0 := by
  let P : Subgroup Γ :=
    { carrier := {g | x ≫ (ρ g).hom = x}
      one_mem' := by
        show x ≫ (ρ 1).hom = x
        rw [map_one]; exact Category.comp_id x
      mul_mem' := by
        intro a b ha hb
        show x ≫ (ρ (a * b)).hom = x
        rw [map_mul]
        show x ≫ (ρ b).hom ≫ (ρ a).hom = x
        rw [← Category.assoc, show x ≫ (ρ b).hom = x from hb]; exact ha
      inv_mem' := by
        intro a ha
        show x ≫ (ρ a⁻¹).hom = x
        rw [map_inv]
        show x ≫ (ρ a).inv = x
        exact (Iso.comp_inv_eq (ρ a : X ≅ X)).mpr (show x ≫ (ρ a).hom = x from ha).symm }
  haveI : Fact n.Prime := ⟨hn⟩
  have hP : IsPGroup n P := fun g => ⟨J, Subtype.ext (h g.1 g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have : Nat.card {g // x ≫ (ρ g).hom = x} = n ^ m := hm
  rw [this, Nat.cast_pow]
  exact pow_ne_zero _ hk

theorem exists_baseModel : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN1 n J T l₀ hn hJ hA
  have hnp : n.Prime := hn.1
  have hM : 0 < l₀.M := by have := l₀.three_le; omega
  have hS : 0 < n * l₀.M := Nat.mul_pos hnp.pos hM
  have hN : 0 < n ^ J := pow_pos hnp.pos _
  have hdiv : n ^ J ∣ (n * l₀.M) ^ J := pow_dvd_pow_of_dvd (dvd_mul_right _ _) _
  let l₁ : Level H := { l₀ with A := n ^ J, A_pos := hN }
  have h₁ : l₁.A = n ^ J := rfl
  have R₀ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₀ (n * l₀.M) 0 hS (by simp [hA])
  rw [hA] at R₀
  obtain ⟨⟨β, hβ⟩, ft₀, ded₀⟩ := R₀
  obtain ⟨⟨β₁, hβ₁⟩, ft₁, ded₁⟩ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₁ (n * l₀.M) J hS hdiv
  obtain ⟨⟨b, hb⟩, hb2⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H (n * l₀.M) (n * l₀.M) 1 (n ^ J) J hS hN dvd_rfl (one_dvd _)
  obtain ⟨bfin, -, -⟩ := (hb2 b hb).1 rfl hdiv
  obtain ⟨⟨b', hb'⟩, hb2'⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H n (n * l₀.M) (n ^ J) (n ^ J) J hS hN (dvd_mul_right _ _) dvd_rfl
  obtain ⟨bop, brange⟩ := (hb2' b' hb').2 rfl
  obtain ⟨C₁, q, hq, qm, qfin, qj, qφ, qp⟩ := GlobalTheory.T.exists_compactModel_above_fullLevel E H D Xo n (n ^ J) T l₁ h₁ (n * l₀.M) J β₁ b' hS
    (dvd_mul_right _ _) hdiv hβ₁ hb'
  obtain ⟨k, r, ν, hr, hk, lev, -, -, -, -, -, rsurj⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN1 l₀ l₁
    ⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩
  obtain ⟨Γ, _, _, ρ₀, τ₀, ν₀, inj, quot, hω⟩ := GlobalTheory.T.moduli_level_quotient_by_finite_group L1 L2 L3 E H D Xo hD hN1 l₀ l₁ r ν k hA rfl rfl hk hr lev
  have hU : IsUnit ((n * l₀.M : ℕ) : RZ H (n * l₀.M) (n ^ J)) := isUnit_RZ H _ hS
  obtain ⟨ρ, τ, mu, hact⟩ := GlobalTheory.exists_action_model hext E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ C₁ _
    (pullback.lift q C₁.s hq) Γ ρ₀ τ₀ ν₀ (ded₁ β₁ hβ₁) ft₁ (Xo l₁).univ.proper inferInstance (fun g => (hω g).1) (by
      intro ω
      obtain ⟨h1, -, -, g, σ, h4, h5, h6⟩ := hω ω
      obtain ⟨ρZ, hρZ⟩ := T.sym l₁ h₁ (ρ₀ ω) (ν₀ ω) g σ h4 h5 (by rw [h1]; exact h6)
      obtain ⟨ρ', hρ'⟩ := exists_restrict T.s b' hU brange ρZ.hom
      refine ⟨ρ', ?_⟩
      rw [← cancel_mono (pullback.fst T.s (spMap b'))]
      simp only [Category.assoc, hρ', pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, qj, hρZ])
  have hover : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).hom = x →
      (ρ₀ ω).hom ≫ (Xo l₁).s = (Xo l₁).s := by
    intro κ _ x ω hx
    obtain ⟨-, -, -, g, σ, h4, h5, -⟩ := hω ω
    have := GlobalTheory.galoisPart_eq_refl_of_fixes_point E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω) (ρ ω) σ hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 h4 h5 κ x hx
    subst this
    rw [h5]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  have hφ : ∀ ω, C₁.m.φ ≫ (mu ω).φ = (ν₀ ω).φ ≫ C₁.m.φ := fun ω => by
    rw [(hact ω).1, (hω ω).1]; exact (hact ω).2.2
  have htriv : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).hom = x →
      pullback.fst C₁.t.G.hom x ≫ (mu ω).φ = pullback.fst C₁.t.G.hom x := by
    intro κ _ _ x ω hx
    exact GlobalTheory.T.finiteOrderAutomorphism_fixing_level_trivial_on_fixedFibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω) (ν₀ ω) (ρ ω) (mu ω) hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 (hφ ω) (dvd_mul_left _ _) (hover κ x ω hx) (by rw [(hω ω).1]; exact (hω ω).2.2.1)
      ⟨τ ω, Nat.card Γ, Nat.card_pos, by rw [← map_pow, pow_card_eq_one', map_one], (hact ω).1.symm⟩ κ x hx
  have hcard : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : κ) ≠ 0 := by
    intro κ _ _ x
    refine card_stab_ne_zero ρ x (J := J) hnp (fun ω hx => ?_) ?_
    · obtain ⟨h1, -, h3, g, σ, -, -, h6⟩ := hω ω
      have := GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω) (ν₀ ω) (ρ ω) (mu ω) hβ₁ hS ⟨J, hdiv⟩
        (hact ω).2.1 (hφ ω) (hover κ x ω hx) (by rw [h1]; exact h3) g (by rw [h1]; exact h6) κ x hx (htriv κ x ω hx)
      apply inj
      rw [map_pow, map_one]
      exact Iso.ext ((pow_hom_eq_iterate _ _).trans this)
    · have := natCast_ne_zero_of_pt (x ≫ C₁.s) hU
      rw [Nat.cast_mul] at this
      exact left_ne_zero_of_mul this
  have good₁ : Good C₁.t := good_pullback L3.gtBaseChange E H _ _ T.t C₁.t q qm T.good
  have push := GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D l₁ _ _ _ (baseKA l₁) _ (Xo l₁).s (Xo l₁).univ (Xo l₁).s β₁ C₁
    (ded₁ β₁ hβ₁) good₁.2.2
  have hcomm : β₁.comp b = k.comp β := by
    ext x
    exact (hβ₁ (b x)).trans ((hb x).trans ((hβ x).symm.trans (hk (β x)).symm))
  obtain ⟨C, good, ⟨above⟩⟩ := GlobalTheory.T.exists_quotient_model_by_tame_finite_group E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ _ _ _ (Xo l₀).s (Xo l₀).univ.t β Γ C₁
    b k r ν ρ₀ τ₀ ρ τ mu (ded₁ β₁ hβ₁) (ded₀ β hβ) hcomm bfin hr quot (Xo l₁).univ.proper
    (fun g => ⟨(hact g).1, (hact g).2.1, (hact g).2.2, (hω g).2.1⟩) qp hcard
    (fun κ _ _ x g hx => by rw [← (hact g).1]; exact htriv κ x g hx) good₁ push
  have hcop : (n ^ J).Coprime l₁.M := ((GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 n hn l₁).pow_left J
  exact ⟨⟨hA, β, hβ, C, good,
    GlobalTheory.T.levelChange_extends_base_model hext L1 L2 L3 E H D Xo n (n ^ J) T hD l₀ l₁ h₁ _ _ β β₁ C C₁ b r ν above b' q hq (ded₀ β hβ)
      (ded₁ β₁ hβ₁) ft₀ bfin qfin qj hA rfl rfl hcop lev rsurj ⟨k, hk, hr, hcomm⟩,
    l₁, rfl, rfl, h₁, β₁, hβ₁, C₁, b, hb, r, ν, lev, rsurj, above, b', hb', q, hq, qfin, qm, qj, qφ⟩⟩

end GlobalTheory.BaseModelEx

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_model_semiAbelian : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  atlas_forward_decl GlobalTheory.BaseModelEx.exists_baseModel
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LocalModelExists

theorem exists_model_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (b : RZ H (n * l₀.M) 1 →+* O), 0 < n → l₀.Dvd l → IsDedFrac β → IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b → ∃ Y : Model (Xo l) c β, Raises B Y := by
  intro L1 L2 L3 E _ _ _ H D Xo n N T hN l₀ l B c O _ β b hn hd hβ hb
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _ (Xo l).s
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l).univ
  obtain ⟨k, r, ν, hr, hk, hlev, hfin, -, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L1 L2 L3 E H D Xo hN l₀ l c o m0 hd
  have hpos : 0 < n * l₀.M := Nat.mul_pos hn (by have := l₀.three_le; omega)
  have hB : IsDedFrac B.β := by
    have aux : ∀ a : ℕ, l₀.A = a → a = 1 → ∀ β₀ : RZ H (n * l₀.M) a →+* KA l₀,
        IsInc (RZ H (n * l₀.M) a).subtype (KA l₀).val.toRingHom β₀ → IsDedFrac β₀ := by
      intro a ha h1
      subst ha
      exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l₀ (n * l₀.M) 0 hpos (by simp [h1])).2.2
    exact aux 1 B.A_one rfl B.β B.β_inc
  have hcomp : β.comp b = k.comp B.β := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hsm : Smooth (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ (Xo l₀).s (Xo l₀).univ.t B.β _ _ _
    (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) o.t β B.C b k r hr ν hB hβ hcomp
    hnorm hfin
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    b, r, ν, hb, hlev, hC⟩

end GlobalTheory.LocalModelExists
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.SystemAmple

theorem exists_system_ampFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  intro hx h1 h2 h3 htop E _ _ _ H D Xo hpq hN
  classical
  obtain ⟨⟨n₀, n₁, a₀, a₁, hne⟩, -⟩ := GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level E H
  let n : Bool → ℕ := fun i => cond i n₁ n₀
  have aux : ∀ i, AuxiliaryInertOddPrime H (n i) := fun i => by cases i <;> assumption
  choose J k T hJ hamp using fun i => htop E H D hpq Xo (n i) (aux i)
  let B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀ := fun i l₀ h =>
    (GlobalTheory.T.exists_base_model_semiAbelian hx h1 h2 h3 E H D Xo hpq hN (n i) (J i) (T i) l₀ (aux i) (hJ i) h).some
  let ch : ℕ → Bool := fun p => decide (n₀ = p)
  have ch_ne : ∀ p, n (ch p) ≠ p := by
    intro p
    by_cases h : n₀ = p
    · have : ch p = true := by simp [ch, h]
      rw [this]
      exact fun h' => hne (h.trans h'.symm)
    · have : ch p = false := by simp [ch, h]
      rw [this]
      exact h
  have key : ∀ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (i : Idx H p),
      ∃ Y : Model (Xo i.l) i.c (i.c.V W).subtype, ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
        Raises (B (ch p) l₀ h.1) Y := by
    intro p W hp hW i
    obtain ⟨hex, hsp, -⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
    obtain ⟨l₀, h⟩ := hex i.l i.good
    obtain ⟨hdvd, hcop, -⟩ := hsp i.l l₀ h
    obtain ⟨hded, -, hb⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
    have hnp : (n (ch p)).Coprime p := (Nat.coprime_primes (aux _).1 hp).2 (ch_ne p)
    have hz : zeta 1 ∈ i.c.F := by
      have : zeta 1 = 1 := by simp [zeta]
      rw [this]; exact one_mem _
    obtain ⟨b, hbi⟩ := hb (n (ch p) * l₀.M) 1 (Nat.Coprime.mul_left hnp hcop) one_pos hz
    obtain ⟨Y, hY⟩ := GlobalTheory.LocalModelExists.exists_model_raises h1 h2 h3 E H D Xo _ _ (T (ch p)) hN l₀ i.l
      (B (ch p) l₀ h.1) i.c _ (i.c.V W).subtype b (aux _).1.pos hdvd hded hbi
    exact ⟨Y, l₀, h, hY⟩
  choose Y hY using key
  exact ⟨⟨n, J, aux, hJ, T, B, ch, ch_ne, Y, hY⟩, fun i => ⟨k i, hamp i⟩⟩

end GlobalTheory.SystemAmple
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  atlas_forward_decl GlobalTheory.SystemAmple.exists_system_ampFrames
end
