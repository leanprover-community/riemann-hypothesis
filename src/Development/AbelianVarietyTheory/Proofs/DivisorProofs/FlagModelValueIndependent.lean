import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackKernelOfKernelPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjectsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceFstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSndStatement

section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem isReduced_of_pReg_of_factor (p : ℕ) {Y₀ Y : Scheme.{0}} [IsReduced Y₀] (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0)
    (hfac : ∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) :
    IsReduced Y := by

  have haff : ∀ (V : Y.Opens), IsAffineOpen V → ∀ g : Γ(Y, V), IsNilpotent g → g = 0 := by
    intro V hV g hg
    let q : Γ(Y, V) := (p : Γ(Y, V))
    let O := Y.basicOpen q
    let ρ : Γ(Y, V) →+* Γ(Y, O) := (Y.presheaf.map (homOfLE (Y.basicOpen_le q)).op).hom
    letI : Algebra Γ(Y, V) Γ(Y, O) := ρ.toAlgebra
    haveI : IsLocalization.Away q Γ(Y, O) := hV.isLocalization_basicOpen q
    have hu : IsUnit ((p : ℕ) : Γ(O.toScheme, ⊤)) := by
      have h1 : IsUnit (algebraMap Γ(Y, V) Γ(Y, O) q) := IsLocalization.Away.algebraMap_isUnit q
      rw [map_natCast] at h1
      have := h1.map (O.topIso.inv.hom)
      rwa [map_natCast] at this
    obtain ⟨f₀, hf₀⟩ := hfac O.toScheme O.ι hu
    haveI : IsOpenImmersion (f₀ ≫ i) := hf₀ ▸ inferInstance
    haveI : IsOpenImmersion f₀ := IsOpenImmersion.of_comp f₀ i
    haveI : IsReduced O.toScheme := isReduced_of_isOpenImmersion f₀
    haveI : _root_.IsReduced Γ(Y, O) :=
      isReduced_of_injective (O.topIso.inv.hom) (O.topIso.commRingCatIsoToRingEquiv.symm.injective)
    have h0 : algebraMap Γ(Y, V) Γ(Y, O) g = 0 := (hg.map (algebraMap Γ(Y, V) Γ(Y, O))).eq_zero
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers q) _ g).1 h0
    have hk' : q ^ k * g = 0 := hk
    clear hk h0
    induction k with
    | zero => simpa using hk'
    | succ k ih => exact ih (hp V _ (by rw [pow_succ', _root_.mul_assoc] at hk'; exact hk'))
  refine ⟨fun U => ⟨fun f hf => ?_⟩⟩
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · rw [map_zero]
    exact haff V.1.1 V.1.2 _ (hf.map _)

theorem isReduced_normalModel_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ gs hgs _ Y s i _ _ hfl hfac
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsReduced Y₀ := GlobalTheory.isReduced_of_smooth_of_isReduced (gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s)
  have hR : ∀ a : R, (p : R) * a = 0 → a = 0 := fun a ha =>
    (mul_eq_zero.1 ha).resolve_left (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  haveI := hfl
  exact isReduced_of_pReg_of_factor p i (fun U f hf => pReg_of_flat (p := p) (s ≫ M.s) hR U f hf) hfac

end GlobalTheory.UPel.HT.ES
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_normalModel_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  first | (exact @GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (exact GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (intros; apply GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_over_normal_quasi_projective_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  first | (exact @GlobalTheory.ExtendNormal.exists_extension) | (exact GlobalTheory.ExtendNormal.exists_extension) | (intros; apply GlobalTheory.ExtendNormal.exists_extension  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FiniteCoverProper

theorem isProper_of_lift_through_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  intro R _ _ X Y₀ Y τ s t i hτ hs hi hd ht h
  have hX : IsLocallyNoetherian X := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : LocallyOfFiniteType τ := by rw [← e]; infer_instance
    have : IsLocallyNoetherian (Sp R) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
    exact LocallyOfFiniteType.isLocallyNoetherian τ
  have hsep : IsSeparated τ := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : IsImmersion j := hj
    rw [← e]; infer_instance
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hq : IsQProjOver (t ≫ τ) := ht ▸ GlobalTheory.isQProjOver_comp_of_isFinite_general s hτ
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R Y X t τ hsep hq ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have hgen : genericPoints Y ⊆ Set.range i := GlobalTheory.genericPoints_subset_range_of_isDominant i
  have hr : Set.range x ⊆ Set.range i := hx.trans hgen
  have hx₀ : IsOpenImmersion.lift i x hr ≫ i = x := IsOpenImmersion.lift_fac i x hr
  obtain ⟨z, hz⟩ := h V K y (IsOpenImmersion.lift i x hr) (by rw [← Category.assoc, hx₀, hxy])
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z := by
    rw [← hx₀, Category.assoc]; exact hz.symm
  obtain ⟨⟨x', hx', -⟩⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z, commSq := ⟨hw⟩ }).exists_lift
  exact ⟨x', hx'⟩

end GlobalTheory.FiniteCoverProper
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  first | (exact @GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (exact GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (intros; apply GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FibreCrit

theorem exists_generization_mem {Y : Scheme.{0}} [IsLocallyNoetherian Y] {O : Set Y} (hO : IsOpen O)
    (hd : Dense O) (y : Y) : ∃ e0 : Y, e0 ⤳ y ∧ e0 ∈ O := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) trivial
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  obtain ⟨y', rfl⟩ : y ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hyU
  have hC := irreducibleComponent_mem_irreducibleComponents y'
  obtain ⟨o, ho, hne, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwO⟩ :=
    hd.inter_open_nonempty _ (U.ι.isOpenEmbedding.isOpenMap _ ho) (hne.image _)
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  exact ⟨U.ι hC.1.genericPoint, (hg.specializes mem_irreducibleComponent).map U.ι.continuous,
    ((hg.specializes (hoC hwo)).map U.ι.continuous).mem_open hO hwO⟩

theorem spMap_algebraMap_apply (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (p : Sp K) : spMap (algebraMap V K) p = (⊥ : PrimeSpectrum V) := by
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap V K) p.asIdeal = ⊥
  rw [(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)

end GlobalTheory.FibreCrit

namespace GlobalTheory.FibreCrit

theorem finite_fibre_of_isFinite : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  intro X Y₀ Y s t i hs hi hd hY hfin z
  refine (s.finite_preimage (hfin z)).subset ?_
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨e0, he0y, he0i⟩ := exists_generization_mem i.isOpenEmbedding.isOpen_range i.denseRange y
  obtain ⟨V, _, _, _, g, hg0, hg1⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V)
      (_ : IsDiscreteValuationRing V) (g : Sp V ⟶ Y),
      g (⊥ : PrimeSpectrum V) ∈ Set.range i ∧ g (IsLocalRing.closedPoint V) = y := by
    by_cases he : e0 = y
    · subst he
      have hpt : ∀ q, (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0) q = e0 := fun q => by
        have h := Set.mem_range_self (f := Y.fromSpecResidueField e0)
          (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) q)
        rw [Scheme.range_fromSpecResidueField] at h
        rw [Scheme.Hom.comp_apply]
        exact h
      exact ⟨PowerSeries (Y.residueField e0), inferInstance, inferInstance, inferInstance,
        spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0, (hpt _).symm ▸ he0i, hpt _⟩
    · obtain ⟨O, hO, hV, -, f, hf0, hf1⟩ :=
        GlobalTheory.exists_complete_discreteValuationRing_of_specializes he0y he
      exact ⟨O, inferInstance, hO, hV, f, hf0 ▸ he0i, hf1⟩
  have hr : Set.range (spMap (algebraMap V (FractionRing V)) ≫ g) ⊆ Set.range i := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, spMap_algebraMap_apply V (FractionRing V) q]
    exact hg0
  refine ⟨V, FractionRing V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g ≫ s, g ≫ t, IsOpenImmersion.lift i _ hr, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (· ≫ s) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (congrArg (· ≫ t) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (Scheme.Hom.comp_apply g s _).trans (congrArg s hg1)
  · exact ((Scheme.Hom.comp_apply g t _).trans (congrArg t hg1)).trans hy

end GlobalTheory.FibreCrit
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  first | (exact @GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (exact GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (intros; apply GlobalTheory.FibreCrit.finite_fibre_of_isFinite  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.ValExt

theorem exists_ext_target : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ :=
  of_ext GlobalTheory.UPel.HT.ES.IsogDVR.exists_isPIsog_extend_dvr

end GlobalTheory.UPel.HT.ES.ValExt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_target_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
  first | (exact @GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (exact GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (intros; apply GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem exists_obj_extend_of_isPIsog : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  intro p _ D R _ b N _ _ c V K _ _ _ _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨-, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  have hcomm := o.ab.comm
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V K o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  exact exists_obj V K v _ rfl o₀' B φB hB hφB

end GlobalTheory.UPel.HT.ES.IsogDVR
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_extend_of_pIsogeny_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  first | (exact @GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog) | (exact GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog) | (intros; apply GlobalTheory.UPel.HT.ES.IsogDVR.exists_obj_extend_of_isPIsog  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ESValT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def scaleMap {S S' : Scheme.{0}} {s t : S ⟶ Sp R} {s' t' : S' ⟶ Sp R} {o : Obj b N s} {o₁ : Obj b N s'}
    {f : S' ⟶ S} (m : ObjMap o₁ o f) (e : ℕ) (h : s = t) (h' : s' = t') :
    ObjMap (ESDual.scale o₁ e h') (ESDual.scale o e h) f where
  φ := m.φ
  φ₂ := m.φ₂
  cart := m.cart
  sq := m.sq
  act := m.act
  pol := m.pol
  eta y := m.eta _

theorem extend_source : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ t₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ s₀ := by
  intro p _ D R _ _ _ _ b N hN hNp hpm r w j c _ _ _ _ _ M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst _ _ _ _ _ _ hψ _ V K _ _ _ _ _ _ y x hy
  set κ := spMap (algebraMap V K) with hκ
  obtain ⟨e, rfl⟩ := hψ.1
  obtain ⟨f', hf'⟩ := ESDual.exists_inv_exp (N := N) (by omega) hNp e
  obtain ⟨ψ', hψ'm, h₁, h₂⟩ := hψ.2.2.2.2.2
  haveI := hψ'm
  obtain ⟨hact, heta, ⟨hpol⟩⟩ := ESDual.dual_clauses hψ h₁ h₂
  have hrev : IsPIsog (p ^ e) (ESDual.scale o₀' f' rfl) o₀ ψ' := by
    refine ⟨⟨e, rfl⟩, hψ'm, hact, fun z => ?_, ⟨hpol⟩, ψ₀, hψ.2.1, h₂, h₁⟩
    show o₀.eta z = o₀'.eta (p ^ f' • z) ≫ ψ'
    rw [← heta, smul_smul, ← pow_add, ESDual.eta_congr o₀ hf' (pow_pos (Fact.out : p.Prime).pos _)]
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp K) (y ≫ M.s) κ oV
  have hb : κ ≫ y ≫ M.s = x ≫ s₀ ≫ M.s := by
    rw [← Category.assoc, hy, Category.assoc, ← hst]
  obtain ⟨o₁, ⟨m₁⟩⟩ : ∃ o₁ : Obj b N (κ ≫ y ≫ M.s), Nonempty (ObjMap o₁ o₀ x) := by
    rw [hb]; exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp K) (s₀ ≫ M.s) x o₀
  have mKU : ObjMap oK M.univ (x ≫ t₀) := hy ▸ ESDual.compMap mK mV
  obtain ⟨mK0, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ mKU mt₀
  obtain ⟨ψK, hψK, -⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N (p ^ e) Y₀ (Sp K) (s₀ ≫ M.s) (κ ≫ y ≫ M.s) x _ _
    (ESDual.scale oK f' rfl) o₁ (scaleMap mK0 f' rfl rfl) m₁ ψ' hrev
  obtain ⟨o'', ⟨m''⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_extend_of_pIsogeny_dvr p D R b N hN hNp (p ^ e) V K (y ≫ M.s) (ESDual.scale oV f' rfl)
    (ESDual.scale oK f' rfl) o₁ (scaleMap mK f' rfl rfl) ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o''
  refine ⟨z, ?_⟩
  obtain ⟨g, -, hg⟩ := M.rep (Sp K) (κ ≫ y ≫ M.s) o₁
  have e1 := hg (κ ≫ z) ⟨by rw [Category.assoc, hz], ⟨ESDual.compMap m'' mz⟩⟩
  have e2 := hg (x ≫ s₀) ⟨by rw [Category.assoc, hb], ⟨ESDual.compMap m₁ ms₀⟩⟩
  exact e1.trans e2.symm

end GlobalTheory.ESValT
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ t₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ s₀ := by
  first | (exact @GlobalTheory.ESValT.extend_source) | (exact GlobalTheory.ESValT.extend_source) | (intros; apply GlobalTheory.ESValT.extend_source <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ExtT

theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → IsDominant i → i ≫ s = s₀ → IsFinite s → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → Flat (s ≫ M.s) → IsLocallyNoetherian Y → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → ∃ t : Y ⟶ M.X, i ≫ t = t₀ ∧ t ≫ M.s = s ≫ M.s ∧ IsFinite t := by
  intro p _ D R _ _ _ _ b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs
    hes hft het hiso htj Y s i hio hid his hsf hnorm hflat hln hfac
  have hred : IsReduced Y := GlobalTheory.T.isReduced_normalModel_generic_correspondence p D R b N hpm M Y₀ s₀ gs hgs hes Y s i hio his hflat hfac
  have hval : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i →
      ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
    intro V K _ _ _ _ _ _ y x hy
    exact GlobalTheory.T.exists_dvr_extension_target_generic_correspondence p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K (y ≫ s) x (by rw [← Category.assoc, hy, Category.assoc, his])
  have hqf : ∀ y : Y, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ M.X)
      (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
    intro y
    refine (GlobalTheory.T.finite_points_closure_genericCorrespondence_fst p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj (s y)).subset ?_
    rintro z ⟨V, K, i1, i2, i3, i4, i5, i6, y', z', x, h1, h2, h3, h4⟩
    exact ⟨V, K, i1, i2, i3, i4, i5, i6, y' ≫ s, z', x, by rw [← Category.assoc, h1, Category.assoc, his], h2,
      by rw [← h3]; rfl, h4⟩
  obtain ⟨t, hit, htσ⟩ := GlobalTheory.T.extension_over_normal_quasi_projective_base R Y₀ Y M.X i (s ≫ M.s) M.s t₀ hio hid hln hred hnorm M.qproj
    (by rw [reassoc_of% his, hst]) hval hqf
  have hP : IsProper t := GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence R M.X Y₀ Y M.s s t i M.qproj hsf hio hid htσ (fun V K _ _ _ _ _ _ y x hy => by
    obtain ⟨z, hz⟩ := GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K y x (by rw [hy, hit])
    exact ⟨z, by rw [hz, his]⟩)
  have hC : ∀ z : M.X, {y : Y | t y = z}.Finite := GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first M.X Y₀ Y s t i hsf hio hid hln (fun z => by
    simpa only [his, hit] using GlobalTheory.T.finite_points_closure_genericCorrespondence_snd p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj z)
  haveI : LocallyQuasiFinite t := LocallyQuasiFinite.of_finite_preimage_singleton t hC
  exact ⟨t, hit, htσ, IsFinite.of_isProper_of_locallyQuasiFinite t⟩

end GlobalTheory.ExtT
end
end
