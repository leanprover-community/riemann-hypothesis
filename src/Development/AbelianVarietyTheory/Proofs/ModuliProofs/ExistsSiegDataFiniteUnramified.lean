import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_extension_over_dvr : Out.Laws → Out.Laws2 → ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s'), s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → ∃ t : TObj g k J b (spMap β), TMap t' t (spMap (algebraMap V K)) := by
  first | exact @GlobalTheory.ThetaExtend.exists_tObj_extension | exact GlobalTheory.ThetaExtend.exists_tObj_extension | (intros; apply GlobalTheory.ThetaExtend.exists_tObj_extension <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFromSiegel

theorem exists_cast {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S : Scheme.{0}} {s₁ s₂ : S ⟶ Sp o}
    (e : s₁ = s₂) (t : TObj g k J b s₁) :
    ∃ u : TObj g k J b s₂, ∀ (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (t' : TObj g k J b s') (f : S ⟶ S'),
      TMap t t' f → TMap u t' f := by
  subst e
  exact ⟨t, fun _ _ _ _ h => h⟩

theorem fromC_comp {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
    {s' : S' ⟶ Sp o} {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {t : TObj g k J b s} {t' : TObj g k J b s'}
    {f : S' ⟶ S} (hs : s' = f ≫ s) (h : TMap t' t f) {K : Type} [Field K] {x : Sp K ⟶ S'} (hx : FromC em C t' x) :
    FromC em C t (x ≫ f) := by
  obtain ⟨K₀, _, β, i, j, t₀, tx, tc, h1, h2, h3, h4, h5, h6⟩ := hx
  have e : x ≫ s' = (x ≫ f) ≫ s := by rw [hs, Category.assoc]
  obtain ⟨u, hu⟩ := exists_cast e tx
  exact ⟨K₀, _, β, i, j, t₀, u, tc, h1, e ▸ h2,
    hu _ _ _ _ (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S S' (Sp K) s s' _ t t' tx).2 f x h).1 h3), hu _ _ _ _ h4, h5, h6⟩

theorem dense_range_generic (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] :
    Dense (Set.range (spMap (algebraMap V K))) := by
  have h : DenseRange (PrimeSpectrum.comap (algebraMap V K)) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)]
    exact bot_le
  exact h

theorem exists_isPEL_extension : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (k : ℕ) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s') (τ' : SAB H (Sp K)), (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → ArBase em → s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → IsPEL D a bas ρ t' τ' → ∃ (t : TObj g k J b (spMap β)) (τ : SAB H (Sp V)), IsPEL D a bas ρ t τ ∧ TMap t' t (spMap (algebraMap V K)) := by
  intro hL hL2 hT E _ _ _ H D g J _ a w w' bas h1 hb hw hw' hcl bas' _ k o B _ _ b em ρ ζ V K _ _ _ _ _ _ _ β s₁ s' s₁'
    c c' t' τ' hk hρ hA hs hc hcc hS hP
  obtain ⟨N', rfl⟩ := hk
  obtain ⟨t, ht⟩ := GlobalTheory.T.siegel_extension_over_dvr hL hL2 g _ J D.La bas bas' o B b ζ V K β s₁ s' s₁' c c' t' hs hc hcc hS
  have hF := fromC_comp hs ht
    (GlobalTheory.T.pelObject_fibre_from_complex_charZero hL hL2 E H D g J a w w' bas h1 hb hw hw' hcl N' o b em ρ hρ hA _ s' t' τ' hP K (𝟙 _))
  rw [Category.id_comp] at hF
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_isPELTriple_of_dense_fibres hL hL2 hT E H D g J a bas w w' h1 hb hw hw' hcl _ o b em ρ (Sp V) (spMap β) t hρ hA.2.2
    ((dense_range_generic V K).mono fun p hp => ⟨K, _, _, hp, hF⟩)
  exact ⟨t, τ, hτ, ht⟩

end GlobalTheory.PELFromSiegel
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_datum_moduli_family : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (k : ℕ) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s') (τ' : SAB H (Sp K)), (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → ArBase em → s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → IsPEL D a bas ρ t' τ' → ∃ (t : TObj g k J b (spMap β)) (τ : SAB H (Sp V)), IsPEL D a bas ρ t τ ∧ TMap t' t (spMap (algebraMap V K)) := by
  atlas_forward_decl GlobalTheory.PELFromSiegel.exists_isPEL_extension
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ValuativeGeneric

theorem isProper_of_lift_generic_of_finiteType : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (X Y : Scheme.{0}) (f : X ⟶ Y) (sY : Y ⟶ Sp O), IsQProjOver (f ≫ sY) → IsSeparated sY → LocallyOfFiniteType sY → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro O _ _ X Y f sY hq hs hl h
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact isProper_of_lift_generic O X Y f sY hs hq
    fun V K _ _ _ _ _ _ _ x y hx hy => h V K x y hx hy

end GlobalTheory.ValuativeGeneric
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuative_lift_generic_point : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (X Y : Scheme.{0}) (f : X ⟶ Y) (sY : Y ⟶ Sp O), IsQProjOver (f ≫ sY) → IsSeparated sY → LocallyOfFiniteType sY → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  atlas_forward_decl GlobalTheory.ValuativeGeneric.isProper_of_lift_generic_of_finiteType
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_structure_pullback : ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s₁ : S ⟶ Sp B) (s' : S' ⟶ Sp o) (s₁' : S' ⟶ Sp B) (t : TObj g k J b s) (c : SiegPre g k ζ s₁) (t' : TObj g k J b s') (c' : SiegPre g k ζ s₁') (f : S' ⟶ S), TSieg bas bas' t c → TMap t' t f → (SiegPB c' c f ↔ TSieg bas bas' t' c') := by
  first | exact @GlobalTheory.ZM.siegPB_iff_tSieg | exact GlobalTheory.ZM.siegPB_iff_tSieg | (intros; apply GlobalTheory.ZM.siegPB_iff_tSieg <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegelMapProper

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem isQProjOver_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'} {X T : Scheme.{0}}
    {s : X ⟶ Sp R} {sT : T ⟶ Sp R'} {f : T ⟶ X} (h : IsPullback f sT s (spMap j)) (hs : IsQProjOver s) :
    IsQProjOver sT := by
  obtain ⟨N, i, h1, h2, h3⟩ := (GlobalTheory.isQProjOver_baseChange_and_finite_restrict R R' j X s).1 hs
  refine ⟨N, h.isoPullback.hom ≫ i, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, h3, h.isoPullback_hom_snd]

theorem injective_of_generic {O K : Type} [CommRing O] [IsDomain O] [Field K] {T : Scheme.{0}} (sT : T ⟶ Sp O)
    [Flat sT] (x : Sp K ⟶ T) (hx : Set.range x ⊆ genericPoints T) (δ : O →+* K) (h : x ≫ sT = spMap δ) :
    Function.Injective δ := by
  let pt : Sp K := (⊥ : PrimeSpectrum K)
  have hs : x pt ∈ genericPoints T := hx ⟨pt, rfl⟩
  obtain ⟨s', hs', e⟩ := Flat.generalizingMap sT (genericPoint_specializes (sT (x pt)))
  have h1 : closure {x pt} ⊆ closure ({s'} : Set T) := specializes_iff_closure_subset.mp hs'
  have h2 := hs.2 isIrreducible_singleton.closure h1
  have h3 : sT (x pt) = genericPoint (Sp O) := by
    rw [← e, (hs'.antisymm (specializes_iff_closure_subset.mpr h2)).eq]
  rw [← Scheme.Hom.comp_apply, h, genericPoint_eq_bot_of_affine] at h3
  rw [RingHom.injective_iff_ker_eq_bot]
  exact congrArg PrimeSpectrum.asIdeal h3

theorem isProper_toSiegel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → IsNoetherianRing O → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)) (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TMap tT t f → TSieg bas bas' tT c → u ≫ pullback.snd _ _ = sT → SiegPB c Ag.univ (u ≫ pullback.fst _ _) → IsProper u := by
  intro L1 L2 L3 E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl k o _ b em ρ _ _ hk hρ _ har X s t τ hrep hpel
    p Ag _ _ hS bas' hbas' O _ i z bb hi _ hbb hO T sT f hT tT c u htT hc hu hcu
  have : IsDomain O := hi.isDomain i
  have : CharZero O := i.charZero
  have hbbi : Function.Injective bb := fun x y e => har.2.2 (by rw [← hbb x, ← hbb y, e])
  have := hrep.flat
  have : Flat sT := MorphismProperty.of_isPullback (P := @Flat) hT inferInstance
  have := hS.1
  have := Ag.smooth
  have : Smooth Ag.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) Ag.s
  refine GlobalTheory.T.valuative_lift_generic_point O T _ u (pullback.snd Ag.s (spMap z)) (hu ▸ isQProjOver_of_isPullback hT hrep.qproj)
    inferInstance inferInstance ?_
  intro V K _ _ _ _ _ _ x y hx hxy
  obtain ⟨δ', hδ⟩ := Spec.map_surjective (y ≫ pullback.snd Ag.s (spMap z))
  obtain ⟨δ, rfl⟩ : ∃ δ : O →+* V, CommRingCat.ofHom δ = δ' := ⟨δ'.hom, rfl⟩
  change spMap δ = _ at hδ
  have hxs : x ≫ sT = spMap (algebraMap V K) ≫ spMap δ := by
    rw [← hu, ← Category.assoc, hxy, Category.assoc, hδ]
  have hinj : Function.Injective ((algebraMap V K).comp δ) :=
    injective_of_generic sT x hx _ (by rw [hxs, spMap_comp_spMap])
  have : CharZero K := charZero_of_injective_ringHom hinj
  have hδi : Function.Injective δ := Function.Injective.of_comp (f := algebraMap V K) hinj
  have hxf : (x ≫ f) ≫ s = spMap (algebraMap V K) ≫ spMap (δ.comp bb) := by
    rw [Category.assoc, hT.w, ← Category.assoc, hxs, Category.assoc, spMap_comp_spMap]
  have hid : spMap (RingHom.id (ZP p k)) = 𝟙 _ := Spec.map_id _

  have hV := GlobalTheory.T.siegelPre_pullback_principal_ringChange g k _ _ (zetaZP p k) (zetaZP p k) (RingHom.id _) _ _ Ag.s
    ((y ≫ pullback.fst _ _) ≫ Ag.s) (y ≫ pullback.fst Ag.s (spMap z)) rfl (by rw [hid, Category.comp_id])
  obtain ⟨cV, hcV⟩ := hV.1 Ag.univ
  have hpr : cV.Principal := hV.2.1 _ _ hcV Ag.princ

  obtain ⟨cK, hcK⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange g k _ _ (zetaZP p k) (zetaZP p k) (RingHom.id _) _ _ (sT ≫ spMap z)
    (x ≫ sT ≫ spMap z) x rfl (by rw [hid, Category.comp_id])).1 c
  obtain ⟨tK, htK⟩ := GlobalTheory.tObj_pull o g k J b _ _ (sT ≫ spMap bb) ((x ≫ f) ≫ s) x tT
    (by rw [Category.assoc, hT.w])
  have htKf : TMap tK t (x ≫ f) := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t tT tK).2 f x htT).1 htK
  obtain ⟨τK, hτK⟩ := GlobalTheory.exists_isPEL_of_tmap E H D g J a bas k o b ρ _ _ _ _ t tK τ (x ≫ f) rfl htKf hpel
  have hsK : TSieg bas bas' tK cK :=
    (GlobalTheory.T.siegel_structure_pullback g k J _ bas bas' o _ b _ _ _ _ _ _ _ tT c tK cK x hc htK).1 hcK
  have hcKV : SiegPB cK cV (spMap (algebraMap V K)) := by
    refine ((GlobalTheory.SiegelPullComp.id_comp_cancel g k _ _ _ _ _ _ _ _ _ _ _ _ Ag.univ cV cK _ _).2 hcV).2 ?_
    rw [← Category.assoc (spMap (algebraMap V K)), ← hxy, Category.assoc x u]
    exact ((GlobalTheory.SiegelPullComp.id_comp_cancel g k _ _ _ _ _ _ _ _ _ _ _ _ Ag.univ c cK _ _).2 hcu).1 hcK
  obtain ⟨tV, τV, hτV, htV⟩ := GlobalTheory.T.symplectic_datum_moduli_family L1 L2 L3 E H D g J a w w' bas hpq hbas hw hw' hcl bas' hbas' k o _ b em ρ _
    V K (δ.comp bb) _ _ _ cV cK tK τK hk hρ har hxf hpr hcKV hsK hτK
  obtain ⟨fV, hfV, hmV⟩ := hrep.rep V (δ.comp bb) tV τV (hδi.comp hbbi) hτV
  have he : spMap (algebraMap V K) ≫ fV = x ≫ f :=
    hrep.inj K _ _ _ tK (by rw [hxf, Category.assoc, hfV])
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t tV tK).2 fV _ hmV).1 htV) htKf
  refine ⟨hT.lift fV (spMap δ) (by rw [hfV, spMap_comp_spMap]), hT.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hT.lift_fst, he]
  · rw [Category.assoc, hT.lift_snd, hxs]

end GlobalTheory.SiegelMapProper
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_datum_torsion_level_ext : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → IsNoetherianRing O → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)) (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TMap tT t f → TSieg bas bas' tT c → u ≫ pullback.snd _ _ = sT → SiegPB c Ag.univ (u ≫ pullback.fst _ _) → IsProper u := by
  atlas_forward_decl GlobalTheory.SiegelMapProper.isProper_toSiegel
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_datum_torsion_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)) (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TMap tT t f → TSieg bas bas' tT c → u ≫ pullback.snd _ _ = sT → SiegPB c Ag.univ (u ≫ pullback.fst _ _) → FormallyUnramified u ∧ LocallyQuasiFinite u := by
  first | exact @GlobalTheory.SiegUnram.formallyUnramified_and_locallyQuasiFinite | exact GlobalTheory.SiegUnram.formallyUnramified_and_locallyQuasiFinite | (intros; apply GlobalTheory.SiegUnram.formallyUnramified_and_locallyQuasiFinite <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_basis_change : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (EF : La → La → ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La), (∀ x x' y, EF (x + x') y = EF x y + EF x' y) → (∀ x y y', EF x (y + y') = EF x y + EF x y') → (∀ i j, EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) → (∀ x y, EF (bas' x) (bas' y) = omegaStd x y) → ∀ (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp o) (s' : S ⟶ Sp B) (t : TObj g k J b s), 1 ≤ k → (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (β : o →+* K) (β' : B →+* K), x ≫ s = spMap β → x ≫ s' = spMap β' → β (b.ζ : o) = β' ζ) → ∃ c : SiegPre g k ζ s', c.Principal ∧ TSieg bas bas' t c := by
  first | exact @GlobalTheory.SiegelOfTheta.exists_siegPre | exact GlobalTheory.SiegelOfTheta.exists_siegPre | (intros; apply GlobalTheory.SiegelOfTheta.exists_siegPre <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegelClassify

theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem isReduced_pullback_localization {o O : Type} [CommRing o] [CommRing O] [Algebra o O] (M : Submonoid o)
    [IsLocalization M O] {X : Scheme.{0}} (s : X ⟶ Sp o) [IsReduced X] :
    IsReduced (pullback s (spMap (algebraMap o O))) := by
  have h1 : IsPreimmersion (spMap (algebraMap o O)) := IsPreimmersion.of_isLocalization M
  have h2 : Flat (spMap (algebraMap o O)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat O M)
  let π := pullback.fst s (spMap (algebraMap o O))
  have h3 : IsPreimmersion π := inferInstance
  have h4 : Flat π := inferInstance
  have : ∀ x, _root_.IsReduced ((pullback s (spMap (algebraMap o O))).presheaf.stalk x) := fun x => by
    have hs : Function.Surjective (π.stalkMap x) := π.stalkMap_surjective x
    have hf := Flat.stalkMap π x
    have hi : Function.Injective (π.stalkMap x) := by
      algebraize [(π.stalkMap x).hom]
      have : IsLocalHom (algebraMap (X.presheaf.stalk (π x)) ((pullback s (spMap (algebraMap o O))).presheaf.stalk x)) :=
        inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
      have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π x))
        (B := (pullback s (spMap (algebraMap o O))).presheaf.stalk x)
      exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (π x)) _
    exact isReduced_of_injective (RingEquiv.ofBijective (π.stalkMap x).hom ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk _

theorem dense_generic {B O : Type} [CommRing B] [CommRing O] [IsDomain O] (z : B →+* O) (hz : Function.Injective z)
    {T : Scheme.{0}} (sT : T ⟶ Sp O) [Flat sT] : Dense {x : T | ((sT ≫ spMap z) x).asIdeal = ⊥} := by
  intro x
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) ⤳ sT x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap sT hη
  refine closure_mono (Set.singleton_subset_iff.2 ?_) hx'.mem_closure
  change ((sT ≫ spMap z) x').asIdeal = ⊥
  rw [Scheme.Hom.comp_apply, e]
  change Ideal.comap z ⊥ = ⊥
  exact Ideal.comap_bot_of_injective z hz

theorem exists_localization (p k : ℕ) (hp : p.Prime) {o : Type} [CommRing o] [IsNoetherianRing o] (em : o →+* ℂ)
    (hem : Function.Injective em) (ζ : o) (hζ : em ζ = zeta k) :
    ∃ (M : Submonoid o) (i₀ : Localization M →+* ℂ) (z₀ : ZP p k →+* Localization M), Function.Injective i₀ ∧
      GlobalTheory.Models.IsInc (ZP p k).subtype i₀ z₀ ∧ GlobalTheory.Models.IsInc em i₀ (algebraMap o _) ∧
      ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i →
        GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb →
        ∃ ga : Localization M →+* O, ga.comp (algebraMap o _) = bb ∧ ga.comp z₀ = z := by
  let M : Submonoid o :=
    { carrier := {x | ∃ n : ℕ, n.Coprime p ∧ x = n}
      one_mem' := ⟨1, by simp, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
        exact ⟨n * m, Nat.Coprime.mul_left hn hm, by simp⟩ }
  have h0 : ∀ n : ℕ, n.Coprime p → (n : ℂ) ≠ 0 := fun n hn h => by
    have : n = 0 := by exact_mod_cast h
    subst this
    exact hp.one_lt.ne' (by simpa using hn)
  have hu : ∀ y : M, IsUnit (em y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using h0 n hn
  let i₀ : Localization M →+* ℂ := IsLocalization.lift hu
  have hi₀ : ∀ x, i₀ (algebraMap o _ x) = em x := IsLocalization.lift_eq hu
  have hinj : Function.Injective i₀ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    exact ⟨fun h => by rw [← hi₀, ← hi₀, h], fun h => by rw [hem h]⟩
  have hle : ZP p k ≤ i₀.range := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨algebraMap o _ ζ, (hi₀ ζ).trans hζ⟩
    · obtain ⟨v, hv⟩ := (IsLocalization.map_units (Localization M) (⟨n, n, hn, rfl⟩ : M)).exists_right_inv
      refine ⟨v, ?_⟩
      have := congrArg i₀ hv
      rw [map_mul, hi₀, map_one, map_natCast] at this
      exact eq_inv_of_mul_eq_one_right this
  let e : Localization M ≃+* i₀.range := RingEquiv.ofBijective i₀.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), i₀.rangeRestrict_surjective⟩
  let z₀ : ZP p k →+* Localization M := e.symm.toRingHom.comp (Subring.inclusion hle)
  have hz₀ : ∀ x, i₀ (z₀ x) = (ZP p k).subtype x := fun x =>
    congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))
  refine ⟨M, i₀, z₀, hinj, hz₀, hi₀, fun O _ i z bb hi hz hb => ?_⟩
  have hv : ∀ y : M, IsUnit (bb y) := by
    rintro ⟨_, n, hn, rfl⟩
    refine IsUnit.of_mul_eq_one (z ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨n, hn, rfl⟩)⟩) (hi ?_)
    rw [map_mul, hz, hb, map_one]
    simpa using mul_inv_cancel₀ (h0 n hn)
  have hga : i.comp (IsLocalization.lift (S := Localization M) hv) = i₀ :=
    IsLocalization.ringHom_ext M (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, IsLocalization.lift_eq]
      exact (hb x).trans (hi₀ x).symm)
  refine ⟨IsLocalization.lift hv, IsLocalization.lift_comp hv, RingHom.ext fun x => hi ?_⟩
  rw [hz, ← hz₀, ← hga]; rfl


end GlobalTheory.SiegelClassify
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegClause

theorem lbIso_pull_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso L' (L.pull φ))
    (ψ : X'' ⟶ X') : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) (chartPullSame L _ _ _ ψ fun _ => rfl) h

theorem lbIso_lam_pull {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : A ⟶ B) [IsMonHom e] {L : LB A.left} {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull e.left)) : LBIso (abelian₂ A L) ((abelian₂ B M).pull (e ⊗ₘ e).left) := by
  have pa : ∀ I : Finset (Fin 2), psum A (x2 A) I ≫ e = (e ⊗ₘ e) ≫ psum B (x2 B) I := by
    intro I
    refine (psum_hom (MonoidHom.mk' (fun z : G2 A ⟶ A => z ≫ e) fun a b => MonObj.mul_comp a b _) _ I).trans
      (Eq.trans (congrArg (fun z => psum B z I) (funext fun k => ?_)) (psum_hom (preHom (e ⊗ₘ e)) _ I).symm)
    fin_cases k
    · exact (tensorHom_fst e e).symm
    · exact (tensorHom_snd e e).symm
  have hB : (abelian₂ B M).IsLB := DVR.linComb_isLB M hM _ _
  have r : LBIso (abelian₂ B M) (abelian₂ B M) := GlobalTheory.PolBaseChange.lbIso_refl hB
  have h₁ : LBIso (abelian₂ A L) (abelian₂ A (M.pull e.left)) := GlobalTheory.PowPrimitive.lbIso_linComb h _ _
  have h₂ : LBIso (abelian₂ A (M.pull e.left)) ((abelian₂ B M).pull (e ⊗ₘ e).left) :=
    LBIso.chartPull (chartPullLinComb M e.left (K := ULift.{0} (Finset (Fin 2)))
      (fun I => (psum A (x2 A) I.down).left) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) (e ⊗ₘ e).left (fun I => congrArg (fun z => z.left) (pa I.down)))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B M) _ _ rfl) r
  exact LBIso.trans (DVR.linComb_isLB L hL _ _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (pull_isLB hB _) h₁ h₂

theorem eq_of_basis {κ La Γ : Type} [Fintype κ] [DecidableEq κ] [AddCommGroup La] [CommGroup Γ]
    (bas : (κ → ℤ) ≃ₗ[ℤ] La) (F F' : La → Γ) (hF : ∀ x y, F (x + y) = F x * F y)
    (hF' : ∀ x y, F' (x + y) = F' x * F' y) (h : ∀ i, F (bas (Pi.single i 1)) = F' (bas (Pi.single i 1))) : F = F' := by
  let G : La →+ Additive Γ := AddMonoidHom.mk' (fun x => Additive.ofMul (F x)) fun x y => congrArg _ (hF x y)
  let G' : La →+ Additive Γ := AddMonoidHom.mk' (fun x => Additive.ofMul (F' x)) fun x y => congrArg _ (hF' x y)
  have e : G.toIntLinearMap ∘ₗ bas.toLinearMap = G'.toIntLinearMap ∘ₗ bas.toLinearMap :=
    (Pi.basisFun ℤ κ).ext fun i => by
      rw [Pi.basisFun_apply]
      exact congrArg Additive.ofMul (h i)
  funext x
  obtain ⟨y, rfl⟩ := bas.surjective x
  exact Additive.ofMul.injective (LinearMap.congr_fun e y)



end GlobalTheory.ZM.SiegClause
end
