import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelReductionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianCubeFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFinrankOfCokernel

section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_reduction_holds : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), LevelReduction P := by
  first | exact @GlobalTheory.HodgeTateLevel.levelReduction | exact GlobalTheory.HodgeTateLevel.levelReduction | (intros; apply GlobalTheory.HodgeTateLevel.levelReduction <;> assumption)
end

section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_not_in_closure : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → SpecialFibreNotInClosure p O := by
  first | exact @GlobalTheory.WeilIntegral.specialFibreNotInClosure | exact GlobalTheory.WeilIntegral.specialFibreNotInClosure | (intros; apply GlobalTheory.WeilIntegral.specialFibreNotInClosure <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat

namespace GlobalTheory.WeilIntegral

theorem exists_open_generic_le (p : ℕ) (O : Type) [CommRing O] (h : SpecialFibreNotInClosure p O)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp O) [Smooth f] (x : X)
    (hx : (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (f x)) (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ U : X.Opens, (∃ y : X, y ∈ U ∧ (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (f y)) ∧
      ∀ y ∈ U, PrimeSpectrum.asIdeal (R := O) (f y) = ⊥ → y ∈ W := by
  obtain ⟨R, j, hj, ⟨x', rfl⟩, -⟩ := X.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  have : Nonempty (Spec R) := ⟨x'⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 ‹_›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have hs' : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  letI : Algebra O R := φ.hom.toAlgebra
  have : Algebra.Smooth O R := hs'
  have key : ∀ (z : Spec R) (c : O), c ∈ PrimeSpectrum.asIdeal (R := O) (f (j z)) ↔
      algebraMap O R c ∈ PrimeSpectrum.asIdeal (R := R) z := by
    intro z c
    rw [← Scheme.Hom.comp_apply, ← hφ]
    rfl
  obtain ⟨_, hz, z, rfl⟩ := nonempty_preirreducible_inter W.isOpen j.isOpenEmbedding.isOpen_range hW ⟨_, x', rfl⟩
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hza, ha⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
    (a := (z : PrimeSpectrum R)) (u := (j ⁻¹ᵁ W : Set (Spec R))) hz (j ⁻¹ᵁ W).isOpen
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hza (Ideal.zero_mem _)
  obtain ⟨q, g, c, hq, hg, hc, d, hd⟩ := h R a ha0 ⟨x', by simpa using (key x' p).1 hx⟩
  refine ⟨j ''ᵁ (PrimeSpectrum.basicOpen g), ⟨j q, ⟨q, hg, rfl⟩, (key q p).2 (by simpa using hq)⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ h0
  refine ha (a := y) fun hay => ?_
  have h1 : algebraMap O R c * g ∈ PrimeSpectrum.asIdeal (R := R) y := hd ▸ Ideal.mul_mem_right _ _ hay
  rcases (PrimeSpectrum.isPrime (R := R) y).mem_or_mem h1 with h2 | h2
  · exact hc (h0.le ((key y c).2 h2))
  · exact hy h2

theorem hasTrivialisingOpen_of_specialFibreNotInClosure (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [hp : Fact ¬IsUnit (p : O)]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (h : SpecialFibreNotInClosure p O) :
    HasTrivialisingOpen P := by
  have hinj := P.integers.hom_inj
  have : IsDomain O := hinj.isDomain (algebraMap O C)
  have : IsFractionRing O C := P.integers.isFractionRing
  have := P.semi.smooth
  have := P.semi.geomConnected
  have : IsIntegral P.G.left := isIntegral_of_smooth_of_geometricallyConnected P.G.hom
  have := geometricallyIntegral_of_smooth P.G.hom
  have : IsPreimmersion (spMap (algebraMap O C)) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have : IsPreimmersion P.gen := MorphismProperty.of_isPullback P.gen_pull.1.flip ‹_›
  obtain ⟨m, hm, hpm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hp.out)
  obtain ⟨x, hx⟩ := P.G.hom.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum O)
  have := P.A.isAb.smooth
  have := P.A.isAb.geomConnected
  have : IsIntegral P.A.A.left := isIntegral_of_smooth_of_geometricallyConnected P.A.A.hom
  obtain ⟨a⟩ : Nonempty P.A.A.left := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (P.A.isLB.cover.ge (Set.mem_univ a))
  obtain ⟨W, hW, hWV⟩ := P.gen.isEmbedding.isInducing.isOpen_iff.1 (P.A.L.U i).isOpen
  obtain ⟨U, hU, hUW⟩ := exists_open_generic_le p O h P.G.hom x (by rw [hx]; exact hpm) ⟨W, hW⟩
    ⟨P.gen a, hWV.ge hi⟩
  refine ⟨U, hU, ChartRig.exists_gen_pull _ _ i P.A.isLB fun y _ => hWV.le (hUW _ y.2 ?_)⟩
  rw [← Scheme.Hom.comp_apply, P.gen_pull.1.w, Scheme.Hom.comp_apply]
  have e : ∀ z : PrimeSpectrum C, Ideal.comap (algebraMap O C) z.asIdeal = ⊥ := fun z => by
    rw [Ideal.eq_bot_of_prime z.asIdeal]
    exact Ideal.comap_bot_of_injective _ hinj
  exact e _

theorem hasTrivialisingOpen (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (h : SpecialFibreNotInClosure p O) :
    HasTrivialisingOpen P :=
  hasTrivialisingOpen_of_specialFibreNotInClosure p C v O Λ P h

end GlobalTheory.WeilIntegral
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialising_open_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), SpecialFibreNotInClosure p O → HasTrivialisingOpen P := by
  atlas_forward_decl GlobalTheory.WeilIntegral.hasTrivialisingOpen
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem exists_point_in_all {K : Type} [Field K] [IsAlgClosed K] {X Y : Scheme.{0}} (π : X ⟶ Y)
    [LocallyOfFiniteType π] [GeometricallyIntegral π] (x : Sp K ⟶ Y) {J : Type} [Finite J]
    (U : J → X.Opens) (hU : ∀ i, ∃ q : X, q ∈ U i ∧ π q = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ∀ i, g (IsLocalRing.closedPoint K) ∈ U i := by
  have : IsIntegral (pullback π x) :=
    GeometricallyIntegral.geometrically_isIntegral x _ _ (IsPullback.of_hasPullback π x)
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  have hgen : ∀ i, pullback.fst π x (genericPoint (pullback π x :)) ∈ U i := fun i => by
    obtain ⟨q, hq, hx⟩ := hU i
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) q
      (IsLocalRing.closedPoint K) hx
    exact ((genericPoint_specializes z).map (pullback.fst π x).continuous).mem_open (U i).isOpen (hz ▸ hq)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints
    (Z := ⋂ i, ((pullback.fst π x ⁻¹ᵁ U i : (pullback π x).Opens) : Set (pullback π x :))) ⟨_, Set.mem_iInter.2 hgen⟩
    (isOpen_iInter_of_finite fun i => (pullback.fst π x ⁻¹ᵁ U i).isOpen).isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun i => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc _) ∈ U i
    exact (congrArg (fun t => pullback.fst π x t ∈ U i)
      (pointOfClosedPoint_apply (pullback.snd π x) c hc _)).mpr (Set.mem_iInter.1 hcO i)

section Translation

variable {O : Type} [CommRing O]

theorem specO_self_hom : (specO O O).hom = 𝟙 (Sp O) := Spec.map_id _

def toBase (G : Over (Sp O)) : G ⟶ specO O O :=
  Over.homMk G.hom ((congrArg (G.hom ≫ ·) specO_self_hom).trans (Category.comp_id _))

theorem eq_toBase {G : Over (Sp O)} (f : G ⟶ specO O O) : f = toBase G :=
  Over.OverMorphism.ext (((Category.comp_id _).symm.trans
    (congrArg (f.left ≫ ·) specO_self_hom.symm)).trans (Over.w f))

def transl {G : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) : G ⟶ G := 𝟙 G * (toBase G ≫ a)

theorem comp_transl {G T : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) (w : T ⟶ G) :
    w ≫ transl a = w * (toBase T ≫ a) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, eq_toBase (w ≫ toBase G)]

theorem point_comp_transl {G : Over (Sp O)} [GrpObj G] (a z : specO O O ⟶ G) :
    z ≫ transl a = z * a := by
  rw [comp_transl, ← eq_toBase (𝟙 _), Category.id_comp]

theorem transl_inv_comp {G : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) :
    transl a⁻¹ ≫ transl a = 𝟙 G := by
  rw [comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one,
    _root_.mul_one]

end Translation

theorem exists_translate_inOpen (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (G : Over (Sp O)) [GrpObj G] [Smooth G.hom]
    [GeometricallyConnected G.hom] (U : G.left.Opens) (x : G.left) (hx : x ∈ U)
    (hx' : G.hom x = IsLocalRing.closedPoint O) (J : Type) [Finite J] (a : J → (specO O O ⟶ G)) :
    ∃ z : specO O O ⟶ G, ∀ i, InOpen U (z * a i) := by
  obtain ⟨-, hk, hlift⟩ := valuationRing_henselian_and_lift_of_isAlgClosed O K
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  have hr : spMap (IsLocalRing.residue O) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
      IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  obtain ⟨g, hg, hgU⟩ := exists_point_in_all G.hom (spMap (IsLocalRing.residue O))
    (fun i => (transl (a i)).left ⁻¹ᵁ U) fun i => ⟨(transl (a i)⁻¹).left x, by
      show (transl (a i)).left ((transl (a i)⁻¹).left x) ∈ U
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_inv_comp]
      exact hx, by
      rw [← Scheme.Hom.comp_apply, Over.w, hx', hr]⟩
  obtain ⟨y, hy, hy'⟩ := hlift _ G.hom inferInstance g hg
  refine ⟨Over.homMk y (hy.trans specO_self_hom.symm), fun i => ?_⟩
  rw [← point_comp_transl]
  have h1 : (y ≫ (transl (a i)).left) (IsLocalRing.closedPoint O) ∈ U := by
    have e : g (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = y (IsLocalRing.closedPoint O) := by
      rw [← hy', ← hr]
      rfl
    have := hgU i
    rw [e] at this
    exact this
  exact eq_top_iff.2 fun q _ =>
    ((IsLocalRing.specializes_closedPoint (R := O) q).map
      (y ≫ (transl (a i)).left).continuous).mem_open U.isOpen h1

theorem translatesInto : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), TranslatesInto P := by
  intro p hp C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P U ⟨x, hx, hxp⟩ J _ a
  have hv := P.integers
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI := P.semi.smooth
  haveI := P.semi.geomConnected
  refine exists_translate_inOpen O C P.G U x hx ?_ J a
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top)
    fun b hb => ?_)
  have h1 : v (algebraMap O C b) < 1 := lt_of_le_of_ne (hv.map_le_one b) fun e => hb (hv.isUnit_of_one' e)
  have h2 : 0 < v (algebraMap O C p) := by
    rw [map_natCast]
    exact pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
  have h3 : (p : O) ∣ b ^ n := hv.le_iff_dvd.1 (by rw [map_pow, map_pow]; exact hn.le)
  exact (PrimeSpectrum.isPrime _).mem_of_pow_mem n (Ideal.mem_of_dvd _ h3 hxp)

end GlobalTheory.WeilIntegral
end
end

section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translates_into_holds : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), TranslatesInto P := by
  atlas_forward_decl GlobalTheory.WeilIntegral.translatesInto
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem exists_smooth_chart {O : Type} [CommRing O] (X : Over (Sp O)) [Smooth X.hom] (W : X.left.Opens)
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (w : specO O B ⟶ X) (hw : InOpen W w) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : Algebra.Smooth O R) (θ : R →ₐ[O] B)
      (r : specO O R ⟶ X), ptMap θ ≫ r = w ∧ InOpen W r := by
  let w₀ : Spec (CommRingCat.of B) ⟶ X.left := w.left
  have hx : w₀ (IsLocalRing.closedPoint B) ∈ W := by
    have : IsLocalRing.closedPoint B ∈ w₀ ⁻¹ᵁ W := by
      rw [show w₀ ⁻¹ᵁ W = ⊤ from hw]; trivial
    exact this
  obtain ⟨R, f, hf, h1, h2⟩ := Scheme.exists_affine_mem_range_and_range_subset hx
  have hr : Set.range w₀ ⊆ Set.range f := by
    have : w₀ ⁻¹ᵁ f.opensRange = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem w₀ h1
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ w₀ ⁻¹ᵁ f.opensRange := by rw [this]; trivial
    exact hy
  let l := IsOpenImmersion.lift f w₀ hr
  have hl : l ≫ f = w₀ := IsOpenImmersion.lift_fac _ _ _
  let α : CommRingCat.of O ⟶ R := Spec.preimage (f ≫ X.hom)
  have hα : Spec.map α = f ≫ X.hom := Spec.map_preimage _
  letI : Algebra O R := α.hom.toAlgebra
  have hs : Smooth (Spec.map α) := by rw [hα]; infer_instance
  have hs' : α.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  let β : R ⟶ CommRingCat.of B := Spec.preimage l
  have hβ : Spec.map β = l := Spec.map_preimage _
  have hc : α ≫ β = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hβ, ← Category.assoc, hl]
    exact Over.w w
  let θ : R →ₐ[O] B := ⟨β.hom, fun a => congrArg (fun g => g.hom a) hc⟩
  refine ⟨R, inferInstance, inferInstance, hs', θ, Over.homMk f hα.symm, ?_, ?_⟩
  · ext1
    exact (congrArg (· ≫ f) hβ).trans hl
  · exact top_le_iff.1 fun y _ => h2 ⟨y, rfl⟩

theorem CubeIn.comp {S : Scheme.{0}} {X T T' : Over S} [GrpObj X] {U : X.left.Opens} {z a b c : T ⟶ X}
    (h : CubeIn U z a b c) (u : T' ⟶ T) : CubeIn U (u ≫ z) (u ≫ a) (u ≫ b) (u ≫ c) := by
  intro i j k hi hj hk
  have := (h i j k hi hj hk).comp u
  simpa only [MonObj.comp_mul, MonObj.comp_pow] using this

theorem exists_smooth_cube {O : Type} [CommRing O] (G : Over (Sp O)) [GrpObj G] [Smooth G.hom]
    (U : G.left.Opens) (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (z a b c : specO O B ⟶ G)
    (h : CubeIn U z a b c) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : Algebra.Smooth O R) (θ : R →ₐ[O] B)
      (z₀ a₀ b₀ c₀ : specO O R ⟶ G), ptMap θ ≫ z₀ = z ∧ ptMap θ ≫ a₀ = a ∧ ptMap θ ≫ b₀ = b ∧
        ptMap θ ≫ c₀ = c ∧ CubeIn U z₀ a₀ b₀ c₀ := by
  have h2 : ∀ X Y : Over (Sp O), Smooth X.hom → Smooth Y.hom → Smooth (X ⊗ Y).hom := by
    intro X Y hX hY
    have : Smooth (pullback.fst X.hom Y.hom) :=
      smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback X.hom Y.hom).flip hY
    exact inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))
  let X : Over (Sp O) := (G ⊗ G) ⊗ (G ⊗ G)
  haveI : Smooth X.hom := h2 _ _ (h2 _ _ ‹_› ‹_›) (h2 _ _ ‹_› ‹_›)
  let p₁ : X ⟶ G := fst _ _ ≫ fst _ _
  let p₂ : X ⟶ G := fst _ _ ≫ snd _ _
  let p₃ : X ⟶ G := snd _ _ ≫ fst _ _
  let p₄ : X ⟶ G := snd _ _ ≫ snd _ _
  let w : specO O B ⟶ X := lift (lift z a) (lift b c)
  have e₁ : w ≫ p₁ = z := by simp [w, p₁]
  have e₂ : w ≫ p₂ = a := by simp [w, p₂]
  have e₃ : w ≫ p₃ = b := by simp [w, p₃]
  have e₄ : w ≫ p₄ = c := by simp [w, p₄]
  let V : ℕ × ℕ × ℕ → X.left.Opens := fun n => (p₁ * p₂ ^ n.1 * p₃ ^ n.2.1 * p₄ ^ n.2.2).left ⁻¹ᵁ U
  let s : Finset (ℕ × ℕ × ℕ) := Finset.Iic (1, 1, 1)
  have key : ∀ {T : Over (Sp O)} (r : T ⟶ X),
      InOpen (s.inf V) r ↔ CubeIn U (r ≫ p₁) (r ≫ p₂) (r ≫ p₃) (r ≫ p₄) := by
    intro T r
    have e : ∀ n : ℕ × ℕ × ℕ, InOpen (V n) r ↔
        InOpen U ((r ≫ p₁) * (r ≫ p₂) ^ n.1 * (r ≫ p₃) ^ n.2.1 * (r ≫ p₄) ^ n.2.2) := by
      intro n
      simp only [← MonObj.comp_pow, ← MonObj.comp_mul]
      unfold InOpen
      rw [Over.comp_left, Scheme.Hom.comp_preimage]
    constructor
    · intro hr i j k hi hj hk
      refine (e (i, j, k)).1 (top_le_iff.1 ?_)
      rw [← show r.left ⁻¹ᵁ s.inf V = ⊤ from hr]
      exact Scheme.Hom.preimage_mono _ (Finset.inf_le (by simp [s, hi, hj, hk]))
    · intro hr
      refine top_le_iff.1 fun y _ => ?_
      change r.left y ∈ ((s.inf V : X.left.Opens) : Set X.left)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
      refine Set.mem_iInter₂.2 fun n hn => ?_
      obtain ⟨h1, h2, h3⟩ := Finset.mem_Iic.1 hn
      have : y ∈ r.left ⁻¹ᵁ V n := by
        rw [show r.left ⁻¹ᵁ V n = ⊤ from (e n).2 (hr _ _ _ h1 h2 h3)]; trivial
      exact this
  obtain ⟨R, _, _, _, θ, r, hr, hW⟩ := exists_smooth_chart X (s.inf V) B w
    ((key w).2 (by rwa [e₁, e₂, e₃, e₄]))
  refine ⟨R, _, _, ‹_›, θ, r ≫ p₁, r ≫ p₂, r ≫ p₃, r ≫ p₄, ?_, ?_, ?_, ?_, (key r).1 hW⟩ <;>
    rw [← Category.assoc, hr] <;> assumption

def pushPt {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (T : Over S') :
    (T ⟶ A) →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]))
    fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_generic_cube {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (T : Over S') (U : G.left.Opens)
    (z a b c : Over.mk (T.hom ≫ f) ⟶ G) (hc : CubeIn U z a b c) :
    ∃ z' a' b' c' : T ⟶ A, z'.left ≫ φ = z.left ∧ a'.left ≫ φ = a.left ∧ b'.left ≫ φ = b.left ∧
      c'.left ≫ φ = c.left ∧ CubeIn (φ ⁻¹ᵁ U) z' a' b' c' := by
  have hs : Function.Surjective (pushPt h T) := fun x =>
    ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨z, rfl⟩ := hs z
  obtain ⟨a, rfl⟩ := hs a
  obtain ⟨b, rfl⟩ := hs b
  obtain ⟨c, rfl⟩ := hs c
  refine ⟨z, a, b, c, rfl, rfl, rfl, rfl, fun i j k hi hj hk => ?_⟩
  have := hc i j k hi hj hk
  simp only [← map_pow, ← map_mul] at this
  exact this

theorem exists_numerator {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
    (R : Type) [CommRing R] [Algebra O R] (s : (C ⊗[O] R)ˣ) :
    ∃ (f g : R) (c e : O), c ≠ 0 ∧ e ≠ 0 ∧ f * g = algebraMap O R c ∧
      (1 : C) ⊗ₜ[O] f = algebraMap O (C ⊗[O] R) e * s := by
  let m : R →ₗ[O] C ⊗[O] R := TensorProduct.mk O C R 1
  haveI : IsLocalizedModule (nonZeroDivisors O) m :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) C m).2 (TensorProduct.isBaseChange O R C)
  obtain ⟨⟨f, e₁⟩, hf⟩ := IsLocalizedModule.surj (nonZeroDivisors O) m (s : C ⊗[O] R)
  obtain ⟨⟨g, e₂⟩, hg⟩ := IsLocalizedModule.surj (nonZeroDivisors O) m (s⁻¹ : (C ⊗[O] R)ˣ)
  have hf' : (1 : C) ⊗ₜ[O] f = (e₁ : O) • (s : C ⊗[O] R) := hf.symm
  have hg' : (1 : C) ⊗ₜ[O] g = (e₂ : O) • ((s⁻¹ : (C ⊗[O] R)ˣ) : C ⊗[O] R) := hg.symm
  have h : m (f * g) = m (((e₁ : O) * e₂) • 1) := by
    have : m (f * g) = ((1 : C) ⊗ₜ[O] f) * ((1 : C) ⊗ₜ[O] g) := by simp [m]
    rw [this, hf', hg', smul_mul_smul_comm, Units.mul_inv, map_smul]
    rfl
  obtain ⟨e₃, h₃⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) h
  have n := fun x : nonZeroDivisors O => nonZeroDivisors.coe_ne_zero x
  refine ⟨(e₃ : O) • f, g, e₃ * (e₁ * e₂), e₃ * e₁, mul_ne_zero (n _) (mul_ne_zero (n _) (n _)),
    mul_ne_zero (n _) (n _), ?_, ?_⟩
  · rw [smul_mul_assoc, Algebra.algebraMap_eq_smul_one, mul_smul]
    exact h₃
  · rw [TensorProduct.tmul_smul, hf', smul_smul, Algebra.smul_def]

theorem cubeValuesIntegral_of_localUnits {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0}
    {O : Type} [CommRing O] [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
    (hL : LocalUnits O) : CubeValuesIntegral P := by
  rintro U Θ hΘ B _ _ _ _ _ ⟨ψ₀⟩ z a b c hcube
  have hinj := P.integers.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : Smooth P.G.hom := P.semi.smooth
  obtain ⟨R, _, _, _, θ, z₀, a₀, b₀, c₀, rfl, rfl, rfl, rfl, h₀⟩ := exists_smooth_cube P.G U B z a b c hcube
  let iC : C →+* C ⊗[O] R := Algebra.TensorProduct.includeLeftRingHom
  let iR : R →+* C ⊗[O] R := (Algebra.TensorProduct.includeRight (R := O) (A := C) (B := R)).toRingHom
  let t : Sp (C ⊗[O] R) ⟶ Sp C := spMap iC
  let m : Over.mk ((Over.mk t).hom ≫ spMap (algebraMap O C)) ⟶ specO O R := Over.homMk (spMap iR) (by
    change spMap iR ≫ spMap (algebraMap O R) = spMap iC ≫ spMap (algebraMap O C)
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm)
  obtain ⟨z₁, a₁, b₁, c₁, hz, ha, hb, hc, h₁⟩ :=
    exists_generic_cube P.gen_pull (Over.mk t) U _ _ _ _ (h₀.comp m)
  obtain ⟨f, g, k, e, hk, he, hfg, hf⟩ := exists_numerator R (Θ _ t z₁ a₁ b₁ c₁)
  obtain ⟨u, hu⟩ := hL R B θ ψ₀ f g k hk hfg
  have hd : ψ₀ (θ f) ≠ 0 := by
    have := congrArg (fun x => ψ₀ (θ x)) hfg
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at this
    exact left_ne_zero_of_mul (this ▸ hk)
  have he' : algebraMap O C e ≠ 0 := (map_ne_zero_iff _ hinj).2 he
  refine ⟨Units.mk0 (algebraMap O C (ψ₀ (θ f)) / algebraMap O C e)
    (div_ne_zero ((map_ne_zero_iff _ hinj).2 hd) he'), u, fun ψ z' a' b' c' hz' ha' hb' hc' => ?_⟩
  let φ : C ⊗[O] R →ₐ[O] C := Algebra.TensorProduct.lift (AlgHom.id O C)
    ((Algebra.ofId O C).comp (ψ.comp θ)) fun _ _ => Commute.all _ _
  have key : ∀ (x₀ : specO O R ⟶ P.G) (x₁ : Over.mk t ⟶ P.A.A) (x' : Pts P.A.A),
      x₁.left ≫ P.gen = (m ≫ x₀).left → IsGeneric P (ptMap ψ ≫ ptMap θ ≫ x₀) x' →
      x'.left = spMap φ.toRingHom ≫ x₁.left := by
    intro x₀ x₁ x' h h'
    refine P.gen_pull.1.hom_ext ?_ ?_
    · refine h'.trans ?_
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (spMap φ.toRingHom ≫ ·) h)).symm
      change spMap (algebraMap O C) ≫ spMap ψ.toRingHom ≫ spMap θ.toRingHom ≫ x₀.left =
        spMap φ.toRingHom ≫ spMap iR ≫ x₀.left
      simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      simp [φ, iR]
    · refine (Over.w x').trans ?_
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (spMap φ.toRingHom ≫ ·) (Over.w x₁))).symm
      change 𝟙 (Sp C) = spMap φ.toRingHom ≫ spMap iC
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext x
      simp [φ, iC]
  rw [hΘ _ _ φ.toRingHom t _ z₁ a₁ b₁ c₁ z' a' b' c' (key _ _ _ hz hz') (key _ _ _ ha ha') (key _ _ _ hb hb')
    (key _ _ _ hc hc') h₁]
  have h2 := congrArg φ hf
  rw [map_mul, AlgHom.commutes] at h2
  have h3 : φ ((1 : C) ⊗ₜ[O] f) = algebraMap O C (ψ (θ f)) := by simp [φ]
  have h4 : ψ (θ f) = ψ₀ (θ f) * ψ u := by
    conv_lhs => rw [hu]
    simp
  rw [h3, h4, map_mul] at h2
  change φ _ = _
  rw [Units.val_mk0, div_mul_eq_mul_div, h2, mul_div_cancel_left₀ _ he']

theorem cubeValuesIntegral (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) : LocalUnits O → CubeValuesIntegral P :=
  cubeValuesIntegral_of_localUnits P

end GlobalTheory.WeilIntegral
end
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_values_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), LocalUnits O → CubeValuesIntegral P := by
  atlas_forward_decl GlobalTheory.WeilIntegral.cubeValuesIntegral
end

section
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilIntegral

theorem exists_factor_pi {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    {J : Type} [Finite J] {T : J → Type} [∀ i, CommRing (T i)] [∀ i, Algebra O (T i)]
    (e : B ≃ₐ[O] Π i, T i) (ψ : B →ₐ[O] O) :
    ∃ (i : J) (φ : T i →ₐ[O] O), ψ = φ.comp ((Pi.evalAlgHom O T i).comp e.toAlgHom) := by
  classical
  haveI := Fintype.ofFinite J
  set χ : (Π i, T i) →ₐ[O] O := ψ.comp e.symm.toAlgHom with hχ
  have hsum : ∑ i, χ (Pi.single i 1) = 1 := by
    rw [← map_sum, show (∑ i, Pi.single i 1 : Π i, T i) = 1 from Finset.univ_sum_single (1 : Π i, T i), map_one]
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hidem : IsIdempotentElem (χ (Pi.single i 1)) := by
    have : IsIdempotentElem (Pi.single i (1 : T i) : Π j, T j) := by
      unfold IsIdempotentElem
      rw [← Pi.single_mul, _root_.one_mul]
    exact this.map χ
  have h1 : χ (Pi.single i 1) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.1 hidem).resolve_left hi
  have hmul : ∀ y : Π j, T j, y * Pi.single i 1 = Pi.single i (y i) := by
    intro y
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  let φ : T i →ₐ[O] O :=
    { toFun := fun t => χ (Pi.single i t)
      map_one' := h1
      map_mul' := fun a b => by rw [Pi.single_mul, map_mul]
      map_zero' := by simp only [Pi.single_zero, map_zero]
      map_add' := fun a b => by simp only [Pi.single_add, map_add]
      commutes' := fun r => by
        change χ (Pi.single i (algebraMap O (T i) r)) = _
        rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, h1, smul_eq_mul, _root_.mul_one]
        rfl }
  refine ⟨i, φ, AlgHom.ext fun b => ?_⟩
  have hb : ψ b = χ (e b) := by simp [hχ]
  rw [hb]
  change χ (e b) = χ (Pi.single i (e b i))
  rw [← hmul, map_mul, h1, _root_.mul_one]

end GlobalTheory.WeilIntegral

open GlobalTheory.TangentPow in

theorem GlobalTheory.WeilIntegral.weilIntegralFinite_of_local : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralLocal P → WeilIntegralFinite P := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hloc B _ _ _ _ N hN x y hx hy
  classical
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : HenselianLocalRing O := henselianLocalRing_of_valuationRing_of_isAlgClosed O C
  obtain ⟨J, hJ, T, _, _, e, hT⟩ := ((finite_algebras_over_henselian O).1 B).1
  let π : ∀ i, B →ₐ[O] T i := fun i => (Pi.evalAlgHom O T i).comp e.toAlgHom
  have hflat : ∀ i, Module.Flat O (T i) := fun i =>
    Module.Flat.of_retract (e.symm.toLinearMap ∘ₗ LinearMap.single O T i)
      (LinearMap.proj i ∘ₗ e.toLinearMap) (LinearMap.ext fun t => by simp)
  have key : ∀ i, ∃ u : T i, ∀ φ : T i →ₐ[O] O, algebraMap O C (φ u) =
      (weil P.A N (P.toA (ptMap φ ≫ ptMap (π i) ≫ x)) (P.toA (ptMap φ ≫ ptMap (π i) ≫ y)) : C) := by
    intro i
    haveI := (hT i).1
    haveI := (hT i).2
    haveI := hflat i
    exact hloc (T i) N hN (ptMap (π i) ≫ x) (ptMap (π i) ≫ y)
      (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  choose u hu using key
  refine ⟨e.symm u, fun ψ => ?_⟩
  obtain ⟨i, φ, rfl⟩ := GlobalTheory.WeilIntegral.exists_factor_pi e ψ
  rw [← ptMap_comp_ptMap, Category.assoc, Category.assoc, ← hu i φ]
  exact congrArg (fun t => algebraMap O C (φ t)) (congrFun (e.apply_symm_apply u) i)
end
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_integral_local_to_finite : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralLocal P → WeilIntegralFinite P := by
  atlas_forward_decl GlobalTheory.WeilIntegral.weilIntegralFinite_of_local
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.KernelNoTorsion GlobalTheory.RaynaudPDiv
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.RaynaudTower

theorem exists_pDivGroup_raynaud_tower : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate) (tw : G.TorsionTower P.Gt), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) ∧ (∀ (s : G.Tate) (n : ℕ), (e s : P.T).lev n = (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n))) ∧ ∀ n : ℕ, algebraMap O C (muRoot ζ n) = (P.eps.1.lev n : C) := by
  intro p hp C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hi := P.integers.hom_inj
  haveI : IsDomain O := hi.isDomain (algebraMap O C)
  have hA := isSemiAbelian_of_isGt _ _ P.Gt ⟨P.D⟩
  haveI := hA.smooth
  obtain ⟨G, ⟨t⟩⟩ := exists_tower p O (fun h => hp.out.ne_zero ((Nat.cast_eq_zero (R := C)).1 (by
    rw [← map_natCast (algebraMap O C), h, map_zero]))) P.Gt hA P.finite_flat
  obtain ⟨e, he⟩ := exists_tateEquiv p O P.Gt G t
  obtain ⟨l, hl⟩ := exists_lieEquiv p O P.Gt G t
  obtain ⟨ζ, hζ, hζ'⟩ := exists_generator P.integers P.eps
  choose c hc using fun s : P.T => exists_dual_tate p O P.Gt G t (P.weilChar s)
  have hu : ∀ s n, charElem (c s) n = (unitOf (torsionLift (t.y n) (t.y_pow n) ≫ (P.weilChar s).χ n) : G.A n) :=
    fun s n => hc s n _ (AlgHom.id O _) _ (by rw [torsionLift_ι, spOver_id, Category.id_comp])
  have hx : ∀ {a b : G.dual.Tate}, (∀ n, charElem a n = charElem b n) → a = b := fun h =>
    (charHom G).injective (hom_mu_ext fun n => by rw [charHom_app_muT, charHom_app_muT, h])
  have hadd : ∀ s s', c (s + s') = c s + c s' := fun s s' => hx fun n => by
    rw [charElem_add, hu, hu, hu, P.weilChar_add, MonObj.comp_mul, GmPoints.unitOf_mul, Units.val_mul]
  have hpow : ∀ (R : Type) [CommRing R] [Algebra O R] (w : specO O R ⟶ Gm (Sp O)) (k : ℕ),
      unitOf (w ^ k) = unitOf w ^ k := fun R _ _ w k => map_pow (MonoidHom.mk' unitOf GmPoints.unitOf_mul) w k
  have hsm : ∀ (a : ℤ_[p]) s, c (a • s) = a • c s := fun a s => hx fun n => by
    have h : (P.weilChar (a • s)).χ n = (P.weilChar s).χ n ^ digit n a := P.char_ext fun w => by
      rw [P.isWeilChar_weilChar, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val, map_pow,
        P.isWeilChar_weilChar, Tate.lev_smul, weil_pow_right (one_le_ppow p n) (s.lev_pow n) (P.toA_pow w),
        Units.val_pow_eq_pow_val]
    rw [charElem_smul, hu, hu, h, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val]
  refine ⟨G, e.trans (LinearEquiv.ofInjective _ (Tate.map_injective P.toA_injective)), l,
    ⟨⟨c, hadd⟩, hsm⟩, ζ, t, hζ, fun s s' => muRoot_ext fun n => hi ?_,
    fun x s => lie_dlog p O P.Gt G t _ _ (hc s) x _ (hl x), fun s n => ?_, hζ'⟩
  · have hw := torsionLift_ι _ ((t.exists_iff n _).1 ⟨s.pt n, rfl⟩)
    rw [muRoot_pairing, muRoot_smul, map_pow, hζ', ← Units.val_pow_eq_pow_val, pow_pairT]
    refine (congrArg (algebraMap O C) (hc s' n O _ _ hw)).trans ((P.isWeilChar_weilChar s' n _).trans ?_)
    rw [hw, ← he]
    rfl
  · rw [← he]
    rfl

end GlobalTheory.RaynaudTower
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pdiv_group_tate_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate) (tw : G.TorsionTower P.Gt), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) ∧ (∀ (s : G.Tate) (n : ℕ), (e s : P.T).lev n = (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n))) ∧ ∀ n : ℕ, algebraMap O C (muRoot ζ n) = (P.eps.1.lev n : C) := by
  atlas_forward_decl GlobalTheory.RaynaudTower.exists_pDivGroup_raynaud_tower
end

section
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HodgeTateCokernel

theorem exists_retraction_range {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (f : M →* M') (hf : Function.Injective f) [Module.Finite ℤ_[p] (HTLat.Tate p M')] :
    ∃ r : HTLat.Tate p M' →ₗ[ℤ_[p]] LinearMap.range (HTLat.Tate.map p f),
      ∀ s : LinearMap.range (HTLat.Tate.map p f), r s = s := by
  set S := LinearMap.range (HTLat.Tate.map p f)
  have h1 : ∀ t, (p : ℤ_[p]) • t ∈ S → t ∈ S := by
    rintro t ⟨u, hu⟩
    have h : ∀ n, f (u.lev (n + 1)) = t.lev n := fun n => by
      rw [← HTLat.Tate.lev_map, hu, HTLat.Tate.lev_smul, PDiv.pow_digit_natCast (t.lev_pow _),
        t.lev_succ]
    exact ⟨HTLat.Tate.mk (fun n => u.lev (n + 1)) fun n =>
      ⟨hf (by rw [map_pow, h, t.lev_pow, map_one]), u.lev_succ _⟩, HTLat.Tate.ext h⟩
  have h2 : ∀ (n : ℕ) t, (p : ℤ_[p]) ^ n • t ∈ S → t ∈ S := fun n => by
    induction n with
    | zero => simp
    | succ n ih => exact fun t ht => h1 t (ih _ (by rwa [smul_smul, ← pow_succ]))
  haveI : Module.IsTorsionFree ℤ_[p] (HTLat.Tate p M' ⧸ S) := .of_smul_eq_zero fun a q h => by
    by_cases ha : a = 0
    · exact .inl ha
    obtain ⟨t, rfl⟩ := S.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      PadicInt.unitCoeff_spec ha, mul_smul] at h
    exact .inr ((Submodule.Quotient.mk_eq_zero _).2
      (h2 _ t ((S.smul_mem_iff' (PadicInt.unitCoeff ha)).1 h)))
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  refine ⟨(LinearMap.id - σ ∘ₗ S.mkQ).codRestrict S fun t => ?_, fun s => Subtype.ext ?_⟩
  · change s.1 - σ (S.mkQ s.1) = s.1
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 s.2, map_zero, sub_zero]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
    exact sub_eq_zero.2 (LinearMap.congr_fun hσ (S.mkQ t)).symm

theorem dual_ext {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] {q : O} (hq : q ≠ 0)
    {s : Set M} (hs : ∀ w : M, q • w ∈ Submodule.span O s) {y z : Module.Dual O M}
    (h : ∀ m ∈ s, y m = z m) : y = z := LinearMap.ext fun w => by
  have h1 : y (q • w) = z (q • w) := LinearMap.eqOn_span (s := s) h (hs w)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ hq h1

theorem cokernelBound_of_group : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) → (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) → Module.Finite O G.omega → Module.Free O G.omega → (∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G)))) → CokernelBound P := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P G e l c ζ hζ hpair hdlog hfin hfree hspan f
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : IsIntegrallyClosed O := P.integers.isIntegrallyClosed
  have hflip : Function.Bijective (pairT P.A P.eps).flip := by
    have h : (pairT P.A P.eps).flip = -pairT P.A P.eps :=
      LinearMap.ext₂ fun s t => ((isAlt_pairT P.A P.eps).neg_eq s t).symm
    rw [h]
    exact neg_bijective.comp P.pairT_bijective
  obtain ⟨r, hr⟩ : ∃ r : P.T →ₗ[ℤ_[p]] P.tateGt, ∀ s : P.tateGt, r s = s := by
    have h : Module.Finite ℤ_[p] P.T := inferInstance
    unfold Point.tateGt
    exact @exists_retraction_range p _ _ _ (_) (_) _ P.toA_injective h
  let u : ℤ_[p] ≃ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  have hc : Function.Surjective c := fun χ => by
    obtain ⟨t, ht⟩ := hflip.2
      (u.symm.toLinearMap ∘ₗ (pairing G O).flip χ ∘ₗ e.symm.toLinearMap ∘ₗ r)
    refine ⟨t, (PDivGroup.tate_free_perfect p O C G).2.2.2.2.2.2.2.1 (LinearMap.ext fun s => ?_)⟩
    have h1 : pairT P.A P.eps (e s : P.T) t = u.symm (pairing G O (e.symm (r (e s : P.T))) χ) :=
      LinearMap.congr_fun ht (e s : P.T)
    rw [hr, LinearEquiv.symm_apply_apply] at h1
    change pairing G O s (c t) = pairing G O s χ
    rw [hpair, h1]
    exact u.apply_symm_apply _
  have hp : (p : O) ^ 2 ≠ 0 := pow_ne_zero _ fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h1
  have hext : ∀ {y z : G.Lie}, (∀ t, y (dlog (G := G) (c t)) = z (dlog (G := G) (c t))) → y = z :=
    fun h => dual_ext hp hspan (by
      rintro _ ⟨χ, rfl⟩
      obtain ⟨t, rfl⟩ := hc χ
      exact h t)
  have hadd : ∀ x y, l (lieAdd x y) = l x + l y := fun x y => hext fun t => by
    rw [LinearMap.add_apply, hdlog, hdlog, hdlog, omega_lieAdd]
  have hsc : ∀ (a : O) x, l (AvDefs.lieScale P.Gt a x) = a • l x := fun a x => hext fun t => by
    rw [LinearMap.smul_apply, hdlog, hdlog, omega_lieScale, smul_eq_mul]
  let F : Module.Dual O (Module.Dual O G.omega) :=
    { toFun := fun y => f.1 (l.symm y)
      map_add' := fun y z => by
        rw [← omega_lieAdd, l.symm_apply_eq.2 ((hadd (l.symm y) (l.symm z)).trans
          (by rw [l.apply_symm_apply, l.apply_symm_apply])).symm]
      map_smul' := fun a y => by
        rw [RingHom.id_apply, smul_eq_mul, ← omega_lieScale,
          l.symm_apply_eq.2 ((hsc a (l.symm y)).trans (by rw [l.apply_symm_apply])).symm] }
  obtain ⟨w, hw⟩ := (Module.bijective_dual_eval O G.omega).2 F
  have hfw : ∀ x, l x w = f.1 x := fun x => by
    have h1 : l x w = f.1 (l.symm (l x)) := LinearMap.congr_fun hw (l x)
    rwa [l.symm_apply_apply] at h1
  have key : ∀ m ∈ Submodule.span O (Set.range (dlog (G := G))),
      ∃ g ∈ LinearMap.range P.al, ∀ x, l x m = g.1 x := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨χ, rfl⟩ := hm
      obtain ⟨t, rfl⟩ := hc χ
      exact ⟨P.al₀ t, ⟨1 ⊗ₜ t, by rw [Point.al_tmul, one_smul]⟩, fun x => hdlog x t⟩
    | zero => exact ⟨0, zero_mem _, fun x => map_zero _⟩
    | add m n _ _ hm hn =>
      obtain ⟨g, hg, h⟩ := hm
      obtain ⟨g', hg', h'⟩ := hn
      exact ⟨g + g', add_mem hg hg', fun x => by rw [map_add, h, h']; rfl⟩
    | smul a m _ hm =>
      obtain ⟨g, hg, h⟩ := hm
      exact ⟨a • g, Submodule.smul_mem _ a hg, fun x => by rw [map_smul, h]; rfl⟩
  obtain ⟨g, hg, h⟩ := key _ (hspan w)
  have h2 : (p : O) ^ 2 • f = g := Subtype.ext (funext fun x => by
    rw [← h, map_smul, hfw]; rfl)
  rw [h2]
  exact hg

end GlobalTheory.HodgeTateCokernel
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdiv_group_tate_lie_compat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) → (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) → Module.Finite O G.omega → Module.Free O G.omega → (∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G)))) → CokernelBound P := by
  atlas_forward_decl GlobalTheory.HodgeTateCokernel.cokernelBound_of_group
end

section
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HTLat.KerShape

theorem bLie_mem_W_and_tateGt (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
    [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ]
    (P : Point p v O Λ) [IsDomain O] (ε : PreTilt O p)
    (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε) (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε)
    (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie)
    (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate) (φ : G ⟶ G.dual)
    (hζ : Function.Bijective (fun a : ℤ_[p] => a • ζ))
    (hc : ∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ)
    (hl : ∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x)
    (hφ : ∀ s s' : G.Tate, pairing G O s (tateMap G G.dual O φ s') =
      pairT P.A P.eps (e s : P.T) (e s' : P.T) • ζ)
    (x : LieG P.Gt) : P.bLie x ∈ P.W ∧ P.bLie x ∈ P.tateGt.baseChange C := by
  obtain ⟨B, hB, hB1, hB2⟩ := GlobalTheory.PointGroup.exists_form P.integers G ζ hζ
  have hk : GlobalTheory.PointGroup.KerIsLie G B :=
    (GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear p C v O ε hε H G ζ B P.integers hζ hB).1
  obtain ⟨ξ, hξ0, hξ⟩ := GlobalTheory.PointGroup.exists_ker_of_lie P.integers hB1.2 hk (l x)
  let j : G.Tate →ₗ[ℤ_[p]] P.T := P.tateGt.subtype ∘ₗ e.toLinearMap
  have hBc : ∀ s t, B s (c t) = pairT P.A P.eps (j s) t := fun s t =>
    hζ.1 ((hB s (c t)).symm.trans (hc s t))
  have hcφ : ∀ s, c (j s) = tateMap G G.dual O φ s := fun s =>
    hB2.1 (LinearMap.ext fun s' => hζ.1
      ((hB s' _).symm.trans ((hc s' (j s)).trans ((hφ s' s).symm.trans (hB s' _)))))
  have h1 : ∀ (z : O ⊗[ℤ_[p]] G.Tate) t, P.pairV (P.inclT (j.baseChange O z)) (1 ⊗ₜ t) =
      algebraMap O C (TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O z)) := fun z t => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul a s =>
      rw [LinearMap.baseChange_tmul, Point.inclT_tmul, Point.pairV_tmul, LinearMap.baseChange_tmul,
        LinearMap.flip_apply, hBc, TensorProduct.rid_tmul, _root_.mul_one, Algebra.smul_def,
        Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have h2 : P.bLie x = P.inclT (j.baseChange O ξ) := P.eq_of_pairV fun t => by
    rw [h1, hξ, hl, Point.pairV_bLie]
  have h3 : ∀ χ, dlog G χ = omegaMap _ _ G.bidual.hom (hodgeTate G.dual χ) := fun χ => by
    rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap, ← LinearMap.comp_apply,
      ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply]
  have h4 : ∀ (z : O ⊗[ℤ_[p]] G.Tate) x', (P.al (j.baseChange O z)).1 x' =
      l x' (omegaMap _ _ G.bidual.hom (omegaDualMap G G.dual φ (G.hodgeTateLinear z))) :=
    fun z x' => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, Submodule.coe_add, Pi.add_apply, hx, hy]
      | tmul a s =>
        rw [LinearMap.baseChange_tmul, Point.al_tmul, hodgeTateLinear_tmul, map_smul, map_smul,
          map_smul, ← hodgeTate_tateMap, ← h3, ← hcφ, hl]
        rfl
  have h5 : P.al (j.baseChange O ξ) = 0 := Subtype.ext (funext fun x' => by
    rw [h4, hξ0, map_zero, map_zero, map_zero]
    rfl)
  rw [h2]
  refine ⟨?_, ?_⟩
  · change P.alC _ = 0
    rw [Point.alC_inclT, h5, map_zero]
  · clear hξ0 hξ h2 h5
    induction ξ using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul a s =>
      rw [LinearMap.baseChange_tmul, Point.inclT_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ (e s).2

end GlobalTheory.HTLat.KerShape
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_sandwich_point_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate) (φ : G ⟶ G.dual), Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) → (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) → (∀ s s' : G.Tate, pairing G O s (tateMap G G.dual O φ s') = pairT P.A P.eps (e s : P.T) (e s' : P.T) • ζ) → ∀ x : LieG P.Gt, P.bLie x ∈ P.W ∧ P.bLie x ∈ P.tateGt.baseChange C := by
  atlas_forward_decl GlobalTheory.HTLat.KerShape.bLie_mem_W_and_tateGt
end

section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HTLat.KerPerp

theorem eq_zero_of_forall_dual {O C M : Type} [CommRing O] [CommRing C] [Algebra O C]
    [AddCommGroup M] [Module O M] [Module.Free O M] (z : C ⊗[O] M)
    (h : ∀ l : Module.Dual O M, (Algebra.linearMap O C ∘ₗ l).liftBaseChange C z = 0) : z = 0 := by
  let b := Module.Free.chooseBasis O M
  refine (b.baseChange C).ext_elem fun i => ?_
  have e : (b.baseChange C).coord i = (Algebra.linearMap O C ∘ₗ b.coord i).liftBaseChange C := by
    refine LinearMap.ext fun w => ?_
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      rw [Module.Basis.coord_apply, Module.Basis.baseChange_repr_tmul,
        LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, Algebra.linearMap_apply,
        Module.Basis.coord_apply, Algebra.smul_def, smul_eq_mul, mul_comm]
  rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, e]
  exact h _

theorem mem_W_iff : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ x : P.V, x ∈ P.W ↔ ∀ y, P.pairV (P.bLie y) x = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P x
  obtain ⟨hf, -, hb⟩ := Point.omega_free_finite_bijective p C v O Λ P
  have key : ∀ y (w : P.V), P.pairV (P.bLie y) w =
      (Algebra.linearMap O C ∘ₗ ((LinearMap.proj y : (_ → O) →ₗ[O] O) ∘ₗ
        (omega P.Gt).subtype)).liftBaseChange C (P.alC w) := by
    intro y w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c t =>
      have e : (c ⊗ₜ[ℤ_[p]] t : P.V) = c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Point.alC_tmul, LinearMap.liftBaseChange_tmul, e, map_smul, Point.pairV_bLie]
      rfl
  constructor
  · intro hx y
    rw [key, show P.alC x = 0 from hx, map_zero]
  · intro h
    refine eq_zero_of_forall_dual (P.alC x) fun l => ?_
    obtain ⟨y, rfl⟩ := hb.2 l
    exact (key y x).symm.trans (h y)

end GlobalTheory.HTLat.KerPerp
end

section
section
open GlobalTheory GlobalTheory.HTLat TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HTLat.AnnKer

theorem annW_eq_span_bLie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), (∀ x : P.V, (∀ y ∈ P.W, P.pairV x y = 0) ↔ x ∈ Submodule.span C (Set.range P.bLie)) ∧ Module.finrank C (Submodule.span C (Set.range P.bLie)) + Module.finrank C P.W = 2 * P.A.g := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  set L := Submodule.span C (Set.range P.bLie) with hL
  have hWL : P.W = P.pairV.orthogonal L := by
    ext x
    rw [KerPerp.mem_W_iff p C v O Λ P x, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h n hn
      have : L ≤ LinearMap.ker (P.pairV.flip x) := Submodule.span_le.2 (by
        rintro _ ⟨z, rfl⟩
        exact h z)
      exact this hn
    · intro h y
      exact h _ (Submodule.subset_span ⟨y, rfl⟩)
  have hl : ∀ w : P.V, (∀ y, P.pairV w y = 0) → w = 0 := fun w hw =>
    P.eq_of_pairV fun t => by rw [hw, map_zero, LinearMap.zero_apply]
  have hnd : P.pairV.Nondegenerate :=
    ⟨hl, fun w hw => hl w fun y => by rw [P.pairV_swap, hw, neg_zero]⟩
  have hrefl : P.pairV.IsRefl := fun x y h => by rw [P.pairV_swap, h, neg_zero]
  refine ⟨fun x => ?_, ?_⟩
  · rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl L, ← hWL,
      LinearMap.BilinForm.mem_orthogonal_iff]
    refine ⟨fun h n hn => ?_, fun h y hy => ?_⟩
    · exact hrefl _ _ (h n hn)
    · exact hrefl _ _ (h y hy)
  · have ho := LinearMap.BilinForm.finrank_orthogonal hnd L
    rw [← hWL, P.finrank_V] at ho
    have hle : Module.finrank C L ≤ 2 * P.A.g := P.finrank_V ▸ Submodule.finrank_le L
    omega

end GlobalTheory.HTLat.AnnKer
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_kernel_annihilator : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), (∀ x : P.V, (∀ y ∈ P.W, P.pairV x y = 0) ↔ x ∈ Submodule.span C (Set.range P.bLie)) ∧ Module.finrank C (Submodule.span C (Set.range P.bLie)) + Module.finrank C P.W = 2 * P.A.g := by
  atlas_forward_decl GlobalTheory.HTLat.AnnKer.annW_eq_span_bLie
end

section
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HTLat.KernelDim

section

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C]
  [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem range_alC (h : CokernelBound P) : LinearMap.range P.alC = ⊤ := by
  have hp : ((p : C) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine eq_top_iff.2 fun y hy => ?_
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul c f =>
    obtain ⟨x, hx⟩ := h f
    refine ⟨(c / (p : C) ^ 2) • P.inclT x, ?_⟩
    rw [map_smul, P.alC_inclT, hx, Point.inclOm, TensorProduct.mk_apply, ← TensorProduct.smul_tmul,
      TensorProduct.smul_tmul', Algebra.smul_def ((p : O) ^ 2), map_pow, map_natCast, smul_eq_mul,
      _root_.mul_one, div_mul_cancel₀ _ hp]

theorem finrank_OmC : Module.finrank C P.OmC = P.A.g := by
  haveI := P.isLocalRing
  haveI := (Point.omega_free_finite_bijective p C v O Λ P).1
  rw [Module.finrank_baseChange, OmegaRank.finrank_omega_Gt p C v O Λ P]

end

theorem finrank_W : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), CokernelBound P → Module.finrank C P.W = P.A.g := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P h
  have h₁ := LinearMap.finrank_range_add_finrank_ker P.alC
  rw [range_alC P h, finrank_top, finrank_OmC, P.finrank_V] at h₁
  change Module.finrank C (LinearMap.ker P.alC) = _
  omega

end GlobalTheory.HTLat.KernelDim
end

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_W_eq_dimension : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), CokernelBound P → Module.finrank C P.W = P.A.g := by
  atlas_forward_decl GlobalTheory.HTLat.KernelDim.finrank_W
end

section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_torus_le_lie_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), P.tateTorus.baseChange C ≤ Submodule.span C (Set.range P.bLie) := by
  first | exact @GlobalTheory.TorusTateLie.tateTorus_le_span_bLie | exact GlobalTheory.TorusTateLie.tateTorus_le_span_bLie | (intros; apply GlobalTheory.TorusTateLie.tateTorus_le_span_bLie <;> assumption)
end

section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_finrank_of_cokernel : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), CokernelBound P → P.W = Submodule.span C (Set.range P.bLie) → ∀ τ : Λ →+* O, Module.finrank C (P.eigW τ) = AvDefs.rTau P.Gt P.oGt τ := by
  first | exact @GlobalTheory.HodgeTateEigenRank.finrank_eigW | exact GlobalTheory.HodgeTateEigenRank.finrank_eigW | (intros; apply GlobalTheory.HodgeTateEigenRank.finrank_eigW <;> assumption)
end

section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HTKernel

theorem hodgeTateKernelAtPoint_of_dieudonne (h : GlobalTheory.Published.PrismaticDieudonneHodge) :
    GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hv := P.integers
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨ε, hε₁⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C _ O hv
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε := GlobalTheory.PrismModel.isPrimitiveSystem_of_one hε₁
  have hS := GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ h p C v O hv ε hε
  obtain ⟨G, e, l, c, ζ, tw, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_pdiv_group_tate_lie p C v O Λ P
  obtain ⟨hf, hfr, hb⟩ := GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span p C v O ε hε hv hS G
  have hcok : CokernelBound P := GlobalTheory.T.pdiv_group_tate_lie_compat p C v O Λ P G e l c ζ h1 h2 h3 hf hfr hb
  have hint : WeilIntegralFinite P := GlobalTheory.T.weil_integral_local_to_finite p C v O Λ P (GlobalTheory.T.weil_pairing_integral p C v O Λ P (GlobalTheory.T.polarized_abelian_cube_function C P.A)
    (GlobalTheory.T.trivialising_open_exists p C v O Λ P (GlobalTheory.T.special_fibre_not_in_closure p C v O hv)) (GlobalTheory.T.translates_into_holds p C v O Λ P)
    (GlobalTheory.T.cube_values_integral p C v O Λ P (GlobalTheory.T.local_units_holds p C v O hv)))
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_polarization_torsion_tower p C v O Λ P hint G tw
  have hiso := GlobalTheory.T.hodge_tate_sandwich_point_property p C v O Λ P ε hε hS G e l c ζ φ h1 h2 h3 fun s s' => muRoot_ext fun n =>
    hv.hom_inj (by
      rw [hφ, muRoot_smul, map_pow, h5, ← h4, ← h4, ← pow_pairT P.A P.eps, Units.val_pow_eq_pow_val])
  obtain ⟨horth, hrank⟩ := GlobalTheory.T.hodge_tate_kernel_annihilator p C v O Λ P
  have hdim := GlobalTheory.T.finrank_W_eq_dimension p C v O Λ P hcok
  have hle : Submodule.span C (Set.range P.bLie) ≤ P.W :=
    Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact (hiso x).1)
  have hW : P.W = Submodule.span C (Set.range P.bLie) :=
    (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  refine ⟨GlobalTheory.T.level_reduction_holds p C v O Λ P, (weilChar_surjective_and_map_range_al p C v O Λ P).1, hcok, hdim,
    fun a x hx => ?_, hW ▸ GlobalTheory.T.tate_torus_le_lie_span p C v O Λ P, ?_, fun x => ?_, GlobalTheory.T.eigen_finrank_of_cokernel p C v O Λ P hcok hW, hW⟩
  · change P.alC _ = 0
    rw [P.isEquivariant_alC a x, show P.alC x = 0 from hx, map_zero]
  · rw [hW]
    exact Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact (hiso x).2)
  · rw [horth, ← hW]

theorem hodgeTateKernelAtPoint : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint :=
  fun h => hodgeTateKernelAtPoint_of_dieudonne h.q4

end GlobalTheory.HTKernel
end
