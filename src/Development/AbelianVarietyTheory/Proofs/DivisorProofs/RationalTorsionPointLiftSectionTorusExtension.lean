import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatTorsionIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTorsMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisFixedSectionExtension

theorem extend_section {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of V)) [IsFinite p] (g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ s = g := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ X.isoSpec.hom)
  obtain ⟨π, hπ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  have hfin : π.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hπ]
    infer_instance
  have hcomp : π ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hπ, Category.assoc, Iso.hom_inv_id_assoc, hg]
  have hc : ∀ v : V, φ.hom (π.hom v) = algebraMap V (FractionRing V) v := fun v =>
    congrArg (fun f => f.hom v) hcomp
  have hmem : ∀ a, φ.hom a ∈ (algebraMap V (FractionRing V)).range := by
    intro a
    obtain ⟨q, hq, hqa⟩ := hfin.to_isIntegral a
    have hint : IsIntegral V (φ.hom a) := by
      refine ⟨q, hq, ?_⟩
      have h1 := Polynomial.hom_eval₂ q π.hom φ.hom a
      rw [hqa, map_zero] at h1
      have h2 : φ.hom.comp π.hom = algebraMap V (FractionRing V) := RingHom.ext hc
      rw [h2] at h1
      exact h1.symm
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap V (FractionRing V)).rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* V := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  have hψ : ∀ a, algebraMap V (FractionRing V) (ψ a) = φ.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict _ hmem a))
  have hψφ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V (FractionRing V)) = φ := by
    ext a
    exact hψ a
  have hπψ : π ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
    ext v
    exact hinj ((hψ _).trans (hc v))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hπ, ← Spec.map_comp, hπψ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψφ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem exists_section_of_galoisFixed : ∀ (V : Type) [inst : CommRing V] [inst_1 : IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)), AlgebraicGeometry.IsFinite (CategoryTheory.Over.hom N) → ∀ (nb : ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ (σ : Gal(AlgebraicClosure (FractionRing V)/FractionRing V)), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (AlgHom.toRingHom (↑σ : AlgebraicClosure (FractionRing V) →ₐ[FractionRing V] AlgebraicClosure (FractionRing V)))) (CategoryTheory.Over.Hom.left nb) = CategoryTheory.Over.Hom.left nb) → ∃ (s : CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)) ⟶ N), nb = CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartesianMonoidalCategory.toUnit (ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)))) s := by
  intro V _ _ _ hV N hN nb hfix
  haveI := hV
  haveI := hN
  haveI : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨g, hg⟩ := GlobalTheory.TorsDescent.descend_point (K := FractionRing V) N.left nb.left hfix
  have hg' : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ g =
      nb.left := hg
  have hw : nb.left ≫ N.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := Over.w nb
  have hgp : g ≫ N.hom = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (g ≫ N.hom)
    rw [← hχ]
    congr 1
    have h1 : χ ≫ CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        CommRingCat.ofHom (algebraMap V (FractionRing V)) ≫
          CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, hχ, ← hw, ← hg', Category.assoc]
    ext v
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective
      (congrArg (fun f => f.hom v) h1)
  obtain ⟨s, hs, hsg⟩ := extend_section N.left N.hom g hgp
  refine ⟨Over.homMk s hs, ?_⟩
  apply Over.OverMorphism.ext
  show nb.left = (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) ≫ s
  rw [Category.assoc, hsg, hg']

end GlobalTheory.GaloisFixedSectionExtension
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FinDescent

theorem galoisFixed_point_of_finite : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first
  | exact @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | (apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed ..)

end GlobalTheory.FinDescent
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_invariant_point_descends_to_section : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first | exact @GlobalTheory.FinDescent.galoisFixed_point_of_finite | exact GlobalTheory.FinDescent.galoisFixed_point_of_finite | (intros; apply GlobalTheory.FinDescent.galoisFixed_point_of_finite <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.TorsLift

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem gtTors_toT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (g : GtPtF D F) (h : k • g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k (GlobalTheory.FieldRestrictionTest.toT g) := by
  obtain ⟨gs, h0, hs, hl⟩ := (GlobalTheory.TorusExt.isNsmul_iff_eq k g (k • g)).2 rfl
  refine ⟨GlobalTheory.FieldRestrictionTest.toT (k • g),
    ⟨fun i => GlobalTheory.FieldRestrictionTest.toT (gs i), h0, fun i => hs i, congrArg GlobalTheory.FieldRestrictionTest.toT hl⟩, ?_⟩
  exact (GlobalTheory.FieldRestrictionTest.isZero_toT _).2 ((GlobalTheory.TorusExt.isZero_iff_eq _).2 h)

theorem inj (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hR : GlobalTheory.Mum.Base V)
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (D : DegData V (maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp V))
    (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G) (hfin : IsFinite N.hom) (hg₀ : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k g₀)
    (huniv : ∀ (T : Over (Sp V)) (g : GtPt D.toPre T), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g)
    (htors : x₀ ^ k = 1) (hform : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (n n' : TF (R := V) F ⟶ N)
    (h : n.left ≫ x₀.left = n'.left ≫ x₀.left) : n = n' := by
  have hB := D.tau_bimult
  haveI : IsNoetherianRing V := hR.1.1
  have : CharZero V := hR.2
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hR.1 D A G hG U F k hk
  have key : ∀ m : TF (R := V) F ⟶ N, ∃ q : GtPtF D.toPre F, GtPt.IsPullF F m.left g₀ q ∧
      ∃ hq : k • q = GlobalTheory.TorusExt.iota hB F 0,
        (f (GlobalTheory.TorusExt.qkMk hB 0 q hq)).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = m.left ≫ x₀.left := by
    intro m
    obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF m g₀
    obtain ⟨h0, hn, hz⟩ := hg₀
    obtain ⟨h0', hh0'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF m h0
    have hk' : k • q = GlobalTheory.TorusExt.iota hB F 0 := by
      rw [map_zero, ← (GlobalTheory.TorusExt.isNsmul_iff_eq k q h0').1 (GlobalTheory.FieldRestrictionTest.isNsmul_restrict hq hh0' hn)]
      exact (GlobalTheory.TorusExt.isZero_iff_eq _).1 (GlobalTheory.FieldRestrictionTest.isZero_restrict hh0' hz)
    obtain ⟨a, ha, hqa⟩ := GlobalTheory.ToricTorsionUnif.generic V hR G hG D A U k hk N g₀ x₀ hfin htors hform F m.left
      (Over.w m) (GlobalTheory.TorusExt.qkMk hB 0 q hk') rfl hq
    exact ⟨q, hq, hk', by rw [← (hf.1 _ a).1 hqa]; exact ha⟩
  obtain ⟨q, hq, hk1, e1⟩ := key n
  obtain ⟨q', hq', hk2, e2⟩ := key n'
  have hff : f (GlobalTheory.TorusExt.qkMk hB 0 q hk1) = f (GlobalTheory.TorusExt.qkMk hB 0 q' hk2) := by
    rw [← cancel_mono U.gen.inv]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, e1, h, e2]
    · exact (Over.w (f (GlobalTheory.TorusExt.qkMk hB 0 q hk1) ≫ U.gen.inv)).trans
        (Over.w (f (GlobalTheory.TorusExt.qkMk hB 0 q' hk2) ≫ U.gen.inv)).symm
  obtain ⟨z, hz1, hz2⟩ := (GlobalTheory.TorusExt.equiv_iff hB _ _).1 ((hf.2.2.1 _ _).1 hff)
  have hz : z = 0 := by
    have h1 : k • z = 0 := by
      have := hz1.symm
      simpa using this
    have h2 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left (by omega)
  have hqq : q' = q := by
    have := hz2
    simpa [hz] using this
  subst hqq
  have ht : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k (GlobalTheory.FieldRestrictionTest.toT q') :=
    GlobalTheory.TorsionFormCompare.tors_of_isPull n hq hg₀
  obtain ⟨_, _, hu⟩ := huniv _ _ ht
  exact (hu n hq).trans (hu n' hq').symm

theorem lift : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A) (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N), xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ x.left → p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → ∃ (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), h ^ N = 1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors N g ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g ∧ IntTerm.Ext U.toUnifPre x h ∧ GtPt.IsPullF (AlgebraicClosure (FractionRing V)) (toUnit (TF (R := V) (AlgebraicClosure (FractionRing V)))).left g p.g := by
  intro V _ _ _ hV D A G _ _ hG U N hN x xb p hxb hy hp
  have : CharZero V := hV.2.2.2
  haveI : IsNoetherianRing V := hV.1
  have hR : GlobalTheory.Mum.Base V := ⟨admissibleBase_of_completeNormalLocalCharZero hV, hV.2.2.2⟩
  obtain ⟨M, g₀, x₀, hfin, -, hg₀, huniv, hx₀, hform⟩ :=
    GlobalTheory.ToricTorsionUnif.exists_torsion_toG V hR G D A U N hN
  have hB := D.tau_bimult
  have hkg : N • p.g = 0 := by rw [GlobalTheory.TorusExt.qk_nsmul hB p, hy, map_zero]
  obtain ⟨nb, hnb, -⟩ := huniv _ _ (gtTors_toT p.g hkg)
  obtain ⟨a, ha, hqa⟩ := GlobalTheory.ToricTorsionUnif.generic V hR G hG D A U N hN M g₀ x₀ hfin hx₀ hform
    (AlgebraicClosure (FractionRing V)) nb.left (Over.w nb) p hy hnb
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) (admissibleBase_of_completeNormalLocalCharZero hV) D A G hG U
    (AlgebraicClosure (FractionRing V)) N hN
  have hax : a = xb := ((hf.1 p a).1 hqa).trans ((hf.1 p xb).1 hp).symm
  have hnx : nb.left ≫ x₀.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫
      x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) := by
    rw [← ha, hax, hxb, Category.assoc]
  have hfix : ∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V),
      spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left := by
    intro σ
    have hσ : spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => σ.commutes r
    let n' : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ M :=
      Over.homMk (spMap σ.toAlgHom.toRingHom ≫ nb.left) (by
        rw [Category.assoc, Over.w nb]
        show spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jK V = _
        rw [reassoc_of% hσ]; rfl)
    have e := inj V hR G hG D A U N hN M g₀ x₀ hfin hg₀ huniv hx₀ hform (AlgebraicClosure (FractionRing V)) n' nb
      (by
        show (spMap σ.toAlgHom.toRingHom ≫ nb.left) ≫ x₀.left = _
        rw [Category.assoc, hnx, reassoc_of% hσ])
    exact congrArg (·.left) e
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_invariant_point_descends_to_section V hV.2.1 M hfin nb hfix
  obtain ⟨g, hg⟩ := GlobalTheory.ConstLie.exists_isPull s g₀
  refine ⟨s ≫ x₀, g, ?_, GlobalTheory.TorsionFormCompare.tors_of_isPull s hg hg₀,
    (GlobalTheory.TorsionFormCompare.formalEq_iff _ _ _).2 (((GlobalTheory.TorsionFormCompare.formalEq_iff _ _ _).1 hform).pull s hg),
    ?_, ?_⟩
  · rw [← MonObj.comp_pow, hx₀, MonObj.comp_one]
  · show x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = (toUnit (TF (R := V) (FractionRing V)) ≫ s ≫ x₀).left
    apply GlobalTheory.OnePoint.point_ext (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))
    rw [← hnx, hs, Over.comp_left, Over.comp_left, Over.comp_left]
    simp only [← Category.assoc]
    congr 2
    have e1 : ∀ X : Over (Sp V), (toUnit X).left = X.hom := fun X => by simp
    rw [e1, e1]
    show jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) ≫ jK V
    rw [← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (AlgebraicClosure (FractionRing V)))) g
    have h2 := GlobalTheory.FlatTors.TorsMapExists.isPullF_trans hg hq
    rw [← Over.comp_left, ← hs] at h2
    rwa [GlobalTheory.FieldRestrictionTest.isPullF_unique h2 hnb] at hq

end GlobalTheory.Poinc.TorsLift
end
end
