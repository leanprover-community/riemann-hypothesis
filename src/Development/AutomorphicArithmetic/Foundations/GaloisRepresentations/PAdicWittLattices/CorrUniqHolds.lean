import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvariStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BocksteinReductionCommutesWithRestriction
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
import Development.EtaleCohomology.WeilConjectures.ContinCut
import Development.EtaleCohomology.WeilConjectures.FinQCut
import Development.EtaleCohomology.WeilConjectures.AdicKerPf
import Development.EtaleCohomology.EtaleDuality.FinAdicFin
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism
import Development.EtaleCohomology.WeilConjectures.AbsContPf
import Development.EtaleCohomology.WeilConjectures.ChevPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAicLocalSubring
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AffineProperBaseChange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace UpperTheory.Gal.G3

theorem vFin_holds : GlobalTheory.GalV.VFin := by
  intro l _ k _ _ hl X p _ n i
  have hT : ∀ a m, Finite (Ht (l ^ a) (sch.obj X) m i) := fun a m => by
    have : NeZero (l ^ a) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact UpperTheory.Et.etale_finiteness_of_duality (l ^ a) k (by rw [Nat.cast_pow]; exact hl.pow a) p m i
  have hM : Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) :=
    LateralTheory.EWeil.AdicFinPf.AdicFin_of l _ n i (fun a => hT a n)
      (LateralTheory.EWeil.AdicKerPf.AdicKer_of GlobalTheory.EtC.RedCoef.a11 l _ i
        (fun b => LateralTheory.Fin.AdicFin.etale_bockstein_sequence_adic_finiteness GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 l b _ i
          (LateralTheory.EWeil.FinQCut.inv_of_over hl p)) hT n)
  exact ⟨hM, Module.Finite.base_change ℤ_[l] ℚ_[l] _⟩

end UpperTheory.Gal.G3

end
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3 MorphismProperty
universe u v

set_option backward.isDefEq.respectTransparency.types false in
private theorem isProper_desc {A G U Z : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hUC : UniversallyClosed g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (UniversallyClosed f))
  have hLFT : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (LocallyOfFiniteType f))
  have hD : MorphismProperty.diagonal @UniversallyClosed g := by
    refine of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hQ ?_
    rw [MorphismProperty.diagonal_iff]
    infer_instance
  rw [MorphismProperty.diagonal_iff] at hD
  have hP : IsProper (pullback.diagonal g) := IsProper.mk
  have hC : IsClosedImmersion (pullback.diagonal g) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hP, inferInstance⟩
  haveI : IsSeparated g := ⟨hC⟩
  exact IsProper.mk

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc_fin (W : Scheme.{0}) (n : ℕ) :
    IsFinite (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
  induction n with
  | zero =>
    haveI := Function.isEmpty (sigmaMk (fun _ : Fin 0 => W)).symm
    infer_instance
  | succ n ih =>
    let t := extendCofanIsColimit (fun _ : Fin (n + 1) => W) (coproductIsCoproduct fun _ : Fin n => W)
      (coprodIsCoprod W (∐ fun _ : Fin n => W))
    let e : (∐ fun _ : Fin (n + 1) => W) ≅ W ⨿ (∐ fun _ : Fin n => W) :=
      (coproductIsCoproduct fun _ : Fin (n + 1) => W).coconePointUniqueUpToIso t
    have key : (Sigma.desc (f := fun _ : Fin (n + 1) => W) fun _ => 𝟙 W) =
        e.hom ≫ coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
      refine Sigma.hom_ext _ _ fun j => ?_
      have hj := IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct (fun _ : Fin (n + 1) => W)) t ⟨j⟩
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [hj]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_zero]
        exact (coprod.inl_desc _ _).symm
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_succ]
        show 𝟙 W = (Sigma.ι (fun _ : Fin n => W) i ≫ coprod.inr) ≫
          coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W)
        rw [Category.assoc, coprod.inr_desc, Sigma.ι_desc]
    rw [key]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc (W : Scheme.{0}) (J : Type) [Finite J] :
    IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have key : (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) =
      (Sigma.reindex e.symm (fun _ : J => W)).inv ≫ (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, ← Category.assoc]
    have h := Sigma.ι_reindex_inv e.symm (fun _ : J => W) (e j)
    simp only [Equiv.symm_apply_apply] at h
    rw [h]
    exact (Sigma.ι_desc (f := fun _ : Fin n => W) (fun _ => 𝟙 W) (e j)).symm
  rw [key]
  haveI := isFinite_desc_fin W n
  infer_instance

private theorem locallyQuasiFinite_of_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  have hf : affineLocally RingHom.Etale f := by
    rw [← HasRingHomProperty.eq_affineLocally @Etale]
    exact ‹Etale f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine affineLocally_le (fun {R S} _ _ {g} hg => ?_) f hf
  letI : Algebra R S := RingHom.toAlgebra g
  have : Algebra.Etale R S := hg
  show Algebra.QuasiFinite R S
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
theorem UpperTheory.Gal.G3.jSplitDesc :
    SplitDesc := by
  intro Z Y W s c _ _ _ J _ σ hs
  obtain ⟨hσ, hiso⟩ := hs
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have key : pullback.snd s c =
      inv (Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hσ j, Category.id_comp])) ≫
        Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc, pullback.lift_snd, Sigma.ι_desc]
  haveI : IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := isFinite_desc W J
  haveI : Etale (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  haveI : IsFinite (pullback.snd s c) := by rw [key]; infer_instance
  haveI : Etale (pullback.snd s c) := by rw [key]; infer_instance
  have hpb := IsPullback.of_hasPullback s c
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) c :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : IsProper s := isProper_desc hpb
  have hE : Etale s := of_isPullback_of_descendsAlong hpb.flip hQ (inferInstanceAs (Etale (pullback.snd s c)))
  haveI := hE
  haveI := locallyQuasiFinite_of_etale s
  exact ⟨(IsFinite.iff_isProper_and_locallyQuasiFinite s).mpr ⟨inferInstance, inferInstance⟩, hE⟩
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.G3

private theorem prim_isEmpty {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {V : Scheme.{0}} (v : V) (f : V ⟶ sp k) :
    IsEmpty (Prim q Γ(V, ⊤)) := by
  constructor
  rintro ⟨ζ, hu, -⟩
  have h0 : ((q : ℕ) : Γ(sp k, ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom,
      show ((q : ℕ) : CommRingCat.of k) = 0 from hq, map_zero]
  have h1 : ((q : ℕ) : Γ(V, ⊤)) = 0 := by
    rw [← map_natCast f.appTop.hom, h0, map_zero]
  rw [h1] at hu
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  exact not_isUnit_zero hu

private theorem sec_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) (i : ℤ) {U : Scheme.{0}} (f : U ⟶ sp k) :
    Subsingleton (Sec (tw q i) U) := by
  suffices h : ∀ x : Sec (tw q i) U, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  let S : Sieve U :=
    { arrows := fun V j => Sec.res j x = 0
      downward_closed := by
        intro V W j hj g
        have hj' : ModuleCat.Hom.hom ((tw q i).obj.map j.op) x = 0 := hj
        show ModuleCat.Hom.hom ((tw q i).obj.map (g ≫ j).op) x = 0
        rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hj', map_zero] }
  have hS : S ∈ Scheme.etaleTopology U := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨V, j, v, m, -, hj, hv, hm⟩ := (GlobalTheory.ofRings_loc (ZMod q) (twF q i) U).1 x u
    refine ⟨V, j, v, hj, hv, ?_⟩
    refine hm.symm.trans ?_
    haveI : IsEmpty (Prim q Γ(V, ⊤)) := prim_isEmpty hq v (j ≫ f)
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q i Γ(V, ⊤)) m
    rw [Subsingleton.elim g 0, Submodule.Quotient.mk_zero]
    exact map_zero _
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (J := Scheme.etaleTopology) (P' := (tw q i).obj)
      (forget (ModuleCat.{1} (ULift.{1, 0} (ZMod q))))).mp (tw q i).cond)
  exact (hsh S hS).isSeparatedFor (fun _ _ _ => 0) x 0 (fun V j hj => hj)
    (fun V j hj => show ModuleCat.Hom.hom ((tw q i).obj.map j.op) 0 = 0 from map_zero _)

private theorem ht_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {X : Scheme.{0}} (p : X ⟶ sp k) (n i : ℤ) :
    Subsingleton (Ht q (sch.obj X) n i) := by
  have hbij := GlobalTheory.T.etaleCohomology_bijective_of_support_bijective (ZMod q) (sch.obj X) (0 : tw q i ⟶ tw q i) (fun U hU => by
    obtain ⟨g⟩ := hU
    have g' : U ⟶ X := g
    haveI := sec_subsingleton hq i (g' ≫ p)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨b, Subsingleton.elim _ _⟩⟩) n
  have hz : HK.post (ZMod q) ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) n = 0 := by
    have h := PostFun.post_add ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) 0 n
    rw [add_zero] at h
    exact left_eq_add.1 h
  refine ⟨fun a b => hbij.1 ?_⟩
  rw [hz]; rfl

theorem jCharVan : CharVan := by
  intro l _ k _ hl X x n i
  have hs : ∀ m : ℕ, Subsingleton (Ht (l ^ (m + 1)) (sch.obj X) n i) := fun m =>
    ht_subsingleton (k := k) (by push_cast; rw [hl, zero_pow (Nat.succ_ne_zero m)]) x n i
  constructor
  intro a b
  apply Subtype.ext
  funext m
  cases m with
  | zero =>
    rw [← a.2 0, ← b.2 0]
    congr 1
    exact (hs 0).elim _ _
  | succ m => exact (hs m).elim _ _

end UpperTheory.Gal.G3

end
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem htot_subsingleton (l : ℕ) [Fact l.Prime] (E : Spc)
    (h : ∀ n : ℤ, Subsingleton (Hl l E n 0)) : Subsingleton (Htot l E) := by
  have hq : ∀ n : ℤ, Subsingleton (HQ l E n 0) := fun n => by
    have := h n
    refine ⟨fun a b => ?_⟩
    have z : ∀ c : HQ l E n 0, c = 0 := fun c => by
      induction c using TensorProduct.induction_on with
      | zero => rfl
      | tmul q y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add c d hc hd => rw [hc, hd, add_zero]
    rw [z a, z b]
  exact ⟨fun a b => DFinsupp.ext fun n => (hq n).elim _ _⟩

private theorem op_eq (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (p : Z ⟶ sp k)
    (s : Y ⟶ Z) (t : Y ⟶ Z') (hT : (et l (sp k)).Good)
    (tr : (et l (sp k)).H (s ≫ p) →ₗ[ℚ_[l]] (et l (sp k)).H p) (htr : (et l (sp k)).IsTr p (s ≫ p) s tr)
    (A : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (hA : IsCorrOp l s t A)
    (x : Htot l (sch.obj Z')) : A x = tr (pullTot l (sch.map t) x) := by
  obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, hx⟩ := hA
  have hσ : ∀ j, σ j ≫ s ≫ p = c ≫ p := fun j => by
    rw [← Category.assoc, hsp.choose j]
  have hinj := hT.inj p (c ≫ p) c rfl G a hgal
  apply hinj
  have e := htr W (c ≫ p) c rfl J σ hσ hsp (pullTot l (sch.map t) x)
  refine Eq.trans ?_ e.symm
  refine (hx x).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Functor.map_comp, pullTot_comp]
  rfl

theorem UpperTheory.Gal.G3.jCorrUniq :
    EtGood → SplitDesc → CharVan → CorrUniq := by
  intro hG hD hV l _ k _ Z Y Z' p s t A A' hA hA'
  by_cases hl : (l : k) = 0
  · have := htot_subsingleton l (sch.obj Z) fun n => hV l k hl p n 0
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  · have hu : IsUnit (l : Γ(sp k, ⊤)) := by
      have h : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (l : k)) := (IsUnit.mk0 _ hl).map _
      rwa [map_natCast] at h
    have hT := hG l (sp k) hu
    obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, -⟩ := id hA
    obtain ⟨hf, he, hs, -, -, -⟩ := hgal
    obtain ⟨_, _⟩ := @hD Z Y W s c hf he hs J _ σ hsp
    obtain ⟨tr, htr⟩ := hT.tr p (s ≫ p) s rfl
    exact LinearMap.ext fun x => (op_eq l k p s t hT tr htr A hA x).trans (op_eq l k p s t hT tr htr A' hA' x).symm
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jVBcS :
    VBcS := by
  intro l _ k Ω _ _ _ _ φ hl X p _ _ n i
  refine GlobalTheory.GenusTwoPureComparison.Cmp.pullHQ_bijective l _ n i fun m => ?_
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ m : ℕ) : k) := by
    push_cast
    exact hl.pow m
  exact GlobalTheory.GenusTwoPureComparison.Cmp.eqv_fieldChange UpperTheory.Et.proper_base_change UpperTheory.Et.etale_base_change_of_duality (l ^ m) k Ω φ hq p i n
end

section
namespace UpperTheory.Gal.G3

theorem etnGood' : EtnGood := pEtnGood (pFEtBasic pPtsOfSplits) pEtTr

theorem corrUniq_holds : CorrUniq := jCorrUniq (pEtGood etnGood') jSplitDesc jCharVan

theorem vBcS_holds : VBcS := jVBcS

theorem vInv_holds : GlobalTheory.GalV.VInv := fun l _ _ _ f _ _ _ G _ a ha hiso n i => GlobalTheory.T.pullbackLAdicRationalCohomology_galoisCover_invariants l f G a ha hiso n i

end UpperTheory.Gal.G3
end
