import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced

section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

theorem exists_sFam_primePow_sq :
    ∀ g l : ℕ, 1 ≤ g → l.Prime → Odd l →
      ∃ j : ℕ, 1 ≤ j ∧ Nonempty (SFam g ((l ^ j) ^ 2) (zetaAway ((l ^ j) ^ 2))) := by
  intro g l hg hl _hodd
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hLaws hLaws2 GlobalTheory.Moduli.cube_of_isLB
    GlobalTheory.thetaUnifAV_closed g l hg hl _hodd

  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have hn : (l ^ max j₀ 1) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl.ne_zero)

  have key := hj₀ (max j₀ 1) (le_max_left _ _) (cycAway ((l ^ max j₀ 1) ^ 2)) (cycBase hn)
    (cycAway ((l ^ max j₀ 1) ^ 2)).subtype (arBase_cycAway _ hn)
  rwa [cycBase_ζ hn] at key

end GlobalTheory.SiegelTor
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegLev

section
variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h n ζ s}
  {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {d d' d'' : ℕ}

theorem sRel_trans (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c d' d f) (e : ℕ) : SRel c' c (d' * e) (d * e) f :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.2 e

end

theorem spMap_id_eq (o : Type) [CommRing o] : spMap (RingHom.id o) = 𝟙 _ := Spec.map_id _

theorem sFam_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N →
    Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  intro h n N o _ _ b hn hN hnN ⟨F⟩
  set ζ : o := (b.ζ : o) ^ (N / n)

  obtain ⟨c₀, h₀₁, h₀₂⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X F.X (F.s ≫ spMap (RingHom.id o)) F.s (𝟙 _) rfl
    (by simp)).2.2 F.univ
  have r₀₁ : SRel F.univ c₀ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₁
  have r₀₂ : SRel c₀ F.univ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₂
  have p₀ : c₀.Principal := sRel_principal r₀₂ F.princ
  obtain ⟨S₁, π, C, hfin, het, hsurj, hlow, huniv⟩ :=
    GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover h n N o o ζ b (RingHom.id o) F.X F.s c₀ hn hN hnN rfl p₀
  have hN0 : N ≠ 0 := hN.pos.ne'
  have pC : C.Principal := sRel_principal hlow p₀
  refine ⟨{
    X := S₁
    s := π ≫ F.s
    smooth := by
      haveI := F.smooth
      have := smoothOfRelativeDimension_comp 0 (h * (h + 1) / 2) π F.s
      rwa [zero_add] at this
    qproj := GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase o _ _ π F.s hfin F.qproj
    univ := C
    princ := pC
    rep := ?_
    inj := ?_ }⟩
  · intro T s' c hred hdense hp
    obtain ⟨cl, hcl1, hcl2⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o ζ (b.ζ : o) (RingHom.id o) T s' c hN0 b.unit hnN rfl
    have pl : cl.Principal := sRel_principal hcl2 hp
    obtain ⟨f, hf, hfp⟩ := F.rep T (s' ≫ spMap (RingHom.id o)) cl hred
      (by rw [spMap_id_eq, Category.comp_id]; exact hdense) pl
    rw [spMap_id_eq, Category.comp_id] at hf
    subst hf
    have r1 : SRel c F.univ (N / n) 1 (𝟙 _ ≫ f) := sRel_trans ((sRel_one_one_iff _ _ _).2 hfp) hcl1
    have r2 : SRel c c₀ (N / n) 1 ((𝟙 _ ≫ f) ≫ 𝟙 _) := sRel_trans r₀₁ r1
    obtain ⟨t₁, ⟨ht₁, hC⟩, -⟩ := huniv T f c (by simpa using r2)
    exact ⟨t₁, by rw [← Category.assoc, ht₁], hC⟩
  · intro R _ _ x y s' c hxy hx hy
    have rx : SRel c C 1 1 x := (sRel_one_one_iff _ _ _).2 hx
    have ry : SRel c C 1 1 y := (sRel_one_one_iff _ _ _).2 hy
    have kx : SRel c c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale rx (N / n))
    have ky : SRel c c₀ (N / n) 1 (y ≫ π) := sRel_trans hlow (by simpa using sRel_scale ry (N / n))

    obtain ⟨cx, hcx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X (Sp R) (F.s ≫ spMap (RingHom.id o))
      ((x ≫ π) ≫ F.s) (x ≫ π) rfl (by simp)).1 c₀
    have e1 : SRel cx c₀ 1 1 (x ≫ π) := (sRel_one_one_iff _ _ _).2 hcx
    have e2 : SRel cx c 1 (N / n) (𝟙 _) := sRel_cancel (f' := 𝟙 _) kx (by simpa using e1)
    have e3 : SRel cx c₀ 1 1 (𝟙 _ ≫ y ≫ π) := sRel_trans ky e2
    have fx : SiegPB cx F.univ (x ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e1)
    have fy : SiegPB cx F.univ (y ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e3)
    have hπ : x ≫ π = y ≫ π := F.inj R (x ≫ π) (y ≫ π) _ cx (by simpa using hxy) fx fy

    obtain ⟨Cx, hCx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h N o o (b.ζ : o) (b.ζ : o) (RingHom.id o) S₁ (Sp R) (π ≫ F.s)
      ((x ≫ π) ≫ F.s) x rfl (by rw [spMap_id_eq]; simp)).1 C
    have g1 : SRel Cx C 1 1 x := (sRel_one_one_iff _ _ _).2 hCx
    have g2 : SRel Cx c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale g1 (N / n))
    have g3 : SRel Cx c 1 1 (𝟙 _) := sRel_cancel (f' := 𝟙 _) rx (by simpa using g1)
    have g4 : SiegPB Cx C y := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans ry g3)
    exact (huniv (Sp R) (x ≫ π) Cx g2).unique ⟨rfl, hCx⟩ ⟨hπ.symm, g4⟩

end GlobalTheory.SiegLev
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_deeper_level_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N → Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  atlas_forward_decl GlobalTheory.SiegLev.sFam_of_dvd
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by
  atlas_forward_decl GlobalTheory.spec_local_hom_ext_of_injective
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LiftLocal

theorem toStalk_bijective (R : Type) [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R)
    (hq : q = IsLocalRing.closedPoint R) : Function.Bijective (StructureSheaf.toStalk R q).hom := by
  subst hq
  let e := IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl
    (S := (Spec.structureSheaf R).presheaf.stalk (IsLocalRing.closedPoint R)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  have : ⇑(StructureSheaf.toStalk R (IsLocalRing.closedPoint R)).hom = ⇑e :=
    funext fun r => (e.commutes r).symm
  rw [this]
  exact e.bijective

theorem isLocalHom_of_bijective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : IsLocalHom f :=
  ⟨fun a ha => by
    have h2 : (RingEquiv.ofBijective f hf).symm (f a) = a := (RingEquiv.ofBijective f hf).symm_apply_apply a
    rw [← h2]
    exact ha.map _⟩

theorem lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π]
    [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'),
    IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  intro R _ _ X Y π _ _ _ x
  obtain ⟨p, hp⟩ := (pullback.fst x π).surjective (IsLocalRing.closedPoint R)
  have hb := toStalk_bijective R _ hp
  have hτ : IsLocalHom (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom := isLocalHom_of_bijective _ hb
  letI : Algebra ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    ((pullback.fst x π).stalkMap p).hom.toAlgebra
  haveI : Module.Flat ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    Flat.stalkMap (pullback.fst x π) p
  haveI : IsLocalHom (algebraMap ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p)) :=
    inferInstanceAs (IsLocalHom ((pullback.fst x π).stalkMap p).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := (Sp R).presheaf.stalk ((pullback.fst x π) p)) (B := (pullback x π).presheaf.stalk p)
  have hψ : Function.Injective ((pullback.fst x π).stalkMap p).hom := FaithfulSMul.algebraMap_injective _ _
  have hψl : IsLocalHom ((pullback.fst x π).stalkMap p).hom := inferInstance
  refine ⟨(pullback x π).presheaf.stalk p, inferInstance, inferInstance,
    ((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom,
    ⟨fun a ha => hτ.map_nonunit a (hψl.map_nonunit _ ha)⟩, hψ.comp hb.1,
    (pullback x π).fromSpecStalk p ≫ pullback.snd x π, ?_⟩
  have hS : spMap (((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom) =
      Spec.map ((pullback.fst x π).stalkMap p) ≫ (Sp R).fromSpecStalk ((pullback.fst x π) p) := by
    rw [Scheme.Spec_fromSpecStalk']
    exact (Spec.map_comp (StructureSheaf.toStalk R ((pullback.fst x π) p)) ((pullback.fst x π).stalkMap p))
  rw [Category.assoc, ← pullback.condition, hS, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]

end GlobalTheory.LiftLocal
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π] [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'), IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  atlas_forward_decl GlobalTheory.LiftLocal.lift
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem GlobalTheory.SiegLev.SQuot.eq_of_siegPB : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  intro h n N o o' _ _ ζ ζ' F j Q R _ _ x y s' c hxy hx hy
  haveI := Q.fin; haveI := Q.etale; haveI := Q.onto
  obtain ⟨R1, _, _, φ1, hl1, hφ1, x1, hx1⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R Q.X F.X Q.π x
  obtain ⟨R2, _, _, φ2, hl2, hφ2, y2, hy2⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R1 Q.X F.X Q.π (spMap φ1 ≫ y)
  set g : Sp R2 ⟶ Sp R := spMap φ2 ≫ spMap φ1 with hg
  set x2 : Sp R2 ⟶ F.X := spMap φ2 ≫ x1 with hx2d
  have hx2 : x2 ≫ Q.π = g ≫ x := by simp only [x2, g, Category.assoc, hx1]
  have hy2' : y2 ≫ Q.π = g ≫ y := by simp only [g, Category.assoc, hy2]
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c2, hc2⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n o o ζ ζ (RingHom.id o) (Sp R) (Sp R2) s' (g ≫ s') g rfl (by rw [hid, Category.comp_id])).1 c
  have key : ∀ z : Sp R ⟶ Q.X, ∀ z2 : Sp R2 ⟶ F.X, z2 ≫ Q.π = g ≫ z → SiegPB c Q.univ z → SRel c2 F.univ 1 (N / n) z2 := by
    intro z z2 hz hcz
    have A := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n n o o o ζ ζ ζ Q.X (Sp R) (Sp R2) Q.s s' (g ≫ s') Q.univ c c2 z g 1 1 1 ((sRel_one_one_iff _ _ _).2 hcz)).1
    have B : SRel c2 Q.univ 1 1 (g ≫ z) := A.1 ((sRel_one_one_iff _ _ _).2 hc2)
    have C := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n N n o o' o ζ ζ' ζ Q.X F.X (Sp R2) Q.s F.s (g ≫ s') Q.univ F.univ c2 Q.π z2 1 (N / n) 1 Q.low).1
    rw [hz] at C
    exact C.2 B
  have e := Q.fibre R2 x2 y2 (g ≫ s') c2 (by
      rw [← Q.base, ← Category.assoc, ← Category.assoc y2, hx2, hy2', Category.assoc, Category.assoc, hxy]; simp only [g, Category.assoc])
    (key x x2 hx2 hx) (key y y2 hy2' hy)
  rw [hx2, hy2'] at e
  have hcomp : spMap (φ2.comp φ1) = g := by
    simp only [g, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  exact GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom R R2 (φ2.comp φ1) inferInstance (hφ2.comp hφ1) Q.X x y (by rw [hcomp]; exact e)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  first | exact @GlobalTheory.SiegLev.SQuot.eq_of_siegPB | exact GlobalTheory.SiegLev.SQuot.eq_of_siegPB | (intros; apply GlobalTheory.SiegLev.SQuot.eq_of_siegPB <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelLevelLoweringQuotient_represents_reduced : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N) (Q : SQuot F n (zetaAway n) j), 3 ≤ n → Odd N → n ∣ N → Function.Injective j → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Surjective (spMap j) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Q.X, f ≫ Q.s = s' ∧ SiegPB c Q.univ f := by
  first | exact @GlobalTheory.quotFam_represents | exact GlobalTheory.quotFam_represents | (intros; apply GlobalTheory.quotFam_represents <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLev

theorem sFam_down : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) →
    Nonempty (SFam h n (zetaAway n)) := by
  intro h n N hn hN hnN hpow ⟨F⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  obtain ⟨j, hinj, hζ, hfes⟩ := GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale n N hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_siegelLevelLoweringQuotientFamily h n N F j hn hN hnN hζ hfin het
  exact ⟨{
    X := Q.X
    s := Q.s
    smooth := Q.smooth
    qproj := Q.qproj
    univ := Q.univ
    princ := Q.princ
    rep := fun S s' c hred hdense hpr =>
      GlobalTheory.T.siegelLevelLoweringQuotient_represents_reduced h n N F j Q hn hN hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
    inj := fun R _ _ x y s' c hs h₁ h₂ =>
      GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object h n N _ _ (zetaAway n) (zetaAway N) F j Q R x y s' c hs h₁ h₂ }⟩

end GlobalTheory.SiegLev
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) → Nonempty (SFam h n (zetaAway n)) := by
  atlas_forward_decl GlobalTheory.SiegLev.sFam_down
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

theorem exists_sFam_cycAway : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n)) := by
  intro g n hg hn hodd
  have hn1 : n ≠ 1 := by omega
  have hlp : n.minFac.Prime := Nat.minFac_prime hn1
  have hln : n.minFac ∣ n := Nat.minFac_dvd n
  have hlodd : Odd n.minFac := Odd.of_dvd_nat hodd hln
  obtain ⟨j, hj, ⟨F⟩⟩ := GlobalTheory.SiegelTor.exists_sFam_primePow_sq g n.minFac hg hlp hlodd
  set l := n.minFac with hl
  set k := (l ^ j) ^ 2 with hk
  have hl3 : 3 ≤ l := by
    rcases hlodd with ⟨m, hm⟩
    have := hlp.two_le
    omega
  have hk3 : 3 ≤ k := by
    have h1 : l ≤ l ^ j := Nat.le_self_pow (by omega) l
    have h2 : l ^ j ≤ (l ^ j) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hkodd : Odd k := (hlodd.pow).pow
  have hN0 : n * k ≠ 0 := by positivity
  have hNodd : Odd (n * k) := hodd.mul hkodd
  obtain ⟨i, hi, hz, -⟩ := GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale k (n * k) hN0 (dvd_mul_left k n)
  obtain ⟨F₂⟩ := GlobalTheory.SiegelFamilyNumberField.nonempty_baseChange F i hi
  rw [hz] at F₂
  haveI : IsDedekindDomain (cycAway (n * k)) := (arBase_cycAway (n * k) hN0).1
  have hup : Nonempty (SFam g (n * k) ((cycBase hN0).ζ : cycAway (n * k))) :=
    GlobalTheory.T.siegelFamily_deeper_level_of_dvd g k (n * k) (cycAway (n * k)) (cycBase hN0) hk3 hNodd (dvd_mul_left k n)
      (by rw [cycBase_ζ]; exact ⟨F₂⟩)
  rw [cycBase_ζ] at hup
  refine GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes g n (n * k) hn hNodd (dvd_mul_right n k) ⟨2 * j + 1, ?_⟩ hup
  rw [pow_succ', hk, ← pow_mul, mul_comm j 2]
  exact mul_dvd_mul_left n (pow_dvd_pow_of_dvd hln _)

end GlobalTheory.SiegelTor
end
