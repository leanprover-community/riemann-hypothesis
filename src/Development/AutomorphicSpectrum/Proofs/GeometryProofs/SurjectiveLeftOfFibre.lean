import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleFlatOfFlatAndFibreFlat
import BuildAid.ForwardExisting

section
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem isPushout_cancel (R k A B T U : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [CommRing T] [CommRing U]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra R T] [Algebra R U]
    [Algebra A B] [Algebra A T] [Algebra A U] [Algebra B U] [Algebra k T] [Algebra k U]
    [Algebra T U]
    [IsScalarTower R A B] [IsScalarTower R A T] [IsScalarTower R A U] [IsScalarTower R B U]
    [IsScalarTower R k T] [IsScalarTower R k U] [IsScalarTower k T U] [IsScalarTower A T U]
    [IsScalarTower A B U]
    (h₁ : Algebra.IsPushout R A k T) (h₂ : Algebra.IsPushout R B k U) :
    Algebra.IsPushout A B T U := by
  rw [Algebra.isPushout_iff] at h₁ h₂ ⊢
  refine IsBaseChange.of_comp (R := R) (S := A) (T := B)
    (f := (IsScalarTower.toAlgHom R k T).toLinearMap)
    (h := (IsScalarTower.toAlgHom A T U).toLinearMap) h₁ ?_
  convert h₂ using 1
  ext x
  simp [IsScalarTower.algebraMap_apply k T U]

noncomputable abbrev fibreMap (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    k ⊗[R] A →+* k ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R k) (IsScalarTower.toAlgHom R A B)).toRingHom

theorem fibreMap_isLocalization (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A]
    [CommRing B] [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] :
    letI := (fibreMap R k A B).toAlgebra
    IsLocalization (M.map (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A))
      (k ⊗[R] B) := by
  letI iTU : Algebra (k ⊗[R] A) (k ⊗[R] B) := (fibreMap R k A B).toAlgebra
  letI iAT : Algebra A (k ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  letI iBU : Algebra B (k ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  letI iAU : Algebra A (k ⊗[R] B) := ((algebraMap B (k ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  haveI t1 : IsScalarTower A B (k ⊗[R] B) := .of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower A (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change (1 : k) ⊗ₜ[R] (algebraMap A B a) = fibreMap R k A B ((1 : k) ⊗ₜ[R] a)
    simp
  haveI t3 : IsScalarTower R A (k ⊗[R] B) := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B (k ⊗[R] B) r, IsScalarTower.algebraMap_apply R A B r]
    rfl
  haveI t4 : IsScalarTower k (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change a ⊗ₜ[R] (1 : B) = fibreMap R k A B (a ⊗ₜ[R] (1 : A))
    simp
  have h := isPushout_cancel R k A B (k ⊗[R] A) (k ⊗[R] B)
    TensorProduct.isPushout' TensorProduct.isPushout'
  exact (Algebra.isLocalization_iff_isPushout M B).mpr h.symm

end GlobalTheory.CompanionTheory.FinAlgFlat

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem fibreMap_flat_localize (R k P Q Bp An : Type*) [CommRing R] [CommRing k] [CommRing P]
    [CommRing Q] [CommRing Bp] [CommRing An] [Algebra R k] [Algebra R P] [Algebra R Q]
    [Algebra R Bp] [Algebra R An] [Algebra P Q] [Algebra P Bp] [Algebra P An] [Algebra Q An]
    [Algebra Bp An] [IsScalarTower R P Q] [IsScalarTower R P Bp] [IsScalarTower R Q An]
    [IsScalarTower R Bp An] [IsScalarTower P Q An] [IsScalarTower P Bp An]
    (M : Submonoid P) [IsLocalization M Bp] (N : Submonoid Q) [IsLocalization N An]
    (h : (fibreMap R k P Q).Flat) : (fibreMap R k Bp An).Flat := by
  have hQA : (fibreMap R k Q An).Flat := by
    have hl := fibreMap_isLocalization R k Q An N
    letI := (fibreMap R k Q An).toAlgebra
    exact IsLocalization.flat (k ⊗[R] An)
      (N.map (Algebra.TensorProduct.includeRight : Q →ₐ[R] k ⊗[R] Q))
  have e : (fibreMap R k Bp An).comp (fibreMap R k P Bp) =
      (fibreMap R k Q An).comp (fibreMap R k P Q) := by
    refine RingHom.ext fun x => ?_
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      simp [← IsScalarTower.algebraMap_apply]
  have hPA : ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).Flat := by
    rw [e]; exact h.comp hQA
  have hl := fibreMap_isLocalization R k P Bp M
  letI i1 := (fibreMap R k P Bp).toAlgebra
  letI i2 := (fibreMap R k Bp An).toAlgebra
  letI i3 := ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).toAlgebra
  haveI : IsScalarTower (k ⊗[R] P) (k ⊗[R] Bp) (k ⊗[R] An) := .of_algebraMap_eq' rfl
  exact (Module.flat_iff_of_isLocalization (k ⊗[R] Bp)
    (M.map (Algebra.TensorProduct.includeRight : P →ₐ[R] k ⊗[R] P)) (k ⊗[R] An)).mpr hPA

theorem flat_localization_of_fibre (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) (n : Ideal Q) [n.IsMaximal] :
    Module.Flat P (Localization.AtPrime n) := by
  haveI : Module.Finite P Q := .of_restrictScalars_finite R P Q
  haveI : Algebra.IsIntegral P Q := inferInstance
  haveI : Algebra.IsIntegral R P := inferInstance
  haveI : IsNoetherianRing P := IsNoetherianRing.of_finite R P
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite R Q
  let p : Ideal P := n.comap (algebraMap P Q)
  haveI hp : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  have hmR : p.comap (algebraMap R P) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime n) :=
    (Localization.localRingHom p n (algebraMap P Q) rfl).toAlgebra
  haveI tP : IsScalarTower P (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n) x]
      exact (Localization.localRingHom_to_map p n (algebraMap P Q) rfl x).symm
  haveI tR : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R P (Localization.AtPrime p) x,
        ← IsScalarTower.algebraMap_apply P (Localization.AtPrime p) (Localization.AtPrime n),
        IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n),
        ← IsScalarTower.algebraMap_apply R P Q,
        ← IsScalarTower.algebraMap_apply R Q (Localization.AtPrime n)]
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n) :=
    IsLocalization.isNoetherianRing n.primeCompl _ inferInstance
  haveI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hnu
    have ham : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [← hmR, Ideal.mem_comap] at ham
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p
      (algebraMap R P a)).mpr ham
    rw [← IsScalarTower.algebraMap_apply R P (Localization.AtPrime p)] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime n)) :=
    Localization.isLocalHom_localRingHom p n (algebraMap P Q) rfl
  have hfl : Module.Flat R (Localization.AtPrime n) := inferInstance
  have hfib := fibreMap_flat_localize R (IsLocalRing.ResidueField R) P Q (Localization.AtPrime p)
    (Localization.AtPrime n) p.primeCompl n.primeCompl h
  have hBA : Module.Flat (Localization.AtPrime p) (Localization.AtPrime n) :=
    GlobalTheory.T.module_flat_of_flat_and_fibre_flat R (Localization.AtPrime p) (Localization.AtPrime n) hfl hfib
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime n)).mp hBA

theorem flat_of_fibreMap_flat (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) : Module.Flat P Q :=
  Module.flat_of_isLocalized_maximal Q Q (fun n _ => Localization.AtPrime n)
    (fun n _ => Algebra.linearMap Q _) (fun n _ => flat_localization_of_fibre R P Q h n)

theorem ringHom_flat_of_fibre_flat : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q),
    (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat →
      φ.toRingHom.Flat := by
  intro R P Q _ _ _ _ _ _ _ _ _ _ φ h
  letI : Algebra P Q := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R P Q := .of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : IsScalarTower.toAlgHom R P Q = φ := by ext; rfl
  have h' : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat := by
    rw [fibreMap, e]; exact h
  exact flat_of_fibreMap_flat R P Q h'

end GlobalTheory.CompanionTheory.FinAlgFlat
end

open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_flat_special_fibre : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q), (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat → φ.toRingHom.Flat := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat
end

section
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.CompanionTheory.FinFlatModel

open IsLocalRing

section Model

variable {R : Type} [CommRing R] [IsLocalRing R]

noncomputable def quotEquiv : (R ⧸ maximalIdeal R ^ (0 + 1)) ≃+* ResidueField R :=
  Ideal.quotEquivOfEq (by simp)

noncomputable def specIso :
    Spec (CommRingCat.of (ResidueField R)) ≅
      Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))) where
  hom := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).toRingHom.comp (quotEquiv (R := R)).symm.toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).symm.toRingHom.comp (quotEquiv (R := R)).toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _

theorem specIso_hom_thick :
    (specIso (R := R)).hom ≫ thick R (maximalIdeal R) 0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) := by
  simp only [specIso, thick]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem isPullback_fibre {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
        i.inv)
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (specIso (R := R)).hom)
      X.hom (thick R (maximalIdeal R) 0) := by
  refine IsPullback.of_iso
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R (ResidueField R) P)).flip
    (Iso.refl _) i.symm specIso (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [hi]
  · simp [specIso_hom_thick]

theorem exists_model (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    ∃ (P : Type) (_ : CommRing P) (_ : Algebra R P) (i : X.left ≅ Spec (CommRingCat.of P)),
      X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let _ : Algebra R Γ(X.left, ⊤) := g.hom.toAlgebra
  refine ⟨Γ(X.left, ⊤), inferInstance, g.hom.toAlgebra, X.left.isoSpec, ?_⟩
  have : CommRingCat.ofHom (algebraMap R Γ(X.left, ⊤)) = g := rfl
  erw [this, hg]
  simp

theorem map_left_eq {P Q : Type} [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (φ : Q →ₐ[R] P)
    (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)))
    (hj : Y.hom = j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)))
    (hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv) :
    ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left =
      (isPullback_fibre X i hi).isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
        (isPullback_fibre Y j hj).isoPullback.hom := by
  have e1 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := Q)).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have e2 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := Q))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := P))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp
  apply pullback.hom_ext
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.fst Y.hom (thick R (maximalIdeal R) 0) =
        pullback.fst X.hom (thick R (maximalIdeal R) 0) ≫ f.left := pullback.lift_fst _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst,
      reassoc_of% e1, ← (isPullback_fibre X i hi).isoPullback_inv_fst, hf]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.snd Y.hom (thick R (maximalIdeal R) 0) =
        pullback.snd X.hom (thick R (maximalIdeal R) 0) := pullback.lift_snd _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      reassoc_of% e2, ← (isPullback_fibre X i hi).isoPullback_inv_snd]

theorem finite_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Finite R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h')

theorem flat_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (hX : Flat X.hom)
    (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Flat R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : Flat (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h')

end Model

theorem exists_algHom_model :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  intro R _ _ X Y _ _ f
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  obtain ⟨P, _, _, i, hi⟩ := exists_model X
  obtain ⟨Q, _, _, j, hj⟩ := exists_model Y
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.inv ≫ f.left ≫ j.hom)
  have hcomm : CommRingCat.ofHom (algebraMap R Q) ≫ ψ = CommRingCat.ofHom (algebraMap R P) := by
    apply Spec.map_injective
    have hw : f.left ≫ Y.hom = X.hom := Over.w f
    rw [Spec.map_comp, hψ]
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
    have h2 : j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) = Y.hom := hj.symm
    rw [h1, ← hw]
    simp only [Category.assoc, h2]
  let φ : Q →ₐ[R] P :=
    { ψ.hom with
      commutes' := fun r => by
        have := congrArg (fun g => g.hom r) hcomm
        simpa using this }
  have hφ : CommRingCat.ofHom φ.toRingHom = ψ := rfl
  have hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv := by
    rw [hφ, hψ]
    simp
  refine ⟨P, Q, inferInstance, inferInstance, inferInstance, inferInstance, φ, i, j,
    (isPullback_fibre X i hi).isoPullback.symm, (isPullback_fibre Y j hj).isoPullback.symm,
    finite_of_model X i hi, finite_of_model Y j hj, fun h => flat_of_model X h i hi, hf, ?_⟩
  exact map_left_eq f φ i j hi hj hf

end GlobalTheory.CompanionTheory.FinFlatModel
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_scheme_map_from_special_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model
end

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.FinFlat

theorem bijective_of_lTensor (R M N : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] (f : M →ₗ[R] N)
    (h : Function.Bijective (f.lTensor (IsLocalRing.ResidueField R))) : Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have hQ : Subsingleton (IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f)) := by
      have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f), z = 0 := fun z => by
        obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (IsLocalRing.ResidueField R)
          (Submodule.mkQ_surjective (LinearMap.range f)) z
        obtain ⟨v, rfl⟩ := h.2 w
        have h0 : (LinearMap.range f).mkQ ∘ₗ f = 0 := by
          ext x
          simp
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero]
        rfl
      exact ⟨fun x y => by rw [key x, key y]⟩
    have h1 : Subsingleton (N ⧸ LinearMap.range f) := IsLocalRing.subsingleton_tensorProduct.1 hQ
    exact fun y => (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).1 (Subsingleton.elim _ _)
  have hfree : Module.Free R N := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ y, f (s y) = y := fun y => LinearMap.congr_fun hs y
  let π : M →ₗ[R] LinearMap.ker f := (LinearMap.id - s ∘ₗ f).codRestrict (LinearMap.ker f) (fun x => by
    simp [hs'])
  have hπ : π ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    simp [π, LinearMap.mem_ker.1 x.2]
  have hK : Subsingleton (IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f) := by
    have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f, z = 0 := fun z => by
      have h0 : f ∘ₗ (LinearMap.ker f).subtype = 0 := by
        ext x
        simp
      have h1 : (LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z = 0 := by
        apply h.1
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero, map_zero]
        rfl
      have h2 : π.lTensor (IsLocalRing.ResidueField R) ((LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z) = z := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπ, LinearMap.lTensor_id]
        rfl
      rw [← h2, h1, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  have hK' : Subsingleton (LinearMap.ker f) := IsLocalRing.subsingleton_tensorProduct.1 hK
  refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, hsurj⟩
  have h3 : (⟨x, hx⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h3

theorem flat_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite A.hom] [IsFinite B.hom] [Flat A.hom] (b : A ⟶ B)
    (h : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Flat b.left := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R A B b
  have := h3 inferInstance
  have h' : Flat (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  rw [Flat.SpecMap_iff] at h'
  have h'' : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    rw [Flat.SpecMap_iff]
    exact GlobalTheory.T.flat_of_flat_special_fibre R Q P φ h'
  rw [e1]; infer_instance

theorem isIso_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C K : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite K.hom] [Flat C.hom] (u : C ⟶ K)
    (h : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) : IsIso u := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R C K u
  have := h3 inferInstance
  have h0 : IsIso ((Over.forget _).map ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) := inferInstance
  have h0' : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left := h0
  have h' : IsIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  have h2' : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) :=
    isIso_SpecMap_iff.1 h'
  have hco : ⇑(φ.toLinearMap.lTensor (IsLocalRing.ResidueField R)) =
      ⇑(Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hφ : Function.Bijective φ :=
    bijective_of_lTensor R Q P φ.toLinearMap (by rw [hco]; exact h2')
  have hS : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) := isIso_SpecMap_iff.2 hφ
  have hl : IsIso u.left := by rw [e1]; infer_instance
  haveI : IsIso ((Over.forget _).map u) := hl
  exact isIso_of_reflects_iso u (Over.forget _)

theorem surjective_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite B.hom] (b : A ⟶ B) [Flat b.left]
    (h : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Surjective b.left := by
  constructor
  intro x
  have hsp : SpecializingMap B.hom := B.hom.isClosedMap.specializingMap
  obtain ⟨y, hxy, hy⟩ := hsp (IsLocalRing.specializes_closedPoint (B.hom x))
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) := by
    rw [Ideal.Quotient.nontrivial_iff]; simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))) := inferInstance
  have ht : thick R (IsLocalRing.maximalIdeal R) 0 t = IsLocalRing.closedPoint R := by
    have hle : IsLocalRing.maximalIdeal R ≤ (thick R (IsLocalRing.maximalIdeal R) 0 t).asIdeal := fun x hx => by
      show Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)) x ∈ t.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hx)]
      exact zero_mem _
    exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (thick R (IsLocalRing.maximalIdeal R) 0 t).isPrime.ne_top) hle)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback y t (hy.trans ht.symm)
  obtain ⟨z₀, hz₀⟩ := h.surj y₀
  have hcomp : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ pullback.fst B.hom (thick R (IsLocalRing.maximalIdeal R) 0) =
      pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) ≫ b.left := pullback.lift_fst _ _ _
  have hz : b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) = y := by
    rw [← hy₀, ← hz₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]
  obtain ⟨w, -, hw⟩ := Flat.generalizingMap b.left (show x ⤳ b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) by rwa [hz])
  exact ⟨w, hw⟩

theorem main (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (hab : a ≫ b = toUnit C ≫ e)
  (h₀ : IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e))
  (hf : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left)
  (hs : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) :
  IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  have hb : Flat b.left := flat_left_of_fibre R A B b hf
  have hK : IsPullback (pullback.fst b e) (toUnit (pullback b e)) b e := by
    have h := IsPullback.of_hasPullback b e
    rwa [toUnit_unique (pullback.snd _ _) (toUnit _)] at h
  have hKl := hK.map (Over.forget _)
  have hKl' : IsPullback (pullback.fst b e).left (pullback b e).hom b.left e.left := by
    have hA : (toUnit (pullback b e)).left = (pullback b e).hom := by simpa using Over.w (toUnit (pullback b e))
    rw [← hA]; exact hKl
  have hbfin : IsFinite b.left := by
    have : IsFinite (b.left ≫ B.hom) := by rw [Over.w b]; infer_instance
    exact IsFinite.of_comp b.left B.hom
  have hKfin : IsFinite (pullback b e).hom := by
    have h1 : IsFinite (pullback b e).hom := MorphismProperty.of_isPullback hKl' ‹_›
    exact h1
  have hclosed : IsClosedImmersion (pullback.fst b e).left := by
    have he : IsClosedImmersion e.left := by
      have : IsClosedImmersion (e.left ≫ B.hom) := by
        have : e.left ≫ B.hom = 𝟙 _ := by simpa using Over.w e
        rw [this]; infer_instance
      exact IsClosedImmersion.of_comp _ B.hom
    exact MorphismProperty.of_isPullback hKl'.flip he
  let u : C ⟶ pullback b e := hK.lift a (toUnit C) hab
  have hu1 : u ≫ pullback.fst b e = a := hK.lift_fst _ _ _
  have hu0 : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u) := by
    have hK0 := hK.map (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0))
    have : (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u = (h₀.isoIsPullback _ _ hK0).hom := by
      apply hK0.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp, hu1]
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp, toUnit_unique (u ≫ toUnit _) (toUnit C)]
    rw [this]; infer_instance
  have hu : IsIso u := isIso_of_fibre R C _ u hu0
  refine ⟨?_, hb, surjective_left_of_fibre R A B b hs, ?_⟩
  · have : IsIso u.left := inferInstanceAs (IsIso ((Over.forget _).map u))
    rw [← hu1, Over.comp_left]; infer_instance
  · exact IsPullback.of_iso hK (asIso u).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hu1]) (by simp) (by simp) (by simp)

theorem exact_of_closedFibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B), a ≫ b = toUnit C ≫ e → IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e) → Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  intro R _ _ _ C A B _ _ _ _ _ _ a b e hab h₀ hf hs
  exact main R C A B a b e hab h₀ hf hs

end GlobalTheory.CompanionTheory.Ar.BT.FinFlat
end
end
