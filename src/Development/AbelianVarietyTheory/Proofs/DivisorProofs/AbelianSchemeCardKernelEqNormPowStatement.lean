import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.DegNorm

open Polynomial IntermediateField

theorem deg_pow_finrank_eq_natAbs_norm_pow : ∀ (K : Type) [Field K] (B : AbVar K) (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* End B) (c : 𝓞 F), c ≠ 0 → deg (A := B) (B := B) (ψ c) ^ Module.finrank ℚ F = (Algebra.norm ℤ c).natAbs ^ (2 * B.dim) := by
  intro K _ B F _ _ ψ c hc
  have hN : Algebra.norm ℤ c ≠ 0 := by
    intro h
    have h1 := Algebra.coe_norm_int c
    rw [h, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at h1
    exact hc (by exact_mod_cast h1)
  by_cases hB : B.dim = 0
  · obtain ⟨y, hy⟩ := dvd_algebraMap_norm c
    have hcomp : ψ y ≫ ψ c = Algebra.norm ℤ c • 𝟙 B := by
      change ψ c * ψ y = _
      rw [← map_mul, ← hy, algebraMap_int_eq, Int.coe_castRingHom, map_intCast, ← zsmul_one]
      rfl
    have h := isIsogeny_comp_iff_and_deg_comp K B B B (ψ y) (ψ c) rfl rfl
    obtain ⟨-, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny K B _ hN
    rw [hcomp] at h
    rw [h.2, hB, mul_zero, pow_zero] at hd
    have h1 : deg (A := B) (B := B) (ψ c) = 1 := Nat.eq_one_of_mul_eq_one_left hd
    rw [h1, hB, mul_zero, pow_zero, one_pow]
  · classical
    obtain ⟨k, hk, hPQ⟩ := charpoly_eq_minpoly_pow B hB ψ c
    obtain ⟨⟨-, hd, -⟩, -⟩ := isCharpoly_charpoly_unique K B (ψ c)
    have hxint : IsIntegral ℚ (c : F) := Algebra.IsIntegral.isIntegral _
    have hdeg : k * Module.finrank ℚ ℚ⟮(c : F)⟯ = 2 * B.dim := by
      have e := congrArg Polynomial.natDegree hPQ
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _), hd,
        Polynomial.natDegree_pow, ← IntermediateField.adjoin.finrank hxint] at e
      omega
    have hD := deg_aeval_eq_prod_aroots K B (ψ c) (AlgebraicClosure ℚ) Polynomial.X
    simp only [aeval_X, Multiset.map_id'] at hD
    rw [hPQ, Polynomial.aroots_pow, Multiset.prod_nsmul] at hD
    have hNr := Algebra.norm_eq_prod_roots (K := ℚ) (L := F) (AlgebraicClosure ℚ) (x := (c : F))
      (IsAlgClosed.splits _)
    have e : algebraMap ℚ (AlgebraicClosure ℚ) (((deg (A := B) (B := B) (ψ c) : ℕ) : ℚ) ^ Module.finrank ℚ⟮(c : F)⟯ F) =
        algebraMap ℚ (AlgebraicClosure ℚ) (Algebra.norm ℚ (c : F) ^ k) := by
      rw [map_pow, map_pow, hD, hNr, ← pow_mul, ← pow_mul, mul_comm]
    have e2 := (algebraMap ℚ (AlgebraicClosure ℚ)).injective e
    rw [← Algebra.coe_norm_int] at e2
    have e3 : ((deg (A := B) (B := B) (ψ c) : ℕ) : ℤ) ^ Module.finrank ℚ⟮(c : F)⟯ F = Algebra.norm ℤ c ^ k := by
      exact_mod_cast e2
    have e4 := congrArg (fun t : ℤ => t ^ Module.finrank ℚ ℚ⟮(c : F)⟯) e3
    simp only [← pow_mul] at e4
    rw [hdeg, mul_comm, Module.finrank_mul_finrank] at e4
    have e5 := congrArg Int.natAbs e4
    simpa [Int.natAbs_pow] using e5

end GlobalTheory.AV.AbVar.DegNorm
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_pow_finrank_eq_natAbs_norm_pow : ∀ (K : Type) [Field K] (B : AbVar K) (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* End B) (c : 𝓞 F), c ≠ 0 → deg (A := B) (B := B) (ψ c) ^ Module.finrank ℚ F = (Algebra.norm ℤ c).natAbs ^ (2 * B.dim) := by
  first | (exact @GlobalTheory.AV.AbVar.DegNorm.deg_pow_finrank_eq_natAbs_norm_pow) | (exact GlobalTheory.AV.AbVar.DegNorm.deg_pow_finrank_eq_natAbs_norm_pow) | (intros; apply GlobalTheory.AV.AbVar.DegNorm.deg_pow_finrank_eq_natAbs_norm_pow  <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.TangentCrit

theorem formallyUnramified_of_dual_const_field {K A B : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FiniteType K B] [Algebra.FiniteType A B]
    (H : ∀ φ : B →+* DualNumber K, (∀ c, φ (algebraMap K B c) = algebraMap K (DualNumber K) c) →
      (∀ a, (φ (algebraMap A B a)).snd = 0) → ∀ b, (φ b).snd = 0) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hne
  rw [← Module.support_eq_empty_iff (R := B), ← ne_eq, ← Set.nonempty_iff_ne_empty] at hne
  obtain ⟨p, hp⟩ := hne
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let P : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have hP : P ∈ Module.support B Ω[B⁄A] := by
    rw [Module.support_eq_zeroLocus] at hp ⊢
    exact fun x hx => hpm (hp hx)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hP
  have hsurj : Function.Surjective (algebraMap B m.ResidueField) := by
    intro y
    obtain ⟨x, rfl⟩ := m.bijective_algebraMap_quotient_residueField.surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨b, rfl⟩
  haveI : Algebra.FiniteType K m.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom K B m.ResidueField) hsurj
  haveI : Module.Finite K m.ResidueField := finite_of_finite_type_of_isJacobsonRing K _
  let ev : m.ResidueField →ₐ[K] K := IsAlgClosed.lift
  letI : Algebra m.ResidueField K := ev.toRingHom.toAlgebra
  letI : Algebra B K := (ev.toRingHom.comp (algebraMap B m.ResidueField)).toAlgebra
  haveI : IsScalarTower B m.ResidueField K := .of_algebraMap_eq fun _ => rfl
  letI : Algebra A K := ((algebraMap B K).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B K := .of_algebraMap_eq fun _ => rfl
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor m.ResidueField) :=
    lTensor_injective_of_extend (k := K) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B K := χ.compDer (KaehlerDifferential.D A B)
      have hlin : ∀ c, derToDual D (algebraMap K B c) = algebraMap K (DualNumber K) c := by
        intro c
        ext
        · rw [fst_derToDual]
          change ev (algebraMap B m.ResidueField (algebraMap K B c)) = _
          rw [← IsScalarTower.algebraMap_apply, ev.commutes]
          rfl
        · rw [snd_derToDual, IsScalarTower.algebraMap_apply K A B, D.map_algebraMap]
          rfl
      have := H (derToDual D) hlin (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : m.ResidueField ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))

end GlobalTheory.TangentCrit

namespace GlobalTheory.TangentCrit

end GlobalTheory.TangentCrit
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.FinUnram

theorem formallyUnramified_of_dual_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R] [Module.Finite K R], (∀ (φ : R →ₐ[K] DualNumber K) (r : R), (φ r).snd = 0) → Algebra.FormallyUnramified K R := by
  intro K _ _ R _ _ _ H
  haveI : Algebra.FiniteType K R := inferInstance
  refine GlobalTheory.TangentCrit.formallyUnramified_of_dual_const_field (K := K) (A := K) (B := R)
    (fun φ hK _ b => ?_)
  exact H { φ with commutes' := hK } b

end GlobalTheory.FinUnram
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formally_unramified_of_dual_numbers : ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R] [Module.Finite K R], (∀ (φ : R →ₐ[K] DualNumber K) (r : R), (φ r).snd = 0) → Algebra.FormallyUnramified K R := by
  first | (exact @GlobalTheory.FinUnram.formallyUnramified_of_dual_const) | (exact GlobalTheory.FinUnram.formallyUnramified_of_dual_const) | (intros; apply GlobalTheory.FinUnram.formallyUnramified_of_dual_const  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerUnram

theorem formallyUnramified_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  intro K _ _ B f hf H
  have hfin : IsFinite (Hom.hom f).left := hf.1
  set Z := pullback (Hom.hom f).left η[B.X].left with hZ
  set p : Z ⟶ Sp K := pullback.snd (Hom.hom f).left η[B.X].left with hp
  have : IsFinite p := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom p
  have hnat := Scheme.isoSpec_hom_naturality p
  have hS : Spec.map p.appTop = Z.isoSpec.inv ≫ p ≫ (Sp K).isoSpec.hom := by
    rw [← hnat]; simp
  have hfinS : IsFinite (Spec.map p.appTop) := by rw [hS]; infer_instance
  have hfinR : p.appTop.hom.Finite := (IsFinite.SpecMap_iff _).1 hfinS
  let ψ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  let _ : Algebra K Γ(Z, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) := by
    have h : ψ.hom.Finite := by
      show (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite
      exact hfinR.comp (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
    exact h
  have hp' : p.appTop = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ ψ := by simp [ψ]
  have : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified), hp',
    CommRingCat.hom_comp, RingHom.RespectsIso.cancel_left_isIso RingHom.FormallyUnramified.respectsIso]
  show Algebra.FormallyUnramified K Γ(Z, ⊤)
  refine GlobalTheory.T.formally_unramified_of_dual_numbers K Γ(Z, ⊤) fun φ r => ?_

  let q : Sp (DualNumber K) ⟶ Z := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Z.isoSpec.inv
  have hq : q ≫ p = spMap (algebraMap K (DualNumber K)) := by
    have e := Scheme.isoSpec_inv_naturality p
    simp only [q, Category.assoc]
    rw [← e, Scheme.isoSpec_Spec]
    simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact φ.commutes a
  have hfst : ∀ {T : Scheme} (g : T ⟶ Z), (g ≫ pullback.fst (Hom.hom f).left η[B.X].left) ≫ B.X.hom = g ≫ p := by
    intro T g
    rw [Category.assoc, ← Over.w (Hom.hom f), ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, Over.w η[B.X]]
    rfl
  let v : epsPtR (𝟙 (Sp K)) ⟶ B.X := Over.homMk (q ≫ pullback.fst _ _) (by
    rw [hfst, hq]; exact (Category.comp_id _).symm)
  have hv : v ≫ Hom.hom f = 1 := by
    ext1
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    simp only [v, Over.homMk_left, Category.assoc]
    rw [pullback.condition, ← Category.assoc q, hq]
    rfl

  let T₀ : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let red : T₀ ⟶ epsPtR (𝟙 (Sp K)) := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_id]
    congr 1)
  let bas : epsPtR (𝟙 (Sp K)) ⟶ T₀ := Over.homMk (spMap (algebraMap K (DualNumber K))) rfl
  have hrb : red ≫ bas = 𝟙 T₀ := by
    ext1
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let w : epsPtR (𝟙 (Sp K)) ⟶ B.X := v * (bas ≫ red ≫ v)⁻¹
  have hw₀ : red ≫ w = 1 := by
    simp only [w]
    rw [comp_mul, GrpObj.comp_inv, ← Category.assoc red bas, hrb, Category.id_comp, mul_inv_cancel]
  have hwf : w ≫ Hom.hom f = 1 := by
    simp only [w]
    rw [mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hv, comp_one, comp_one, inv_one,
      _root_.mul_one]
  have hw : w = 1 := H w (by
    have := congrArg Over.Hom.left hw₀
    rw [Over.comp_left] at this
    exact this) hwf
  have hvc : v = bas ≫ red ≫ v := mul_inv_eq_one.mp hw
  have hq2 : q = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ q := by
    refine pullback.hom_ext ?_ ?_
    · have := congrArg Over.Hom.left hvc
      simpa [v, red, bas] using this
    · change q ≫ p = _ ≫ _ ≫ q ≫ p
      rw [hq, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
  simp only [q, ← Category.assoc] at hq2
  rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at hq2
  have := congrArg TrivSqZeroExt.snd congr($(Spec.map_injective hq2).hom r)
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KerUnram
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_kernel_isogeny_tangent_injective : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  first | (exact @GlobalTheory.KerUnram.formallyUnramified_ker) | (exact GlobalTheory.KerUnram.formallyUnramified_ker) | (intros; apply GlobalTheory.KerUnram.formallyUnramified_ker  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreAV

section

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) (A : Over S) [GrpObj A]

theorem pull_map_left_fst {B : Over S} (f : A ⟶ B) :
    ((Over.pullback x).map f).left ≫ pullback.fst B.hom x = pullback.fst A.hom x ≫ f.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
    (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A)) (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
    (z : T ⟶ (Over.pullback x).obj A) : e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, pull_map_left_fst, Category.assoc]

end

open GlobalTheory.AV.AbVar in
theorem fibre_av : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c)) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c) = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  letI : GrpObj ((Over.pullback x).obj A) := Functor.grpObjObj
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans (GlobalTheory.PushEigen.ptClosureEquiv B).symm
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → End B := fun c => @Hom.mk k _ B B ((Over.pullback x).map (act.act c)) (hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := ψf
      map_one' := by
        apply GlobalTheory.AV.AbVar.hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id]
        rfl
      map_mul' := fun a b => by
        apply GlobalTheory.AV.AbVar.hom_ext
        change _ = Hom.hom (ψf b) ≫ Hom.hom (ψf a)
        rw [hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply GlobalTheory.AV.AbVar.hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply GlobalTheory.AV.AbVar.hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show (GlobalTheory.PushEigen.ptClosureEquiv B).symm (e₀.symm (z ≫ act.act c)) =
      (GlobalTheory.PushEigen.ptClosureEquiv B).symm (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map x A (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map x A (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)

end GlobalTheory.FibreAV
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_point_abelian_variety_action : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c)) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c) = 1 → w = 1 := by
  first | (exact @GlobalTheory.FibreAV.fibre_av) | (exact GlobalTheory.FibreAV.fibre_av) | (intros; apply GlobalTheory.FibreAV.fibre_av  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.AVCount

section
attribute [local instance] Over.cartesianMonoidalCategory

theorem deg_eq_card_ker_of_unram : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) → deg f = Nat.card (ptMap f).ker := by
  intro K _ A B f hiso hpfu
  have hfl : Flat f.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  let e : Sp K ⟶ B.X.left := η[B.X].left
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p
  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, GlobalTheory.AV.DegSep.one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, GlobalTheory.AV.DegSep.one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, GlobalTheory.AV.DegSep.one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end

theorem map_zero_eq_one_of_additive_to_group {M G : Type} [AddCommGroup M] [Group G] (f : M → G) (hadd : ∀ a a', f (a + a') = f a * f a') : f 0 = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact mul_left_cancel (this.symm.trans (mul_one (f 0)).symm)

theorem map_nsmul_eq_pow_of_additive_to_mulGroup {M G : Type} [AddCommGroup M] [Group G] (f : M → G) (hadd : ∀ a a', f (a + a') = f a * f a') (n : ℕ) (a : M) : f (n • a) = f a ^ n := by
  induction n with
  | zero => rw [zero_smul, map_zero_eq_one_of_additive_to_group f hadd, pow_zero]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem deg_eq_card_ker_of_tangent : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → deg f = Nat.card (ptMap f).ker :=
  fun K _ _ B f hf hv => deg_eq_card_ker_of_unram K B B f hf (GlobalTheory.T.formallyUnramified_kernel_isogeny_tangent_injective K B f hf hv)

theorem card_ker_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  intro S A _ _ hA F _ _ act k _ _ x h ℓ hℓ hℓk hyp c hc hv
  obtain ⟨B, e, ψ, he, htan⟩ := GlobalTheory.T.geometric_point_abelian_variety_action S A hA F act k x
  have hiso := (GlobalTheory.AV.AbVar.DegNorm.isIsogeny_and_deg_ne_zero B ψ c hc).1
  have hE := deg_eq_card_ker_of_tangent k B (ψ c) hiso (htan c hv)
  have hD := GlobalTheory.T.degree_pow_finrank_eq_natAbs_norm_pow k B F ψ c hc
  have hker : Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = Nat.card (ptMap (ψ c)).ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun g => ?_)
    change _ ↔ e g ≫ Hom.hom (ψ c) = 1
    rw [← he, MulEquiv.map_eq_one_iff]

  have htors : Nat.card {g : Over.mk x ⟶ A // g ^ ℓ = 1} = ℓ ^ (2 * B.dim) := by
    rw [← card_torsion_pt k B ℓ hℓk]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun g => ?_)
    change _ ↔ e g ^ ℓ = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have hL2 : Nat.card {g : Over.mk x ⟶ A // g ^ ℓ = 1} = ℓ ^ (h * Module.finrank ℚ F) := by
    obtain ⟨f, hadd, -, hinj, hsurj⟩ := hyp 1
    have h0 := map_zero_eq_one_of_additive_to_group f hadd
    have hns := map_nsmul_eq_pow_of_additive_to_mulGroup f hadd
    have hq : ((ℓ : ℕ) : 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hkill : ∀ a : Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}, ℓ • a = 0 := by
      intro a
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, hq, zero_mul]
    have hcardQ : Nat.card (𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) = ℓ ^ Module.finrank ℚ F := by
      have h1 := Ideal.absNorm_span_singleton ((ℓ ^ 1 : ℕ) : 𝓞 F)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
      rw [h1]
      have : ((ℓ ^ 1 : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (ℓ : ℤ) := by simp
      rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
      simp
    let eq : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) ≃ {g : Over.mk x ⟶ A // g ^ ℓ = 1} :=
      Equiv.ofBijective (fun a => ⟨f a, by rw [← hns, hkill, h0]⟩)
        ⟨fun a b hab => hinj (congrArg Subtype.val hab),
         fun g => by obtain ⟨a, ha⟩ := hsurj g.1 (by rw [pow_one]; exact g.2); exact ⟨a, Subtype.ext ha⟩⟩
    rw [← Nat.card_congr eq, Nat.card_fun, hcardQ, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]
  have hℓ1 : 1 < ℓ := hℓ.one_lt
  have hdim : 2 * B.dim = h * Module.finrank ℚ F := by
    have := htors.symm.trans hL2
    exact Nat.pow_right_injective hℓ.two_le this
  have hd0 : Module.finrank ℚ F ≠ 0 := Module.finrank_pos.ne'
  rw [hker, ← hE]
  apply Nat.pow_left_injective hd0
  change deg (A := B) (B := B) (ψ c) ^ Module.finrank ℚ F = ((Algebra.norm ℤ c).natAbs ^ h) ^ Module.finrank ℚ F
  rw [hD, hdim, pow_mul]

end GlobalTheory.AVCount
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  first | (exact @GlobalTheory.AVCount.card_ker_eq_norm_pow) | (exact GlobalTheory.AVCount.card_ker_eq_norm_pow) | (intros; apply GlobalTheory.AVCount.card_ker_eq_norm_pow  <;> assumption)
end
