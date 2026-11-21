import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

section
namespace GlobalTheory.LocalHomExtension

theorem exists_isLocalHom_extension {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C]
    [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : Valuation.Integers v O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral)
    (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A O := ι.toAlgebra
  let : Algebra A C := ((algebraMap O C).comp ι).toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  have : Algebra.IsIntegral A B := ⟨hint⟩

  let f : B →ₐ[A] C := IsAlgClosed.lift

  have hO : ∀ b : B, ∃ o : O, algebraMap O C o = f b := fun b => by
    have h1 : IsIntegral A (f b) := (Algebra.IsIntegral.isIntegral b).map f
    exact hv.exists_of_le_one (hv.mem_of_integral h1.tower_top)
  choose g hg using hO
  have inj := hv.hom_inj
  let ι' : B →+* O :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => inj (by rw [hg, map_add, map_add, hg, hg]) }
  have hcomp : ι'.comp φ = ι := by
    ext a
    apply inj
    show algebraMap O C (g (φ a)) = algebraMap O C (ι a)
    rw [hg]
    exact f.commutes a
  refine ⟨ι', ?_, hcomp⟩

  have hA : (IsLocalRing.maximalIdeal O).comap ι = IsLocalRing.maximalIdeal A :=
    ((IsLocalRing.local_hom_TFAE ι).out 0 4).mp (inferInstance : IsLocalHom ι)
  have hp : (((IsLocalRing.maximalIdeal O).comap ι').comap (algebraMap A B)).IsMaximal := by
    rw [Ideal.comap_comap, show ι'.comp (algebraMap A B) = ι from hcomp, hA]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hpm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap ((IsLocalRing.maximalIdeal O).comap ι') hp
  exact ((IsLocalRing.local_hom_TFAE ι').out 0 4).mpr (IsLocalRing.eq_maximalIdeal hpm)

end GlobalTheory.LocalHomExtension
end

section
set_option autoImplicit false

namespace GlobalTheory.CharDepth

open IsLocalRing Formalism.L2.Pj

theorem exists_local_extension_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O) (φ : A →+* B) (hφ : Function.Injective φ)
    (hint : φ.IsIntegral) (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_21; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 v hv φ hφ hint ι h_21 hι; exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension)
  | exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | (apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension ..)

theorem ValExt.exists_local_extension :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∀ (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ ι' : T'.V →+* X.O, IsLocalHom ι' ∧ ι'.comp φ = X.ι := by
  intro T T' φ hφ hfin p _ X
  haveI := X.ι_local
  refine exists_local_extension_of_integral X.v X.ints φ hφ hfin.to_isIntegral X.ι ?_
  have h : (algebraMap X.O X.C).comp X.ι = X.ιF.comp (algebraMap T.V T.Fr) := by
    ext x; exact (X.comp x).symm
  rw [h, RingHom.coe_comp]
  exact X.ιF.injective.comp (IsFractionRing.injective T.V T.Fr)

end GlobalTheory.CharDepth
end
