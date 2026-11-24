module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertIdealSheafOfQuotientIdealTopStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionTensorPullbackRingHomBijectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem ker_kappa_xI_comap :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C))
      (U : Z.affineOpens),
      (letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = secAlg C h U ∧
         RingHom.ker (kappa A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))
           ((xI A B C J).comap (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) =
         J.map (Algebra.TensorProduct.map φ (AlgHom.id A B))) := by
  intro A B C _ _ _ _ _ J Z h U
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let g := h ≫ f
  let W := pullback.snd (str A B) g ⁻¹ᵁ (U : Z.Opens)
  let := (secAlg A g U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        have hs : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ U (by simp) =
            CommRingCat.ofHom (algebraMap A C) ≫
              (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) := by
          calc
            _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
                h.appLE ⊤ U (by simp) :=
              congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h f ⊤ U (by simp))
            _ = _ := (Scheme.ΓSpecIso_inv_naturality_assoc
              (CommRingCat.ofHom (algebraMap A C)) (h.appLE ⊤ U (by simp))).symm
        exact (congrArg (fun F => F.hom a) hs).symm }
  refine ⟨φ, rfl, ?_⟩
  have : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have hTensor : ((bc A B f h).appLE ⊤ W (by simp)).hom.comp (psi A B C) =
      (theta A B g U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
    have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (pullback.snd (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have hpsi (c : C) (b : B) : psi A B C (c ⊗ₜ[A] b) =
        (pullback.fst (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
        (pullback.snd (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
      have h1 := congrArg (fun F => F.hom b) eL
      have h2 := congrArg (fun F => F.hom c) eR
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      rw [h1, h2, ← map_mul, ← map_mul]
      simp [psi]
    have eF : (pullback.fst (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        (pullback.fst (str A B) g).appLE ⊤ W (by simp) := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
    have eS : (pullback.snd (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        h.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) g ≫ h)
        (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
      have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
      rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, mul_comm]
      let : Algebra A Γ(pullback (str A B) g, W) :=
        (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      symm
      change theta A B g U (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) g).app U).hom (secAlg C h U c) *
          ((pullback.fst (str A B) g).appLE ⊤ W (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B f h)) ⟨W, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine,
    GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, hTensor,
    ← Ideal.map_map, Ideal.comap_map_of_bijective _
      (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl

end GlobalTheory.HilbAff
