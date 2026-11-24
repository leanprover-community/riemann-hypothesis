module

public import Development.EtaleCohomology.EtaleSheaves.IntPBPf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntFibPf

lemma eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

lemma eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

lemma isPushout_quot (A : Type) [CommRing A] [IsLocalRing A] {B : CommRingCat.{0}} (ψ : CommRingCat.of A ⟶ B) :
    IsPushout ψ (CommRingCat.ofHom (IsLocalRing.residue A))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map
        : IsLocalRing.ResidueField A →+* _)) := by
  have w : CommSq ψ (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map : IsLocalRing.ResidueField A →+* _)) := by
    constructor; ext a; rfl
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
      (Ideal.Quotient.lift ((IsLocalRing.maximalIdeal A).map ψ.hom) s.inl.hom ?_)) ?_ ?_ ?_)
  · rename_i s; intro a ha
    have hle : ((IsLocalRing.maximalIdeal A).map ψ.hom) ≤ RingHom.ker s.inl.hom := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      have h1 := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
      simp only [Ideal.mem_comap, RingHom.mem_ker, h1,
        (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
    exact hle ha
  · intro s; ext b; rfl
  · intro s; ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have h1 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    exact h1
  · intro s m h1 h2
    ext b
    have := congrArg (fun f => f.hom b) h1
    exact this

theorem IntFib_of : LateralTheory.E.IntPBPf.IntFib := by
  intro A _ _ X p hp
  have : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, ?_, ?_⟩
  · rw [← IsIntegralHom.SpecMap_iff, hψ]; infer_instance
  · intro q i h
    have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot A ψ)
    have hP' : IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) ≫ X.isoSpec.inv) _ p
        (LateralTheory.E.t_E2Cut.cpt A) :=
      hP.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by simp [hψ]) (by simp)
    rw [← hP'.isoPullback_inv_fst, Functor.map_comp, Functor.map_comp]
    exact eqv_comp _ _ _ (eqv_iso (sch.mapIso hP'.isoPullback.symm) _)
      (eqv_comp _ _ _ h (eqv_iso (sch.mapIso X.isoSpec.symm) _))

end LateralTheory.E.IntFibPf
