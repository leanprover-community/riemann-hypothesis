module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace GlobalTheory.PolynomialPushoutEquivalence

theorem eqv_iso (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n

  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp (R : Type) [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n

  have e : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext (pull_comp R f g F n)
  rw [e]
  exact (hf n).comp (hg n)

theorem isPushout_poly {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPushout (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (Polynomial.mapRingHom φ)) (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) := by

  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra (Polynomial A) (Polynomial B) := Polynomial.algebra A B
  exact CommRingCat.isPushout_of_isPushout A (Polynomial A) B (Polynomial B)

theorem main (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv (ZMod q) (E := sp (Polynomial A')) (spMap Polynomial.C) (tw q i)) :
    Eqv (ZMod q) (sch.map (pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp))) (tw q i) := by

  set φ : A →+* A' := (Spec.preimage s).hom with hφ
  have hs : s = Spec.map (CommRingCat.ofHom φ) := by simp [φ]

  have sq : IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s := by
    rw [Category.comp_id, hs]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_poly φ)

  have e : pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp) =
      sq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')) ≫
        inv (pullback.snd (𝟙 (Spec (CommRingCat.of A))) s) := by
    rw [← Category.assoc, IsIso.eq_comp_inv, sq.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp _ _ _ _ (eqv_iso _ _ _) (eqv_comp _ _ _ _ h (eqv_iso _ _ _))

end GlobalTheory.PolynomialPushoutEquivalence

end
