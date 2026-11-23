module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem closedSub_flat_of_quotient_flat : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  intro V _ X _ p J h
  have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : (J.subschemeι ≫ p).appTop.hom =
      (J.subschemeObjIso U).inv.hom.comp
        (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) := by
    have h2 := J.subschemeι_app U
    have h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv := h2
    rw [Scheme.Hom.comp_appTop, h3]
    ext x
    change (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) =
      (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))
    rw [Iso.hom_inv_id_apply]
  rw [e]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h

end GlobalTheory
