module

public import Development.EtaleCohomology.EtaleSheaves.SpreadingOutLocallyQuasiFinite
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
import Mathlib.RingTheory.SimpleRing.Principal
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
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.QuasiFiniteAtDescent

theorem quasiFiniteAt_of_isOpen_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (a : X) (hza : f.fiberι y z = a) (hz : IsOpen ({z} : Set (f.fiber y))) :
    f.QuasiFiniteAt a := by
  have hy : y = f a := by
    rw [← hza, ← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst hy
  have : z = f.asFiber a := by
    apply (f.fiberι (f a)).isEmbedding.injective
    rw [hza, Scheme.Hom.fiberι_asFiber]
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← this]
  exact hz

theorem qf_of_fiberMap {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B)
    [LocallyOfFiniteType g] [LocallyOfFiniteType γ] (x : CA)
    (φ : γ.fiber (γ x) ⟶ g.fiber (vB (γ x))) (hφ : UniversallyOpen φ)
    (e : φ ≫ g.fiberι (vB (γ x)) = γ.fiberι (γ x) ≫ vA) (hx : γ.QuasiFiniteAt x) :
    g.QuasiFiniteAt (vA x) := by
  have hx' : IsOpen ({γ.asFiber x} : Set (γ.fiber (γ x))) :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx
  have hopen := φ.isOpenMap _ hx'
  have h2 : IsOpen ({φ (γ.asFiber x)} : Set (g.fiber (vB (γ x)))) := by
    convert hopen using 1
    exact (Set.image_singleton).symm
  refine quasiFiniteAt_of_isOpen_fiber g (vB (γ x)) (φ (γ.asFiber x)) (vA x) ?_ h2
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]

theorem LeafQFAtDescend_of : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend := by
  intro CA CB A B γ g vA vB sq hg x hx
  have : LocallyOfFiniteType γ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hg
  have sqF := isPullback_fiberToSpecResidueField_of_isPullback sq (γ x)
  have hφ := MorphismProperty.of_isPullback (P := @UniversallyOpen) sqF.flip inferInstance
  refine qf_of_fiberMap γ g vA vB x _ hφ ?_ hx
  exact pullback.lift_fst _ _ _

end LateralTheory.E.QuasiFiniteAtDescent
