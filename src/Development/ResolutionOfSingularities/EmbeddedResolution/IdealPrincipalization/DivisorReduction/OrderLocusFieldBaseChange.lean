module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_withBoundary_baseChange_eq_preimage (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m := by
  haveI : CharZero T.base := hV.charZero
  haveI : CharZero K := (RingHom.charZero_iff f.injective).mp hV.charZero
  haveI : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal m

end FunctorialResolution.EmbeddedResolution
