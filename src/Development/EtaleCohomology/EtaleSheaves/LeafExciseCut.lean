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
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8.ExciseCut

def relMap (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) (i n : ℤ) :
    HK (ZMod q) (mappingCone ((chains _).map (sch.map ι))) (tw q i) n →+
      HK (ZMod q) (mappingCone ((chains _).map (sch.map ι'))) (tw q i) n :=
  HK.pull (ZMod q) (mappingCone.map ((chains _).map (sch.map ι')) ((chains _).map (sch.map ι))
    ((chains _).map (sch.map g)) ((chains _).map (sch.map f)) (by simp only [← Functor.map_comp, w])) (tw q i) n

def LeafConeZero : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R φ F n)) → ∀ n, Subsingleton (HK R (mappingCone φ) F n)

end LateralTheory.E.E8.ExciseCut
