module

public import Mathlib.RepresentationTheory.Coinduced
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

def funDiagRepresentation (X : Type*) [MulAction G X] (ρ : Representation k G V) :
    Representation k G (X → V) where
  toFun g :=
    { toFun := fun F x => ρ g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (ρ g) _ _
      map_smul' := fun c F => funext fun x => map_smul (ρ g) c _ }
  map_one' := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp [mul_smul]

abbrev funDiagRep {k G : Type u} [CommRing k] [Group G] (X : Type u) [MulAction G X]
    (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (funDiagRepresentation X A.ρ)

end GroundTheory.ProfCoh
