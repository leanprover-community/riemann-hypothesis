module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionFamily

section General

variable {S : Scheme.{0}}

noncomputable def torsionLift (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    T ⟶ torsion G n :=
  pullback.lift f (toUnit T) (by rw [GlobalTheory.GrpTangent.comp_mulN, hf, Hom.one_def])

theorem torsionLift_ι (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    torsionLift G f n hf ≫ torsion.ι G n = f :=
  pullback.lift_fst _ _ _

theorem torsion_ι_pow (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GlobalTheory.GrpTangent.comp_mulN, Hom.one_def]
  exact pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))

end General

end GlobalTheory.TorsionFamily
