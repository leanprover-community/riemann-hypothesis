module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArSys
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.B1abs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace UpperTheory.V.Pa

theorem b1Ar : FirstOrderDualArithmeticBound := by
  intro hcoh l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T x0 x k al hS hloc _ hρ hN4 hE hD
  obtain ⟨d', hsum, hab⟩ := hloc
  obtain ⟨A⟩ := arSys hcoh l L Ω s V0 O n r T x0 hS
  refine b1abs l (locOf r) (globOf r V0) T n x k al _ V0.frame.D0 A d' s.odd ?_ hab
    (arPl hcoh l L Ω s V0 O n r hS).1 hρ hN4 hE hD
  rw [← hsum]
  first
    | exact (finsum_eq_sum_of_fintype _).symm
    | (convert (finsum_eq_sum_of_fintype d').symm)

end UpperTheory.V.Pa
