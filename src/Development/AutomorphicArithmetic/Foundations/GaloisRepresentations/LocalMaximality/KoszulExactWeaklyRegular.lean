module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RelativeK1Module
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct Pointwise

section
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ]
  {N N' : Type} [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N]
  [AddCommGroup N'] [Module R N'] [Module ℂ N'] [IsScalarTower ℂ R N']

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ] [Fintype κ]

end

theorem UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    Htpy → KoszulExactBelowLengthOfWeaklyRegular :=
  _root_.UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy
