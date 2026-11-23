module

public import Statements
public import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
public import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
  UpperTheory.FinalTheorems.everyCharacter

theorem riemannHypothesis : RiemannHypothesis :=
  Claim.zeta LFunction_ne_zero_of_half_lt_re

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
  Claim.strip LFunction_ne_zero_of_half_lt_re

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by
  intro N _ χ _ s h₀ h₁ hz
  exact LFunction_eq_zero_re N χ s h₀ h₁ hz
