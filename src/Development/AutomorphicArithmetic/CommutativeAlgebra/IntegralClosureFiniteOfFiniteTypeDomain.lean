module

public import Development.EtaleCohomology.EtaleSheaves.LeafIntClosureAlgPf
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherCharP
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherReduction
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem UpperTheory.integralClosure_finite_of_finiteType_domain :
    LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite := by
  intro Ω L _ _ _ u _ hfd
  have : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    .adjoin_of_finite (Set.finite_singleton u)
  refine GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_of_forall_mvPolynomial
    Ω (Algebra.adjoin Ω {u}) (IntermediateField.adjoin Ω {u}) L ?_
  intro s L' _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpr | rfl
  · haveI : Fact p.Prime := ⟨hpr⟩
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charP Ω p s L'
  · haveI : CharZero Ω := CharP.charP_to_charZero Ω
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charZero Ω s L'
