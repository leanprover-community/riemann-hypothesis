module

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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyClauseStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem val_of_even {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {M : ℕ} (hM : Even M)
    (h : B.valuation ((4 : ℕ) : Ω) < 1) : B.valuation (M : Ω) < 1 := by
  have h2 : B.valuation (2 : Ω) < 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (1 : _) ≤ B.valuation (2 : Ω) * B.valuation (2 : Ω) := one_le_mul hc hc
    rw [← map_mul] at h4
    have : ((4 : ℕ) : Ω) = 2 * 2 := by norm_num
    rw [this] at h
    exact absurd h (not_lt.mpr h4)
  obtain ⟨k, rfl⟩ := hM
  have hk : B.valuation (k : Ω) ≤ 1 := by
    exact B.valuation_le_one (k : B)
  have : ((k + k : ℕ) : Ω) = 2 * (k : Ω) := by push_cast; ring
  rw [this, map_mul]
  exact mul_lt_one_of_lt_of_le h2 hk
