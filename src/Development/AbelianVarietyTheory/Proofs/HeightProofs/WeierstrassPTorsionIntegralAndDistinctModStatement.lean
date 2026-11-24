module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.weierstrassP_torsion_integral_and_distinct_mod : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → Odd m → (m : ℂ)⁻¹ ∈ W → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧ ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  first | exact @GlobalTheory.TorsionIntegral.torsion_integral_distinct | exact GlobalTheory.TorsionIntegral.torsion_integral_distinct | (intros; apply GlobalTheory.TorsionIntegral.torsion_integral_distinct <;> assumption)
