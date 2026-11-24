module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansion
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.cyclotomic_divided_power_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | exact GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | (intros; apply GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one <;> assumption)
