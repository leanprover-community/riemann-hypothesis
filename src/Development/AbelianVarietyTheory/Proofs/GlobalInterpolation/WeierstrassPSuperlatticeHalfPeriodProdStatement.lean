module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeierstrassPSuperlatticeHalfPeriodProd
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

@[expose] public section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.weierstrassP_superlattice_half_period_prod : ∀ (L L' : PeriodPair) (T : Finset ℂ) (w : ℂ), L.lattice ≤ L'.lattice → (∀ t ∈ T, t ∈ L'.lattice ∧ t ∉ L.lattice) → (∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L.lattice → t = t') → (∀ x ∈ L'.lattice, x ∈ L.lattice ∨ ∃ t ∈ T, x - t ∈ L.lattice) → 2 * w ∈ L.lattice → w ∉ L'.lattice → ∀ z, z ∉ L'.lattice → (L'.weierstrassP z - L'.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t) = (L.weierstrassP z - L.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t)) := by
  exact @GlobalTheory.HalfPeriodProduct.wp_half_period_prod
