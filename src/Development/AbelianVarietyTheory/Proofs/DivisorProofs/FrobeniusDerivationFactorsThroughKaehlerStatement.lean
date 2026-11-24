module

public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehler
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars

@[expose] public section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.frobeniusDerivation_factors_through_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  first | exact @GlobalTheory.DI.frobDeriv_factors_kaehler | exact GlobalTheory.DI.frobDeriv_factors_kaehler | (intros; apply GlobalTheory.DI.frobDeriv_factors_kaehler <;> assumption)
