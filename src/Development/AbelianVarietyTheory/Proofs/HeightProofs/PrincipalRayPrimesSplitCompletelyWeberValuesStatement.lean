module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n))) (S : Finset ℕ), ∀ (π : 𝓞 K) (p : ℕ), p.Prime → p ∉ S → Ideal.absNorm (Ideal.span {π}) = p → π - 1 ∈ Ideal.span {(n : 𝓞 K)} → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K (weberSet L n))) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K (weberSet L n)))) = Ideal.span {π}}.ncard = Module.finrank K (IntermediateField.adjoin K (weberSet L n)) := by
  first | exact @GlobalTheory.WeberSplitAny.splits_completely_of_three_le | exact GlobalTheory.WeberSplitAny.splits_completely_of_three_le | (intros; apply GlobalTheory.WeberSplitAny.splits_completely_of_three_le <;> assumption)
