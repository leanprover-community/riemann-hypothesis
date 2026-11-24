module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.WeilBound.CoreStatements.RationalSupMetrics.ValuationUniqueOnForms
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem hasVal_read_of_rep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w :=
  MultiProjectiveCoordinates.valuation_unique_on_forms

end GlobalTheory.CompanionTheory.Ar.Small
