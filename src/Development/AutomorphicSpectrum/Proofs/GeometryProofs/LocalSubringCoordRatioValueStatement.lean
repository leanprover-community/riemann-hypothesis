module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringCoordRatioValue
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.local_subring_coord_ratio_value : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ (A : Subring Ω) (_ : IsLocalRing A), (∀ (k : K) (a b : J k), z ⟨k, b⟩ ≠ 0 → y ⟨k, b⟩ ≠ 0 ∧ y ⟨k, a⟩ / y ⟨k, b⟩ ∈ A) ∧ (∀ n : ℕ, (n : L) ≠ 0 → (n : Ω) ≠ 0 ∧ (n : Ω)⁻¹ ∈ A) ∧ ∀ s ∈ A, s⁻¹ ∈ A → s ≠ 0 → ∃ w : L, w ≠ 0 ∧ Small.HasVal y (0 : K → ℤ) s z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing | exact GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing <;> assumption)
