module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescoping
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix


theorem _root_.GlobalTheory.T.intersection_number_telescoping : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) → IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 → I P (n + 1) (fun j => if (j : ℕ) < k then a else A') - I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') = -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope <;> assumption)
