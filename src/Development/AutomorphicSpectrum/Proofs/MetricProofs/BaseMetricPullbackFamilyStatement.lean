module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamily
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.base_metric_pullback_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (e : ℕ) (X' : Type) [TopologicalSpace X'] (A' : FinHolAtlas e X') (U' : X' → Set X') (lf : X' → X' → (Σ k, ι k) → ℂ) (pr' : X' → BM.Rb.X) (l : Fin BM.q), HoloMap A' BM.Rb.A pr' → (∀ x, IsOpen (U' x)) → (∀ x, x ∈ U' x) → (∀ x p, A'.HoloOn (U' x) (fun y => lf x y p)) → (∀ x, ∀ y ∈ U' x, SameOrbit (lf x y) (lf y y)) → (∀ x, pr' x ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, pr' x' ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x')) (lf x' x') p ≠ 0) → IsNull A' {x | pr' x ∈ BM.O l ∧ (pr' x ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x)) (lf x x) p = 0)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell <;> assumption)
