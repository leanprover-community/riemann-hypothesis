module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverse
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

@[expose] public section

open Set Filter Topology Metric

theorem _root_.GlobalTheory.T.analytic_doubling_map_local_inverse : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (d : B × V → V), AnalyticAt ℂ d (b₀, 0) → d (b₀, 0) = 0 → HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0) → ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | exact GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | (intros; apply GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse <;> assumption)
