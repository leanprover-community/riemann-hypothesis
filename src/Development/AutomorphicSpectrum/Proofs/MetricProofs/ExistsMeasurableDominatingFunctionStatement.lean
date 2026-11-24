module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunction
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

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.cuspWeight_factors_through_measurable_log_bounded : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt), ∃ (G : X.M.Xc → ℝ) (C : ℝ), @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G) ∧ (∀ x ∈ X.S.R.Yo, |G x| ≤ C + C * Real.log (X.S.R.r x)) ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → X.Cd.cuspWeight z = G (X.M.proj z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends | exact GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends <;> assumption)
