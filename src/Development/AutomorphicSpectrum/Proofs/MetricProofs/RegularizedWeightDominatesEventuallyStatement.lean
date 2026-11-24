module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventually
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.regularized_weight_dominates_eventually : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ᶠ t' in 𝓝[>] (0 : ℝ), (∀ x, S'.B.ph x ≤ S'.bregWeight t' x) ∧ M.atlas.Smooth (S'.bregWeight t') ∧ ∀ B p q : ℕ, IsSmoothHerm (MUc Hd S' B p q t') ∧ (MUc Hd S' B p q t').a = (q : ℤ) • muTwDeg Hd B + (p : ℤ) • D.a' ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((MUc Hd S' B p q t').h z) = q * (Real.log (S'.ref.h z) + S'.bregWeight t' (M.proj z) + ∑ r ∈ D.SB B, Real.log (D.vertFactor r z)) + p * Real.log (D.A'.h z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth | exact GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth <;> assumption)
