module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLiftConvergesContinuousGrowthDeriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ (∀ f, Continuous fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∧ (∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ h, ‖∫ g in 𝓕, κ f g h * F g ∂μ‖ ≤ C * (height θ W h : ℝ) ^ N) ∧ ∀ τ, ∀ X ∈ lieAt W τ, ∀ f f', (∀ g h, HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0) → ∀ h, HasDerivAt (fun t : ℝ => ∫ g in 𝓕, κ f g (h * oneP θ W τ X t) * F g ∂μ) (∫ g in 𝓕, κ f' g h * F g ∂μ) 0 := by
  first | exact @GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv | exact GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv | (intros; apply GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv <;> assumption)
