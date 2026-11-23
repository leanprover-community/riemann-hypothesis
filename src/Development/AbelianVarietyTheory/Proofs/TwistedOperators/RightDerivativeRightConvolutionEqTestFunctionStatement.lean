module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunction
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.right_derivative_rightConvolution_eq_test_function : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  first | exact @GlobalTheory.ConvRDeriv.Rder_convR | exact GlobalTheory.ConvRDeriv.Rder_convR | (intros; apply GlobalTheory.ConvRDeriv.Rder_convR <;> assumption)
