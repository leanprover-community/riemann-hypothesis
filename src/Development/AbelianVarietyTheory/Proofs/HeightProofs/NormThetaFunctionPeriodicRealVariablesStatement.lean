module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormThetaFunctionPeriodicRealVariables
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_thetaFunction_periodic_real_variables : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → (∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) → ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U) → ∀ (V W : HSp D) (f : WA V W → ℂ), IsThetaFun ψ V W f → ∀ γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  first | exact @GlobalTheory.FockCompare.ThetaPeriod.norm_periodic | exact GlobalTheory.FockCompare.ThetaPeriod.norm_periodic | (intros; apply GlobalTheory.FockCompare.ThetaPeriod.norm_periodic <;> assumption)
