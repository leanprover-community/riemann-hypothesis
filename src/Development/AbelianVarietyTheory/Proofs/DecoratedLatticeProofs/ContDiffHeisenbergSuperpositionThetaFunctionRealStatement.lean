module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergSuperpositionThetaFunctionReal
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.contDiff_heisenbergSuperposition_thetaFunction_real : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → WO S T) (a : Ω → ℂ), Measurable v → Integrable a μ → ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F (v x) ∂μ) := by
  first | exact @GlobalTheory.SuperposSmooth.main | exact GlobalTheory.SuperposSmooth.main | (intros; apply GlobalTheory.SuperposSmooth.main <;> assumption)
