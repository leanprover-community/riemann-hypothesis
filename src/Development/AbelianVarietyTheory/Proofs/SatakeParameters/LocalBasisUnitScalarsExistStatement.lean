module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalBasisUnitScalarsExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.local_basis_unit_scalars_exist : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first | exact @GlobalTheory.locBasisW_clear_den | exact GlobalTheory.locBasisW_clear_den | (intros; apply GlobalTheory.locBasisW_clear_den <;> assumption)
