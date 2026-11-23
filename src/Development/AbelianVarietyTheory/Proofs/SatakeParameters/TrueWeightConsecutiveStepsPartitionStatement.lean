module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.KerJ NumberField Classical

theorem _root_.GlobalTheory.T.trueWeight_consecutive_steps_partition : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (i : ℕ), i < D.R.m → ∃ n : D.what₂.Tau → ℕ, (∀ τ r, (lamTG M i τ).natW r + n τ = nuT D u i τ r) ∧ (∀ τ, (lamTG M i τ).detShift + C.sSharp i τ = n τ) ∧ (∀ τ r, (lamTG M (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (fun τ r => (lamTG M i τ).natW r + n τ) τ r) ∧ ∀ τ, (lamTG M (i + 1) τ).detShift = -C.sDiv i τ := by
  first | exact @GlobalTheory.KerWtStep.trueWt_step | exact GlobalTheory.KerWtStep.trueWt_step | (intros; apply GlobalTheory.KerWtStep.trueWt_step <;> assumption)
