module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorAdjointDecaying
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gelfand_operator_adjoint_decaying : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ (Z : Submodule ℂ (GA D V → ℂ)), (∀ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ k, ∀ F ∈ Decay θ V ⊓ Z, ∃ F' ∈ Decay θ V ⊓ Z, ∀ φ, IsMod θ V φ → ∫ g in 𝓕, gelf θ V τ k φ g * F g ∂μ = ∫ g in 𝓕, φ g * F' g ∂μ := by
  first | exact @GlobalTheory.Mem.GelfParts.gelf_by_parts | exact GlobalTheory.Mem.GelfParts.gelf_by_parts | (intros; apply GlobalTheory.Mem.GelfParts.gelf_by_parts <;> assumption)
