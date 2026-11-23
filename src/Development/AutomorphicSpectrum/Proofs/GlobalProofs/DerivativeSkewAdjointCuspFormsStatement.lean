module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivativeSkewAdjointCuspForms
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.derivative_skew_adjoint_cusp_forms : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (ψ χ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX ψ), GlobalTheory.CompanionTheory.HCCusp.io μ hθ χ⟫_ℂ = -⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ ψ, GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX χ)⟫_ℂ := by
  exact @GlobalTheory.CompanionTheory.HCCusp.inner_io_der_skew
