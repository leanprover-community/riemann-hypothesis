module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanOfCoefficientSpan
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.thetaFunction_mem_span_of_coefficientSpan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ 𝒢 𝒯 : Set (WO S T → ℂ), (∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) → (∀ Ψ ∈ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f)) → (∀ ℓ, InvForm ψ S T a ℓ → coef ψ S T a ℓ f ∈ Submodule.span ℂ 𝒢) → f ∈ Submodule.span ℂ 𝒯 := by
  first | exact @GlobalTheory.DownLift.SplitCoef.Decomp.mem_span_of_coef_mem_span | exact GlobalTheory.DownLift.SplitCoef.Decomp.mem_span_of_coef_mem_span | (intros; apply GlobalTheory.DownLift.SplitCoef.Decomp.mem_span_of_coef_mem_span <;> assumption)
