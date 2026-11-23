module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_span_tprod_of_commute_at_each_place : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V W : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (R : ∀ τ, Set ((V τ →ₗ[ℂ] V τ) × (W τ →ₗ[ℂ] W τ))) (Q : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ W), (∀ τ, ∀ p ∈ R τ, Q ∘ₗ PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1) = PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : W σ →ₗ[ℂ] W σ)) τ p.2) ∘ₗ Q) → Q ∈ Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, ∀ p ∈ R τ, t τ ∘ₗ p.1 = p.2 ∘ₗ t τ) ∧ T = PiTensorProduct.map t} := by
  first | exact @GlobalTheory.PiTensorCommute.mem_span_map_of_commute | exact GlobalTheory.PiTensorCommute.mem_span_map_of_commute | (intros; apply GlobalTheory.PiTensorCommute.mem_span_map_of_commute <;> assumption)
