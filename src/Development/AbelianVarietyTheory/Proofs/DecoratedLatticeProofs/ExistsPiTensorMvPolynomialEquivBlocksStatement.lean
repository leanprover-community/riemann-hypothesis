module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocks
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

theorem _root_.GlobalTheory.T.exists_piTensorMvPolynomialEquiv_blocks : ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  first | exact @GlobalTheory.BlockPoly.exists_blockEquiv | exact GlobalTheory.BlockPoly.exists_blockEquiv | (intros; apply GlobalTheory.BlockPoly.exists_blockEquiv <;> assumption)
