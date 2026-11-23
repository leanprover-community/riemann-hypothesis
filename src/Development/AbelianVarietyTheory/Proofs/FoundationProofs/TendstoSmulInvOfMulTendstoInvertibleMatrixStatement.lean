module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix : ∀ (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ) (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ), L.det ≠ 0 → Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L) → Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0) → Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | exact GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | (intros; apply GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible <;> assumption)
