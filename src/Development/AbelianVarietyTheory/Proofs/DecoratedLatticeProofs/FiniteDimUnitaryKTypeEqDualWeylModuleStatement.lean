module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModule
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms
open scoped InnerProductSpace Matrix

theorem _root_.GlobalTheory.T.finite_dim_unitary_K_type_eq_dual_weyl_module : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (lamH : Fin k → ℝ), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ (Formalism.QuantumDeterminants.lowK (allPos k) lamH) ⊤ → (∀ i : Fin k, -lamH (Fin.rev i) = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∃ (j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ H), (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ a a', normFock lam (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (σ (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  first | exact @GlobalTheory.DualWeylType.dual_weyl_type | exact GlobalTheory.DualWeylType.dual_weyl_type | (intros; apply GlobalTheory.DualWeylType.dual_weyl_type <;> assumption)
