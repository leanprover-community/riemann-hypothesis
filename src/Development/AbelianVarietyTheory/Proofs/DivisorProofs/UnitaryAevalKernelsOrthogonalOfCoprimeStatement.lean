module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAevalKernelsOrthogonalOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitary_aeval_kernels_orthogonal_of_coprime : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 →
    ∀ (q₁ q₂ a b : K[X]), a * q₁ + b * q₂ = 1 → aeval γ (q₁ * q₂) = 0 →
    ∀ (V : Submodule K (Fin n → K)), (∀ x, x ∈ V ↔ aeval γ q₁ *ᵥ x = 0) →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (bs : Module.Basis ι K V),
    (Matrix.of fun i j => ∑ k, σ ((bs i : Fin n → K) k) * (bs j : Fin n → K) k).det ≠ 0 →
    ∀ x ∈ V, ∀ y : Fin n → K, aeval γ q₂ *ᵥ y = 0 → ∑ k, σ (x k) * y k = 0 := by
  first | exact @GlobalTheory.UnitaryOrth.ker_orthogonal_of_coprime | exact GlobalTheory.UnitaryOrth.ker_orthogonal_of_coprime | (intros; apply GlobalTheory.UnitaryOrth.ker_orthogonal_of_coprime <;> assumption)
