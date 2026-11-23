module

public import Formalism.ConjugateSelfDual.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequality
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

theorem _root_.GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  first | (exact @GlobalTheory.Cong.eigen_small_sub_finite_approx) | (exact GlobalTheory.Cong.eigen_small_sub_finite_approx) | (intros; apply GlobalTheory.Cong.eigen_small_sub_finite_approx  <;> assumption)
