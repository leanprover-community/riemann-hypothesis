module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJointGenEigenspaceIdempotentPoly
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_joint_genEigenspace_idempotent_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  first | exact @GlobalTheory.exists_genEig_idem_poly | exact GlobalTheory.exists_genEig_idem_poly | (intros; apply GlobalTheory.exists_genEig_idem_poly <;> assumption)
