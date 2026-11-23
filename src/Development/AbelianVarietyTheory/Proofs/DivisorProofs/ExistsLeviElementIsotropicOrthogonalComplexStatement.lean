module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementIsotropicOrthogonalComplex
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

@[expose] public section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  first | exact @GlobalTheory.levi_element_cpx | exact GlobalTheory.levi_element_cpx | (intros; apply GlobalTheory.levi_element_cpx <;> assumption)
