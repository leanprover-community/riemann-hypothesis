module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagComplementPosDefFactorization
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

theorem _root_.GlobalTheory.T.hermitian_flag_complement_posDef_factorization : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  first | exact @GlobalTheory.schur_complement_step_cpx | exact GlobalTheory.schur_complement_step_cpx | (intros; apply GlobalTheory.schur_complement_step_cpx <;> assumption)
