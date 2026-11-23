module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulMulSelfOfUnitaryConj
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary : ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  first | exact @GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | exact GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | (intros; apply GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj <;> assumption)
