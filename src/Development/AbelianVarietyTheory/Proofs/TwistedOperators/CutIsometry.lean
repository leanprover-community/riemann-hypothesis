module

public import Formalism.SatakeDualWeyl.Statement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.TruncationIsometry

open Matrix

theorem cT_cut {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε)
    (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
      ε • Formalism.UG.cT σ M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hσ]
  · have h' : j ≠ i := fun e => h e.symm
    simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne h']

theorem cut_isometry {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε) (hε : ε * ε = ε)
    (J M : Matrix (Fin n) (Fin n) R) (hM : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J *
      (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) = J := by
  have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε, sub_self]
  have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, mul_one, h2, sub_zero]
  rw [cT_cut σ ε hσ M]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, smul_smul, hM, hε, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.TruncationIsometry
