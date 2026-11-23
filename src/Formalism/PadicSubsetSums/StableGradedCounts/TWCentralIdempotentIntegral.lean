module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegral
public import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
public import Mathlib.LinearAlgebra.Matrix.Trace
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.TW

theorem isIntegral_trace_of_isIntegral {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  apply GlobalTheory.LieDisc.isIntegral_trace_of_isIntegral_matrix <;> assumption

theorem central_idempotent_integral_twist : CentralIdempotentIntegral := by
  intro K _ _ G _ _ e he hc g
  classical
  set x : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hx
  have hpow : ∀ k : ℕ, x ^ (k + 1) = e * MonoidAlgebra.single (g⁻¹ ^ (k + 1)) 1 := by
    intro k
    induction k with
    | zero => simp [hx]
    | succ k ih =>
      rw [pow_succ, ih, hx, mul_assoc, ← mul_assoc (MonoidAlgebra.single _ _) e, ← hc,
        mul_assoc, ← mul_assoc e e, he, MonoidAlgebra.single_mul_single, ← pow_succ, one_mul]
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hxe : x ^ Fintype.card G = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
    rw [hk, Nat.succ_eq_add_one, hpow, ← Nat.succ_eq_add_one, ← hk, pow_card_eq_one,
      ← MonoidAlgebra.one_def, mul_one]
  have hei : IsIntegral ℤ e := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (by simp), ?_⟩
    simp [pow_two, he]
  have hxi : IsIntegral ℤ x := IsIntegral.of_pow hcard (hxe ▸ hei)
  have hMi : IsIntegral ℤ (Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x) :=
    hxi.map (A := K) (Algebra.leftMulMatrix (MonoidAlgebra.basis G K))
  have htr : (Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x).trace
      = (Fintype.card G : K) * e.coeff g := by
    have : ∀ i : G, Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x i i = e.coeff g := by
      intro i
      rw [Algebra.leftMulMatrix_eq_repr_mul, MonoidAlgebra.basis_apply]
      change (x * MonoidAlgebra.single i 1).coeff i = _
      simp [hx]
    simp [Matrix.trace, this]
  rw [← htr]
  exact isIntegral_trace_of_isIntegral _ hMi

end Formalism.IrreducibleCountingLemmas.TW
