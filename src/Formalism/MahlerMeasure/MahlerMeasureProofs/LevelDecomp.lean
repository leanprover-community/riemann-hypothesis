module

public import Formalism.MahlerMeasure.LevelSum
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.MahlerMeasure.GoodCount

@[expose] public section

namespace Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

theorem ld_biHom_of_euler [CharZero k] {a b : ℕ} {g : MvPolynomial σ k}
    (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) : BiHom w e a b g := by
  classical
  unfold BiHom
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hterm : ∀ i : σ, AddMonoidAlgebra.coeff (X i * pderiv i g) m = (m i : k) * AddMonoidAlgebra.coeff g m := by
    intro i
    rw [MvPolynomial.coeff_X_mul']
    split_ifs with hs
    · have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
      have e1 : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hmi)
      have e2 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : k) + 1 = (m i : k) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one, Nat.sub_add_cancel hmi]
      rw [MvPolynomial.coeff_pderiv, e1, e2, mul_comm]
    · simp at hs
      simp [hs]
  have key : ∀ (v : Fin r → σ) (n : ℕ), ∑ c, X (v c) * pderiv (v c) g = (n : k) • g → ∑ c, m (v c) = n := by
    intro v n hv
    have hcoef := congrArg (AddMonoidAlgebra.coeff · m) hv
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at hcoef
    simp only [hterm] at hcoef
    rw [← Finset.sum_mul] at hcoef
    have hc := mul_right_cancel₀ hm hcoef
    exact_mod_cast hc
  exact ⟨key w a hW, key e b hE⟩

end

open Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {σ : Type}


section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

end


variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ} {w e : Fin r → σ}


end Formalism.GM
