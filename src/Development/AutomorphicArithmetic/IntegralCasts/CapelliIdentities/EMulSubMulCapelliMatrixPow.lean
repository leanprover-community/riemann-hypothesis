module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.Qk36

@[reducible] noncomputable def gl : ℕ → Type :=
  fun n => Matrix (Fin n) (Fin n) ℂ

@[reducible] noncomputable def U : ℕ → Type :=
  fun n => by
    letI : LieRing (gl n) := LieRing.ofAssociativeRing
    letI : LieAlgebra ℂ (gl n) := LieAlgebra.ofAssociativeAlgebra
    exact UniversalEnvelopingAlgebra ℂ (gl n)

noncomputable def E : {n : ℕ} → Fin n × Fin n → gl n :=
  fun {n} a => Matrix.single a.1 a.2 1

noncomputable def e : {n : ℕ} → Fin n × Fin n → U n :=
  fun {n} a => by
    letI : LieRing (gl n) := LieRing.ofAssociativeRing
    letI : LieAlgebra ℂ (gl n) := LieAlgebra.ofAssociativeAlgebra
    exact UniversalEnvelopingAlgebra.ι ℂ (E a)

noncomputable def capelliMatrix : {n : ℕ} →
  Matrix (Fin n) (Fin n) (U n) :=
  fun {n} i j => e (i, j)

private theorem commutator_matrix_pow {R : Type*} [Ring R] {n : Nat}
    (M : Matrix (Fin n) (Fin n) R) (x : R) (a b : Fin n)
    (h : ∀ c d, x * M c d - M c d * x
      = (if b = c then M a d else 0) - (if d = a then M c b else 0))
    (k : Nat) (c d : Fin n) :
    x * (M ^ k) c d - (M ^ k) c d * x
      = (if b = c then (M ^ k) a d else 0) - (if d = a then (M ^ k) c b else 0) := by
  induction k generalizing d with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      sub_self]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, eq_comm (a := a), eq_comm (a := c)]
  | succ k ih =>
    have key : ∀ j, x * ((M ^ k) c j * M j d) - (M ^ k) c j * M j d * x
        = ((if b = c then (M ^ k) a j else 0) - (if j = a then (M ^ k) c b else 0)) * M j d
          + (M ^ k) c j * ((if b = j then M a d else 0) - (if d = a then M j b else 0)) := by
      intro j
      rw [← ih j, ← h j d]
      noncomm_ring
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun j _ => key j)]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;>
      simp only [h1, h2, if_true, if_false, Finset.sum_const_zero] <;> abel

private theorem E_comm {n : Nat} (a b c d : Fin n) :
    E (a, b) * E (c, d)
        - E (c, d) * E (a, b)
      = (if b = c then E (a, d) else 0)
        - (if d = a then E (c, b) else 0) := by
  have h : ∀ p q r s : Fin n, E (p, q) * E (r, s)
      = if q = r then E (p, s) else 0 := by
    intro p q r s
    unfold E
    split_ifs with hqr
    · subst hqr
      simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ hqr _
  rw [h, h]

private theorem e_comm {n : Nat} (a b c d : Fin n) :
    e (a, b) * e (c, d)
        - e (c, d) * e (a, b)
      = (if b = c then e (a, d) else 0)
        - (if d = a then e (c, b) else 0) := by
  letI : LieRing (gl n) := LieRing.ofAssociativeRing
  letI : LieRing (U n) := LieRing.ofAssociativeRing
  unfold e
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie,
    LieRing.of_associative_ring_bracket, E_comm, map_sub]
  congr 1 <;> split_ifs <;> first | rfl | exact map_zero _

theorem e_mul_sub_mul_capelliMatrix_pow : ∀ {n : ℕ} (a b : Fin n) (k : ℕ) (c d : Fin n),
  e (a, b) * (capelliMatrix ^ k) c d -
      (capelliMatrix ^ k) c d * e (a, b) =
    (if b = c then (capelliMatrix ^ k) a d else 0) -
      if d = a then (capelliMatrix ^ k) c b else 0 := by
  intro n a b k c d
  exact commutator_matrix_pow capelliMatrix _ a b
    (fun c d => e_comm a b c d) k c d

end UpperTheory.Reformulated.B.Qk36
