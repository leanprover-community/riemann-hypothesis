module

public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

set_option linter.unusedSimpArgs false

section NonDom

variable {R : Type*} [CommRing R] {r n : ℕ}

def ndEul (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => (colW r n v s) • X v

def ndE (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = j then X (v.1, l) else 0

def ndF (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = l then X (v.1, j) else 0

lemma nd_weight_apply (s : Fin n) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (fun v => colW r n v s) m = Finsupp.weight (colW r n) m s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

lemma ndEul_coeff (s : Fin n) (g : MvPolynomial (Fin r × Fin n) R) (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (ndEul R r n s g) m =
      (Finsupp.weight (fun v => colW r n v s) m : R) * AddMonoidAlgebra.coeff g m := by
  classical
  induction g using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [derivation_C, AddMonoidAlgebra.coeff_zero, coeff_C]
    split_ifs with h
    · subst h; simp
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]
  | mul_X p v hp =>
    have hX : ndEul R r n s (X v) = colW r n v s • X v := mkDerivation_X _ _ _
    rw [Derivation.leibniz, hX, MvPolynomial.coeff_add, smul_eq_mul, smul_eq_mul,
      mul_smul_comm, MvPolynomial.coeff_smul, coeff_mul_X', coeff_X_mul']
    split_ifs with h
    · rw [hp]
      have hle : Finsupp.single v 1 ≤ m := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
      have hm : m = (m - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have hw : Finsupp.weight (fun v => colW r n v s) m =
          Finsupp.weight (fun v => colW r n v s) (m - Finsupp.single v 1) + colW r n v s := by
        conv_lhs => rw [hm]
        rw [map_add (f := _), Finsupp.weight_single, one_smul]
      rw [hw, nsmul_eq_mul]; push_cast; ring
    · simp

lemma ndEul_homog {g : MvPolynomial (Fin r × Fin n) R} {μ : Fin n → ℕ}
    (hg : IsWeightedHomogeneous (colW r n) g μ) (s : Fin n) :
    ndEul R r n s g = (μ s : R) • g := by
  ext m
  rw [ndEul_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases h : AddMonoidAlgebra.coeff g m = 0
  · simp [h]
  · rw [nd_weight_apply, hg h]

lemma ndEul_neg_eq_zero [IsDomain R] [CharZero R] {g : MvPolynomial (Fin r × Fin n) R}
    (s : Fin n) (h : ndEul R r n s g = -g) : g = 0 := by
  ext m
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [ndEul_coeff, MvPolynomial.coeff_neg] at h1
  have h2 : ((Finsupp.weight (fun v => colW r n v s) m : R) + 1) * AddMonoidAlgebra.coeff g m = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.cast_add_one_ne_zero _)
  · simpa using h3

lemma nd_comm_EF {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndE R r n l j (ndF R r n l j g) =
      ndF R r n l j (ndE R r n l j g) + (ndEul R r n l g - ndEul R r n j g) := by
  have key : ⁅ndE R r n l j, ndF R r n l j⁆ = ndEul R r n l - ndEul R r n j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.sub_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at this
  rw [← this]; abel

lemma nd_comm_EulF_l {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n l (ndF R r n l j g) = ndF R r n l j (ndEul R r n l g) - ndF R r n l j g := by
  have key : ⁅ndEul R r n l, ndF R r n l j⁆ = -ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.neg_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.neg_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

lemma nd_comm_EulF_j {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n j (ndF R r n l j g) = ndF R r n l j (ndEul R r n j g) + ndF R r n l j g := by
  have key : ⁅ndEul R r n j, ndF R r n l j⁆ = ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

end NonDom

end Formalism.GradedWeylDivisibility
