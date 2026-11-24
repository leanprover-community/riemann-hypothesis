module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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

theorem UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous :
    ∀ {σ R : Type} [Fintype σ]
    [inst : CommRing R] [inst_1 : Algebra ℚ R] {P : MvPolynomial σ ℚ} {d : ℕ},
    P.IsHomogeneous d →
      ∀ (y : R) (g : σ → R),
        (MvPolynomial.aeval fun (k : σ) ↦ y * g k : MvPolynomial σ ℚ → R) P =
          y ^ d * (MvPolynomial.aeval g : MvPolynomial σ ℚ → R) P := by
  intro σ R _ _ _ P d hP y g
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : s.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 hs) (hP.coeff_eq_zero h)
  have h2 : ∑ i, s i = d := by
    rw [← h1, Finsupp.degree_eq_sum]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h2]
  ring
