module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Expand
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem coeff_chi_smul {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (a : A)
    (y : MonoidAlgebra A G) (i : ℕ) (hi : i ≤ n) :
    (D.chi (a • y)).coeff (n - i) = (-a) ^ i * D.lam i y := by
  have hsum : D.chi (a • y) = ∑ j ∈ Finset.range (n + 1), C (D.lam j y * (-a) ^ j) * X ^ (n - j) := by
    have h := AlgebraTools.Det.expand D y A[X] X (C (-a))
    rw [Polynomial.algebraMap_eq] at h
    unfold GDet.chi
    have harg : MonoidAlgebra.single 1 X - (MonoidAlgebra.mapRingHom G C) (a • y) =
        MonoidAlgebra.single 1 X + C (-a) • (MonoidAlgebra.mapRingHom G C) y := by
      rw [map_neg, neg_smul, ← sub_eq_add_neg]
      congr 1
      ext g
      simp [MonoidAlgebra.mapRingHom]
    rw [harg, h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow]
    ring
  rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    ring
  · intro j hj hji
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    apply hji
    have := Finset.mem_range.mp hj
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem UpperTheory.V.Ws.H5.lamSmul :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (a : A) (y : MonoidAlgebra A G) (i : ℕ), D.lam i (a • y) = a ^ min i n * D.lam i y := by
  intro n A G _ _ D a y i
  have hl : ∀ (z : MonoidAlgebra A G) (j : ℕ), D.lam j z = (-1) ^ j * (D.chi z).coeff (n - j) := by
    intro z j
    unfold GDet.lam
    rfl
  rcases le_or_gt i n with hi | hi
  · rw [hl, coeff_chi_smul D a y i hi, min_eq_left hi, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  · have hn : n - i = n - n := by omega
    have h1 := coeff_chi_smul D 1 y n le_rfl
    rw [one_smul] at h1
    rw [hl (a • y), hl y, hn, coeff_chi_smul D a y n le_rfl, h1, min_eq_right hi.le, neg_pow a n]
    ring
