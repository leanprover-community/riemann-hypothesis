module

public import Mathlib.FieldTheory.Separable
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder :
    ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ), M.charpoly = ∏ i, (X - C (a i : K)) →
      (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) → ∀ d : ℕ, 0 < d → (M ^ d).charpoly.Separable := by
  intro K _ n M a hM ha d hd
  have hinj : Function.Injective (fun i => (a i : K) ^ d) := by
    intro i j hij
    by_contra hne
    apply ha i j hne
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨d, hd, ?_⟩
    rw [div_pow, div_eq_one]
    apply Units.ext
    simpa using hij
  have hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d) := by
    intro i
    rw [← Matrix.mem_spectrum_iff_isRoot_charpoly]
    apply spectrum.pow_mem_pow
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hinj hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.2 (hroot i)
  have hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have heq : (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
  rw [heq]
  exact Polynomial.separable_prod_X_sub_C_iff.2 hinj
