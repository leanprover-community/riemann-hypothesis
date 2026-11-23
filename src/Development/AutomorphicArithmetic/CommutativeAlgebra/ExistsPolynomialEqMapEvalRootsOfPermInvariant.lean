module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEvalRootsSymmetricEqAlgebraMap
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

noncomputable section
open Polynomial

theorem UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (Φ : (MvPolynomial (Fin N) A)[X]), (∀ σ : Equiv.Perm (Fin N), Φ.map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = Φ) →
      ∃ p : A[X], p.natDegree ≤ Φ.natDegree ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → p.map (algebraMap A S) = Φ.map (MvPolynomial.aeval x : MvPolynomial (Fin N) A →ₐ[A] S).toRingHom := by
  intro A _ N g Φ hΦ
  have hsym : ∀ n, (Φ.coeff n).IsSymmetric := by
    intro n σ
    have := congrArg (fun q => q.coeff n) (hΦ σ)
    simpa [Polynomial.coeff_map] using this
  choose a ha using fun n => UpperTheory.exists_eval_roots_symmetric_eq_algebraMap A N g (Φ.coeff n) (hsym n)
  refine ⟨∑ n ∈ Finset.range (Φ.natDegree + 1), monomial n (a n), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun n hn => ?_)
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
  · intro S _ _ x hx
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hn
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ha n S x hx]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

end
