module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeAevalLeOfDegLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst

@[expose] public section

set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.GenSubDeg

theorem genSub_coeff_le : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := by
  intro O _ N D f hf m hm v
  have hg : ∀ i : Fin N × Fin N, (∑ b : Fin N, (X (i.1, b) * C (X (b, i.2)) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O))).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_finsetSum_le fun b _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, add_zero]
    rw [X]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  have hdeg := GlobalTheory.SZShift.totalDegree_aeval_le_of_deg_le_one _ hg f
  have h1 : m.degree ≤ (GlobalTheory.HighWt.genSub O N f).totalDegree := by
    rw [Finsupp.degree]
    exact le_totalDegree (mem_support_iff.mpr hm)
  have h2 : m v ≤ m.degree := by
    classical
    rw [Finsupp.degree]
    by_cases hv : v ∈ m.support
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    · simp [Finsupp.notMem_support_iff.mp hv]
  exact h2.trans (h1.trans ((hdeg.trans hf)))

end GlobalTheory.GenSubDeg
