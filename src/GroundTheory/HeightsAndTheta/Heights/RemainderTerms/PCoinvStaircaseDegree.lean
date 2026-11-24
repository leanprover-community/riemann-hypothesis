module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

theorem Coinv.sum_staircase_exponents (f n : ℕ) :
    ∑ v : Fin f × Fin n, (v.2 : ℕ) = coinvTop f n := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rfl

theorem CoinvStaircaseDegree.proof : CoinvStaircaseDegree.Statement := by
  intro f n e he
  have hle : ∀ v ∈ (Finset.univ : Finset (Fin f × Fin n)), e v ≤ (v.2 : ℕ) := fun v _ => he v
  rw [Finsupp.degree_eq_sum, ← Coinv.sum_staircase_exponents f n]
  refine ⟨Finset.sum_le_sum hle, fun hEq => ?_⟩
  have hall := (Finset.sum_eq_sum_iff_of_le hle).1 hEq
  ext v
  simp [staircase, hall v (Finset.mem_univ v)]

end GroundTheory.Heights₂.Heights.RestTerms
