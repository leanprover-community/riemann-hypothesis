module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NsqMulVecLeOpN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

lemma dot_self {n : ℕ} (y : Fin n → ℂ) : star y ⬝ᵥ y = ((nsq y : ℝ) : ℂ) := by
  simp only [nsq, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' (y i)

lemma quad_AtA {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((Aᵀ * A.map (starRingEnd ℂ)) *ᵥ y) = ((nsq (A.map (starRingEnd ℂ) *ᵥ y) : ℝ) : ℂ) := by
  have h : A *ᵥ star y = star (A.map (starRingEnd ℂ) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h, dot_self]

lemma posDef_of_bound {n q k : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (B : Matrix (Fin k) (Fin n) ℂ) {s : ℝ}
    (hs : s < 1) (hA : ∀ y, nsq (A.map (starRingEnd ℂ) *ᵥ y) ≤ s ^ 2 * nsq y) (hs0 : 0 ≤ s) :
    (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).PosDef := by
  have hH : (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).IsHermitian := by
    have h1 : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ), (Cᵀ * C.map (starRingEnd ℂ)).IsHermitian := by
      intro m C
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, mul_comm]
    exact ((Matrix.isHermitian_one.sub (h1 A)).add (h1 B))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dot_self, quad_AtA, quad_AtA]
  have hpos : 0 < nsq x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    change x i ≠ 0 at hi
    have : 0 < ‖x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i))
  have hB := nsq_nonneg (B.map (starRingEnd ℂ) *ᵥ x)
  have hA' := hA x
  have hs2 : s ^ 2 < 1 := by nlinarith
  have key : 0 < nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) := by
    nlinarith
  have : ((nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) =
      ((nsq x : ℝ) : ℂ) - ((nsq (A.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) +
        ((nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) := by push_cast; ring
  rw [← this]
  exact_mod_cast key

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
