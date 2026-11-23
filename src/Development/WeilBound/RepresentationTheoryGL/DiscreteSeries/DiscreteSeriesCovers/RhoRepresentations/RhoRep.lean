module

import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.RhoRepresentations.RhoRep
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgDs.K

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma rr_toMK_one (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl

lemma rr_toMK_mul {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma rr_toMK_inv {ε : Fin n → Bool} (k : KG ε) : (toMK k)⁻¹ = toMK k⁻¹ := by
  show _ = ((((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  rw [Matrix.coe_units_inv]

lemma rr_adC_one (p q : Fin n × Fin n) : adC (1 : Matrix (Fin n) (Fin n) ℂ) p q = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [adC, inv_one, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]

lemma rr_adC_mul (A B : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n × Fin n) :
    adC (A * B) p q = ∑ r : Fin n × Fin n, adC B p r * adC A r q := by
  simp only [adC, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
  ring

lemma rr_prod_ite {l : ℕ} (w x : Fin l → Fin n × Fin n) :
    (∏ i, (if w i = x i then (1 : ℂ) else 0)) = if w = x then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma rr_op_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.op 1 = 1 := by
  simp [KType.op]

lemma rr_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k k' : KG ε) (v : T.V) :
    T.op (k * k') v = T.op k (T.op k' v) := by
  simp [KType.op]

theorem rho_representation_holds : PositivityTheory.RgDs.K.RhoRep := by
  apply CompanionTheory.RgDs.K.rho_representation_holds <;> assumption

end PositivityTheory.RgDs.K
