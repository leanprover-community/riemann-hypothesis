module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConst
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.RhoNSubNab
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_ncProd (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ ab : PCoord ε, f ab.1.2 ab.1.1 := by
  have e1 : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ x ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ¬ ε x.1 = ε x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    simp_rw [Finset.prod_filter]
  rw [e1, ← Finset.prod_subtype (univ.filter (fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2))
    (fun x => by simp) (fun x : Fin n × Fin n => f x.2 x.1)]
  apply Finset.prod_nbij' Prod.swap Prod.swap
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; rfl

theorem fdc_vand_split (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    Vand μ = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (μ a - μ b)) *
      ∏ ab : PCoord ε, (μ ab.1.2 - μ ab.1.1) := by
  rw [← fdc_ncProd ε (fun a b => μ a - μ b), ← Finset.prod_mul_distrib]
  unfold Vand
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter (fun b : Fin n => a < b)) (fun b => ε a = ε b),
    Finset.filter_filter, Finset.filter_filter]

theorem pi_weight_at_zero_eq (ε : Fin n → Bool) :
    PiW ε 0 = Real.pi ^ (pOf ε * qOf ε) / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  unfold PiW wab
  simp only [Pi.zero_apply, sub_zero, zero_add]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, card_PCoord]

theorem fdc_ncpos (ε : Fin n → Bool) :
    0 < ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  refine Finset.prod_pos fun ab _ => sub_pos.2 ?_
  exact_mod_cast ab.2.1

theorem fdc_tend1 (α k m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (α + (t : ℝ) * m + k) / (α + (t : ℝ) * m)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h2 : Tendsto (fun t : ℕ => k / (α + (t : ℝ) * m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0] with t ht
  field_simp

theorem fdc_tend2 (α m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (t : ℝ) / (α + (t : ℝ) * m)) atTop (𝓝 (1 / m)) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h3 : Tendsto (fun t : ℕ => α / (t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h4 := (tendsto_const_nhds (x := (1 : ℝ))).div (h3.add_const m) (by rw [zero_add]; exact hm.ne')
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0, eventually_gt_atTop 0] with t ht ht0
  have : (0 : ℝ) < t := by exact_mod_cast ht0
  show (1:ℝ) / (α / (t:ℝ) + m) = (t:ℝ) / (α + (t:ℝ) * m)
  rw [div_add' _ _ _ this.ne', one_div_div, mul_comm m]

theorem formal_degree_constant_eq {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (d : ℕ → ℝ)
    (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (h1 : ∀ t, d t / Vand (lamT lam t) = d 0 / Vand lam) (hd0 : 0 < d 0)
    (hup : Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop ≤ ENNReal.ofReal (cPQ ε * PiW ε 0))
    (hlow : ENNReal.ofReal (cPQ ε * PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop) :
    d 0 = dimVlam lam := by
  apply ReciprocityTheory.ChartRestriction.DS.formal_degree_constant_eq <;> assumption

end ReciprocityTheory.ChartRestriction.DS.G2
