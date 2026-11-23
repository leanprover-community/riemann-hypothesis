module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NatCardEqPowLength
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveChartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

def chartUnit (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * a k)

def chartIndexLog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : ℝ :=
  Real.log (genIndex (chartLat y a τ) (curveMul y (chartUnit y c a τ)))

def chartRadius (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (t : (Σ k, ι k) → ℂ) : ℝ :=
  A.h t / ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k

end Objects

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


open Classical in
theorem sum_single_chart_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

theorem isMultiHomog_curveChartMono (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (curveChartMono c d) d := by
  classical
  have h : curveChartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [curveChartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_chart_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial (ι := ι)
    (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm


omit [∀ k, Fintype (ι k)] in
theorem aeval_curveChartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (curveChartMono c d) = chartUnit y c (fun k => (d k : ℤ)) 1 := by
  simp [curveChartMono, chartUnit, map_prod]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ne_zero_of_X_notMem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  show X p ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]


omit [∀ k, Fintype (ι k)] in
theorem curveChartMono_notMem {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    curveChartMono c d ∉ mCoordIdeal y := by
  intro h
  have h' : mConeMap y (curveChartMono c d) = 0 := h
  rw [curveChartMono, map_prod] at h'
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h'
  rw [map_pow, mConeMap, aeval_X] at hk
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) (pow_eq_zero_iff'.mp hk).1

theorem exists_chart {y : (Σ k, ι k) → Ω} {n : ℕ} (hP : IsArithVar (mCoordIdeal y) n) :
    ∃ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hP.2.1.2.2
  exact ⟨c, hc, fun k => ne_zero_of_X_notMem (hc k)⟩

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.Targets
