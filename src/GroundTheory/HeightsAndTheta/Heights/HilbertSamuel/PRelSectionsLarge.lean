module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSectionsLarge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelChartPoly
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelOneStep
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelSectionsLarge

theorem chartMonomial_mem_relSecM {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (b : K → ℕ) :
    ∏ k, y ⟨k, c0 k⟩ ^ b k ∈ relSecM R y b := by
  classical
  have h := monomial_mem_relSecM R y (b := b) (fun p => if p.2 = c0 p.1 then b p.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c0 k) (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem descend {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (n₁ : ℕ)
    (hstep : ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b) :
    ∀ (m : ℕ) (e : K → ℕ), ∑ k, e k = m → ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ s ∈ relChartLat R y (fun k => (b k : ℤ)) 1,
        s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relSecM R y (b + e) → s ∈ relSecM R y b := by
  intro m
  induction m with
  | zero =>
    intro e he b _ s _ hs
    have h0 : e = 0 := funext fun k => by
      simpa using (Finset.sum_eq_zero_iff.mp he) k (Finset.mem_univ k)
    subst h0
    simpa using hs
  | succ m ih =>
    intro e he b hb s hsL hs
    obtain ⟨k0, hk0⟩ : ∃ k0, 0 < e k0 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ k, e k = 0 := Finset.sum_eq_zero fun k _ => Nat.le_zero.mp (hcon k)
      omega
    set e' : K → ℕ := e - Pi.single k0 1 with he'
    have hee : e = e' + Pi.single k0 1 := by
      funext k
      simp only [he', Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = k0
      · subst hk; simp; omega
      · simp [hk]
    have hsum : ∑ k, e' k = m := by
      have : ∑ k, e k = ∑ k, e' k + 1 := by
        rw [hee]; simp only [Pi.add_apply]; rw [Finset.sum_add_distrib]; simp
      omega
    refine ih e' hsum b hb s hsL ?_
    have htL : s * ∏ k, y ⟨k, c0 k⟩ ^ e' k ∈ relChartLat R y (fun k => ((b + e') k : ℤ)) 1 :=
      mul_prod_mem_relChartLat R y (a := fun k => (b k : ℤ)) (a' := fun k => ((b + e') k : ℤ)) (n := 1) e' c0
        (fun k => by simp only [Pi.add_apply]; push_cast; ring) hsL
    have hb' : ∀ k, n₁ ≤ (b + e') k := fun k => le_trans (hb k) (Nat.le_add_right _ _)
    refine hstep (b + e') hb' k0 _ htL ?_
    have hprod : y ⟨k0, c0 k0⟩ * (s * ∏ k, y ⟨k, c0 k⟩ ^ e' k) = s * ∏ k, y ⟨k, c0 k⟩ ^ e k := by
      rw [hee]
      have h1 : ∏ k, y ⟨k, c0 k⟩ ^ (Pi.single k0 1 : K → ℕ) k = y ⟨k0, c0 k0⟩ := by
        rw [Fintype.prod_eq_single k0 (fun k hk => by simp [hk])]
        simp
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, h1]
      ring
    rw [hprod, add_assoc, ← hee]
    exact hs

theorem proof (hC : RelChartPoly.Statement) (hO : RelOneStep.Statement) : RelSectionsLarge.Statement := by
  classical
  intro K _ ι _ Ω _ R hR y hy
  choose c0 hc0 using hy
  obtain ⟨n₁, hn₁⟩ := hO K ι Ω R hR y c0 hc0
  refine ⟨n₁, fun b hb s hs => ?_⟩
  obtain ⟨N, hN⟩ := hC K ι Ω R y c0 _ (hs c0 hc0)
  have hform := mul_mem_relSecM R y hN (chartMonomial_mem_relSecM R y c0 b)
  refine descend R y c0 n₁ hn₁ (∑ _k : K, N) (fun _ => N) rfl b hb s hs ?_
  rw [add_comm]
  convert hform using 1
  have hcancel : (∏ k, y ⟨k, c0 k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c0 k⟩ ^ b k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [Nat.cast_one, one_mul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc0 k))]
  rw [← Finset.prod_pow]
  linear_combination (-(s * ∏ k, y ⟨k, c0 k⟩ ^ N)) * hcancel

end RelSectionsLarge

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
