module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.AdicSum


open Classical in
theorem sum_sub_sum_mem {R : Type} [CommRing R] (J : Ideal R) {X : Type} (v : X → R)
    (S T : Finset X) (hS : ∀ α ∉ S, v α ∈ J) (hT : ∀ α ∉ T, v α ∈ J) :
    ∑ α ∈ S, v α - ∑ α ∈ T, v α ∈ J := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := S)]
  exact J.sub_mem (J.sum_mem fun α hα => hT α (Finset.mem_sdiff.1 hα).2)
    (J.sum_mem fun α hα => hS α (Finset.mem_sdiff.1 hα).2)

theorem exists_adic_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) →
    ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) →
      s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  intro R _ _ _ hR X v hfin
  have hC : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  have hfin' : ∀ n : ℕ, {α | v α ∉ maximalIdeal R ^ n}.Finite := fun n =>
    (hfin n).subset fun α (hα : v α ∉ maximalIdeal R ^ n) (h : v α ∈ maximalIdeal R ^ (n + 1)) =>
      hα (Ideal.pow_le_pow_right (Nat.le_succ n) h)
  let F : ℕ → Finset X := fun n => (hfin' n).toFinset
  have hF : ∀ n, ∀ α ∉ F n, v α ∈ maximalIdeal R ^ n := by
    intro n α hα
    by_contra h
    exact hα ((hfin' n).mem_toFinset.2 h)
  let f : ℕ → R := fun n => ∑ α ∈ F n, v α
  have hsm : ∀ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R R) = maximalIdeal R ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := (hC.toIsPrecomplete).prec (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    exact sum_sub_sum_mem (maximalIdeal R ^ m) v (F m) (F n) (hF m)
      fun α hα => Ideal.pow_le_pow_right hmn (hF n α hα))
  refine ⟨L, fun e S hS => ?_⟩
  have h1 : f (e + 1) - L ∈ maximalIdeal R ^ (e + 1) := by
    have := hL (e + 1)
    rwa [SModEq.sub_mem, hsm] at this
  have h2 := sum_sub_sum_mem (maximalIdeal R ^ (e + 1)) v (F (e + 1)) S (hF (e + 1)) hS
  have : L - ∑ α ∈ S, v α = (f (e + 1) - ∑ α ∈ S, v α) - (f (e + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

end GlobalTheory.Mum.AdicSum
