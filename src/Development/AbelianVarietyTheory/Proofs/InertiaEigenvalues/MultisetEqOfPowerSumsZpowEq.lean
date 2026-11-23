module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem multiset_eq_of_powerSums_zpow_eq : ∀ (k : Type) [Field k] [CharZero k] (z : k), z ≠ 0 →
    (∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1) → ∀ J J' : Multiset ℤ,
    (∀ n : ℕ, (J.map fun h => (z ^ h) ^ n).sum = (J'.map fun h => (z ^ h) ^ n).sum) → J = J' := by
  intro k _ _ z hz hroot J J' hsum

  have hlt : ∀ a b : ℤ, a < b → z ^ a ≠ z ^ b := by
    intro a b hab heq
    have h1 : z ^ (b - a) = 1 := by
      rw [zpow_sub₀ hz, heq, div_self (zpow_ne_zero _ hz)]
    have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    rw [← h2, zpow_natCast] at h1
    exact hroot _ (by omega) h1
  have hinj : Function.Injective (fun h : ℤ => z ^ h) := by
    intro a b hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt a b h hab
    · exact hlt b a h hab.symm

  let χ : ℤ → (Multiplicative ℕ →* k) := fun h => powersHom k (z ^ h)
  have hχ : Function.Injective χ := (powersHom k).injective.comp hinj
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) k).comp χ hχ
  rw [linearIndependent_iff'] at hli

  have key : ∀ (M : Multiset ℤ) (s : Finset ℤ), M.toFinset ⊆ s → ∀ f : ℤ → k,
      (M.map f).sum = ∑ h ∈ s, (M.count h : k) * f h := by
    intro M s hs f
    rw [Finset.sum_multiset_map_count]
    simp_rw [nsmul_eq_mul]
    apply Finset.sum_subset hs
    intro x _ hx
    rw [Multiset.mem_toFinset] at hx
    simp [Multiset.count_eq_zero.mpr hx]
  set s : Finset ℤ := (J + J').toFinset with hs
  have hJ : J.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inl hx)
  have hJ' : J'.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inr hx)
  have hzero := hli s (fun h => (J.count h : k) - (J'.count h : k)) (by
    funext m
    have e := hsum (Multiplicative.toAdd m)
    rw [key J s hJ, key J' s hJ'] at e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [χ, powersHom_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact e)
  refine Multiset.ext.mpr (fun a => ?_)
  by_cases ha : a ∈ s
  · have := hzero a ha
    rw [sub_eq_zero] at this
    exact_mod_cast this
  · rw [hs, Multiset.mem_toFinset, Multiset.mem_add, not_or] at ha
    rw [Multiset.count_eq_zero.mpr ha.1, Multiset.count_eq_zero.mpr ha.2]

end GlobalTheory
