module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem prime_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) : (Ideal.span (x '' (s : Set κ))).IsPrime := by
  have h := (regular_quotient_cotInd R s (x ∘ ((↑) : s → κ)) (hx.comp _ Subtype.val_injective)).2.2
  have e : Set.range (x ∘ ((↑) : s → κ)) = x '' (s : Set κ) := by
    rw [Set.range_comp]
    congr 1
    ext a
    simp
  rwa [e] at h

private theorem not_mem_sub (R : Type) [CommRing R] [IsLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) (a : κ) (ha : a ∉ s) :
    x a ∉ Ideal.span (x '' (s : Set κ)) := by
  classical
  intro hmem
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp hmem
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul R (x i))] at hlx
  simp only [smul_eq_mul] at hlx
  let b : κ → R := Pi.single a 1
  have h0 : ∑ k, (b k - l k) * x k ∈ maximalIdeal R ^ 2 := by
    have hz : ∑ k, (b k - l k) * x k = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, hlx]
      simp [b, Pi.single_apply]
    rw [hz]
    exact zero_mem _
  have h1 := hx.indep _ h0 a
  rw [(Finsupp.mem_supported' R l).mp hl a ha, sub_zero] at h1
  simp only [b, Pi.single_eq_same] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem height_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) :
    (s.card : ℕ∞) ≤ (Ideal.span (x '' (s : Set κ))).height := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    haveI := prime_sub R κ x hx s
    haveI := prime_sub R κ x hx (insert a s)
    have hlt : Ideal.span (x '' (s : Set κ)) < Ideal.span (x '' ((insert a s : Finset κ) : Set κ)) := by
      refine lt_of_le_of_ne (Ideal.span_mono (Set.image_mono (by simp))) fun e => ?_
      apply not_mem_sub R κ x hx s a ha
      rw [e]
      exact Ideal.subset_span ⟨a, by simp, rfl⟩
    have h1 := Ideal.height_strict_mono_of_isPrime hlt
    rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
    exact Order.add_one_le_of_lt (ih.trans_lt h1)

theorem UpperTheory.V.AlgebraTools.regular_localization_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∀ (p : Ideal R) [p.IsPrime], p = Ideal.span (Set.range x) →
      p.height = (Fintype.card κ : ℕ) ∧ IsRegularLocalRing (Localization.AtPrime p) := by
  classical
  intro R _ _ κ _ x hx p _ hp
  have hge : ((Fintype.card κ : ℕ) : ℕ∞) ≤ p.height := by
    have h1 := height_sub R κ x hx Finset.univ
    rwa [Finset.card_univ, Finset.coe_univ, Set.image_univ, ← hp] at h1
  have hle : p.height ≤ ((Fintype.card κ : ℕ) : ℕ∞) := by
    have e : Ideal.span ((Finset.univ.image x : Finset R) : Set R) = p := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hp]
    have hmin : p ∈ (Ideal.span ((Finset.univ.image x : Finset R) : Set R)).minimalPrimes := by
      rw [e, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton p
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_image_le
  have heq : p.height = ((Fintype.card κ : ℕ) : ℕ∞) := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
    IsLocalization.AtPrime.under_maximalIdeal _ p, heq, ← Localization.AtPrime.map_eq_maximalIdeal]
  have hmap : Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      Ideal.map (algebraMap R (Localization.AtPrime p)) (Ideal.span (Set.range x)) := congrArg _ hp
  rw [hmap, Ideal.map_span, ← Set.range_comp]
  have h3 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Localization.AtPrime p)
    (Set.finite_range (algebraMap R (Localization.AtPrime p) ∘ x))
  have h4 : (Set.range (algebraMap R (Localization.AtPrime p) ∘ x)).ncard ≤ Fintype.card κ := by
    rw [← Set.image_univ, ← Finset.coe_univ]
    exact (Set.ncard_coe_finset _ ▸ Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
  exact_mod_cast h3.trans h4
