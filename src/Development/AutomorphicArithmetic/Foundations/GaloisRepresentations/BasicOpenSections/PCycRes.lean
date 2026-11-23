module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma finsum_fib {A P : Type*} [Finite A] (f : A → P) (S : Set P) (g : P → ℤ)
    (hg : ∀ z ∈ S, g z = (Nat.card {a // f a = z} : ℤ)) :
    ∑ᶠ z ∈ S, g z = (Nat.card {a // f a ∈ S} : ℤ) := by
  classical
  haveI := Fintype.ofFinite A
  have h1 : ∑ᶠ z ∈ S, g z = ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) :=
    finsum_mem_congr rfl hg
  set s : Finset A := Finset.univ.filter fun a => f a ∈ S with hs
  have h2 : ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) =
      ∑ z ∈ s.image f, (Nat.card {a // f a = z} : ℤ) := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext z
    simp only [Set.mem_inter_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe, hs,
      Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_support, ne_eq]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨?_, h⟩
      have : Nonempty {a // f a = z} := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        exact h (by simp)
      obtain ⟨⟨a, rfl⟩⟩ := this
      exact ⟨a, hz, rfl⟩
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨ha, h⟩
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hs,
    Finset.card_eq_sum_card_image f s, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext a
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.1 hz
    refine ⟨?_, rfl⟩
    rw [← hbz]
    exact (Finset.mem_filter.1 hb).2
  · exact fun h => h.2

private lemma co_eq (q : ℕ) {n : ℕ} (j : Fin (n + 1)) :
    co q j = (crystallineComparison.wEv q j : ℤ) - (crystallineComparison.wOd q j : ℤ) := by
  unfold co crystallineComparison.wEv crystallineComparison.wOd
  by_cases h : Even (j : ℕ)
  · simp [h, h.neg_one_pow]
  · have h' : Odd (j : ℕ) := Nat.not_even_iff_odd.1 h
    simp [h, h'.neg_one_pow]

theorem UpperTheory.Gal.Mod.cycRes :
    WtVal → CycRes := by
  intro hW p q n Y π T w hOne hPt V _ _ _ _ _ hp y hgen φ hφ y₀
  classical
  have hv := fun j => hW p Y (T j) (w j) (hOne j) V hp y
  haveI : ∀ j, Finite ((T j).Sec y) := fun j => (hv j).1
  letI : ∀ j, Fintype ((T j).Sec y) := fun j => Fintype.ofFinite _
  have hA := hPt V hp y hgen φ hφ (fun j => (T j).Sec y) (fun j => id)
    (fun j => Function.bijective_id)
  have hc := congrArg (Multiset.count y₀) hA
  simp only [crystallineComparison.pts, Multiset.count_sum', Multiset.count_nsmul, id] at hc
  have key : ∀ j : Fin (n + 1),
      ∑ᶠ z ∈ {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀}, w j _ z =
      (Multiset.count y₀ (Finset.univ.val.map fun i : (T j).Sec y =>
        (twist φ Y)^[n - j] (resPt V ≫ i.1 ≫ (T j).r)) : ℤ) := by
    intro j
    rw [finsum_fib (fun i : (T j).Sec y => resPt V ≫ i.1)
      {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀} (w j _)
      (fun z hz => (hv j).2 z hz.1)]
    congr 1
    rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val]
    refine congrArg Multiset.card (Multiset.filter_congr fun i _ => ?_)
    have h1 : (resPt V ≫ i.1) ≫ (T j).p = resPt V ≫ y := by
      rw [Category.assoc, i.2]
    simp only [Set.mem_setOf_eq, h1, true_and, Category.assoc]
    exact eq_comm
  simp only [key, co_eq, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact_mod_cast hc
