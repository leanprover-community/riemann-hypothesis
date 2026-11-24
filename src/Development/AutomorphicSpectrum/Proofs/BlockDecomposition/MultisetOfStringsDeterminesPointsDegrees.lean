module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.DiscSpec

namespace GlobalTheory.CompanionTheory.Rigid


open Classical in
theorem card_spehExp_eq (d m : ℕ) (hm : 1 ≤ m) :
    ((Finset.univ : Finset (Fin d)).filter (fun k => ((m : ℝ) - 1) / 2 = spehExp d k)).card =
      if m ≤ d ∧ Even (d - m) then 1 else 0 := by
  split_ifs with h
  · obtain ⟨hle, t, ht⟩ := h
    have hd : d = m + 2 * t := by omega
    have hdR : (d : ℝ) = m + 2 * t := by exact_mod_cast hd
    have htd : t < d := by omega
    rw [Finset.card_eq_one]
    refine ⟨⟨t, htd⟩, ?_⟩
    ext k
    rw [Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and, spehExp]
    constructor
    · intro hk
      apply Fin.ext
      have : ((k : ℕ) : ℝ) = t := by linarith
      exact_mod_cast this
    · rintro rfl
      show ((m : ℝ) - 1) / 2 = ((d : ℝ) - 1) / 2 - (t : ℝ)
      linarith
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ hk
    apply h
    simp only [spehExp] at hk
    have h1 : (d : ℝ) = m + 2 * ((k : ℕ) : ℝ) := by linarith
    have h2 : d = m + 2 * (k : ℕ) := by exact_mod_cast h1
    exact ⟨by omega, (k : ℕ), by omega⟩


open Classical in
theorem count_strings {X ι : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) (x : X) (m : ℕ) (hm : 1 ≤ m) :
    (GlobalTheory.Rigid.strings p d).count (x, ((m : ℝ) - 1) / 2) =
      (Finset.univ.filter fun i => p i = x ∧ m ≤ d i ∧ Even (d i - m)).card := by
  unfold GlobalTheory.Rigid.strings
  rw [Multiset.count_sum', Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.count_map]
  by_cases hx : p i = x
  · have h := card_spehExp_eq (d i) m hm
    simp only [hx, true_and, Prod.mk.injEq]
    rw [← h]
    rfl
  · have hx' : ¬ x = p i := fun e => hx e.symm
    simp [hx, hx']


open Classical in
theorem card_fibre_add {ι : Type} {X : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) (x : X) (m : ℕ) :
    (Finset.univ.filter fun i => p i = x ∧ d i = m).card +
        (Finset.univ.filter fun i => p i = x ∧ m + 2 ≤ d i ∧ Even (d i - (m + 2))).card =
      (Finset.univ.filter fun i => p i = x ∧ m ≤ d i ∧ Even (d i - m)).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : p i = x
  · simp only [hx, true_and, Nat.even_iff]
    split_ifs <;> omega
  · simp [hx]


open Classical in
theorem card_fibre_eq {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X)
    (d' : κ → ℕ) (hd : ∀ i, 1 ≤ d i) (hd' : ∀ j, 1 ≤ d' j)
    (h : GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d') (x : X) (m : ℕ) :
    (Finset.univ.filter fun i => p i = x ∧ d i = m).card =
      (Finset.univ.filter fun j => p' j = x ∧ d' j = m).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : (Finset.univ.filter fun i => p i = x ∧ d i = 0) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i _ hi => by have := hd i; omega
    have h2 : (Finset.univ.filter fun j => p' j = x ∧ d' j = 0) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ hj => by have := hd' j; omega
    rw [h1, h2, Finset.card_empty, Finset.card_empty]
  · have a1 := card_fibre_add p d x m
    have a2 := card_fibre_add p' d' x m
    have c1 := count_strings p d x m hm
    have c2 := count_strings p' d' x m hm
    have e1 := count_strings p d x (m + 2) (by omega)
    have e2 := count_strings p' d' x (m + 2) (by omega)
    rw [h] at c1 e1
    omega

theorem strings_rigid {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X)
    (d' : κ → ℕ) (hd : ∀ i, 1 ≤ d i) (hd' : ∀ j, 1 ≤ d' j)
    (h : GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d') :
    ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  classical
  have hc : ∀ c : X × ℕ, Fintype.card {i // (p i, d i) = c} = Fintype.card {j // (p' j, d' j) = c} := by
    rintro ⟨x, m⟩
    have := card_fibre_eq p d p' d' hd hd' h x m
    simp only [Fintype.card_subtype, Prod.mk.injEq]
    convert this
  let e : ∀ c : X × ℕ, {i // (p i, d i) = c} ≃ {j // (p' j, d' j) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_⟩
  have := Equiv.ofFiberEquiv_map e i
  exact ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩

end GlobalTheory.CompanionTheory.Rigid
