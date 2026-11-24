module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped NNReal
open Ideal Finset GlobalTheory.Per.AinfComplete

namespace GlobalTheory.WittTeichComplete

open scoped NNReal in
open Ideal Finset in
private lemma tails_of_isAdicComplete_span {A : Type*} [CommRing A] (y : A)
    [IsAdicComplete (Ideal.span {y}) A] : _root_.GlobalTheory.Per.AinfComplete.Tails y := by
  have hsum := _root_.GlobalTheory.Per.AinfComplete.summ_of_precomplete y
  unfold _root_.GlobalTheory.Per.AinfComplete.Summ at hsum
  unfold _root_.GlobalTheory.Per.AinfComplete.Tails
  intro b
  choose L hL using fun n => hsum (fun k => b (n + k))
  refine ⟨L, fun n => ?_⟩
  have key : ∀ m, y ^ m ∣ L n - y * L (n + 1) - b n := by
    intro m
    have h₁ := Ideal.mem_span_singleton.1 (hL n (m + 1))
    have h₂ := Ideal.mem_span_singleton.1 (hL (n + 1) m)
    have hs : ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i) =
        b n + y * ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [pow_zero, one_mul, add_zero]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, show n + (i + 1) = n + 1 + i by omega]
      ring
    have hd : L n - y * L (n + 1) - b n =
        (L n - ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i)) -
          y * (L (n + 1) - ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i)) := by
      rw [hs]; ring
    rw [hd]
    exact dvd_sub ((pow_dvd_pow y (Nat.le_succ m)).trans h₁) (dvd_mul_of_dvd_right h₂ y)
  have h0 := _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus y _ fun m => Ideal.mem_span_singleton.2 (key m)
  exact (sub_eq_zero.1 h0).symm


open scoped NNReal in
open Ideal Finset in
theorem _root_.GlobalTheory.WittTeichComplete.main : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l]
    [PerfectRing O l] (x : O), x ≠ 0 → IsAdicComplete (Ideal.span {x}) O →
    IsAdicComplete (Ideal.span {WittVector.teichmuller l x}) (WittVector l O) ∧
      IsAdicComplete (Ideal.span {((l : ℕ) : WittVector l O)} ⊔
        Ideal.span {WittVector.teichmuller l x}) (WittVector l O) := by
  intro l _ O _ _ _ _ x _ hc
  haveI := hc
  have hcc : WittVector.constantCoeff (WittVector.teichmuller l x) = x := by
    simp [WittVector.constantCoeff]
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.Per.AinfComplete.witt_complete (WittVector.teichmuller l x)
    (hcc ▸ tails_of_isAdicComplete_span x) (fun r hr => _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus x r
      fun n => Ideal.mem_span_singleton.2 (hcc ▸ hr n))
  refine ⟨h₂, ?_⟩
  rwa [Ideal.span_insert] at h₁

end GlobalTheory.WittTeichComplete
