module

public import Formalism.HermitianLattices.StatementMass
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

open NumberField Module Matrix in
open scoped ENNReal in
private lemma exists_integer_eq_star {K : Type} [Field K] [NumberField K] [StarRing K]
    (a : 𝓞 K) : ∃ b : 𝓞 K, (b : K) = star (a : K) := by
  have hint : IsIntegral ℤ (starRingEnd K (a : K)) :=
    map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)
  rw [starRingEnd_apply] at hint
  exact ⟨⟨star (a : K), (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩


open NumberField Module Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
      ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  intro K _ _ _ h
  unfold _root_.Formalism.HermitianLatticesTheory.IsCMUnram at h
  obtain ⟨-, -, hP⟩ := h
  let S : Set (𝓞 K) := {x | ∃ θ τ : 𝓞 K,
    algebraMap (𝓞 K) K τ = star (algebraMap (𝓞 K) K θ) ∧ x = θ - τ}
  let I : Ideal (𝓞 K) := Ideal.span S
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨θ, τ, hτ, hnot⟩ := hP P hPm
    exact hnot (hle (Ideal.subset_span ⟨θ, τ, hτ, rfl⟩))
  have key : ∀ x ∈ I, ∃ t : 𝓞 K, (x : K) * star (x : K) = (t : K) + star (t : K) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨θ, τ, hτ, rfl⟩ := hx
      change (τ : K) = star (θ : K) at hτ
      have h2 : star (τ : K) = θ := by rw [hτ, star_star]
      refine ⟨θ * (τ - θ), ?_⟩
      push_cast
      rw [star_sub, star_mul', star_sub, h2, ← hτ]
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨u, hu⟩ := hy
      obtain ⟨y', hy'⟩ := exists_integer_eq_star y
      refine ⟨s + u + x * y', ?_⟩
      push_cast
      simp only [star_add, star_mul', hy', star_star]
      linear_combination hs + hu
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨c', hc'⟩ := exists_integer_eq_star c
      refine ⟨c * c' * s, ?_⟩
      rw [smul_eq_mul]
      push_cast
      simp only [star_mul', hc', star_star]
      linear_combination ((c : K) * star (c : K)) * hs
  obtain ⟨t, ht⟩ := key 1 (hI ▸ Submodule.mem_top)
  exact ⟨t, by simpa using ht.symm⟩

end GlobalTheory
