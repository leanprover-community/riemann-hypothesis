module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Convex
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue

theorem entire_of_halfPlane_continuations :
    ∀ (S : ℂ → ℂ) (G : ℕ → ℂ → ℂ), (∀ k, DifferentiableOn ℂ (G k) {s | -(k : ℝ) < s.re}) →
  (∀ k s, 1 < s.re → G k s = S s) → ∃ T : ℂ → ℂ, Differentiable ℂ T ∧ ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → T s = G k s := by
  intro S G hG hS
  have hopen : ∀ r : ℝ, IsOpen {s : ℂ | r < s.re} := fun r =>
    isOpen_lt continuous_const Complex.continuous_re

  have hagree : ∀ j k : ℕ, j ≤ k → Set.EqOn (G j) (G k) {s : ℂ | -(j : ℝ) < s.re} := by
    intro j k hjk
    have hsub : {s : ℂ | -(j : ℝ) < s.re} ⊆ {s : ℂ | -(k : ℝ) < s.re} := by
      intro s hs
      have h1 : (j : ℝ) ≤ k := by exact_mod_cast hjk
      simp only [Set.mem_setOf_eq] at hs ⊢
      linarith
    have hfj : AnalyticOnNhd ℂ (G j) {s : ℂ | -(j : ℝ) < s.re} :=
      (hG j).analyticOnNhd (hopen _)
    have hfk : AnalyticOnNhd ℂ (G k) {s : ℂ | -(j : ℝ) < s.re} :=
      ((hG k).mono hsub).analyticOnNhd (hopen _)
    have hpre : IsPreconnected {s : ℂ | -(j : ℝ) < s.re} :=
      (convex_halfSpace_re_gt (-(j : ℝ))).isPreconnected
    have h2 : (2 : ℂ) ∈ {s : ℂ | -(j : ℝ) < s.re} := by
      have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]
      linarith
    have hev : G j =ᶠ[nhds (2 : ℂ)] G k := by
      have hmem : {s : ℂ | (1 : ℝ) < s.re} ∈ nhds (2 : ℂ) :=
        (hopen 1).mem_nhds (by simp)
      filter_upwards [hmem] with s hs
      rw [hS j s hs, hS k s hs]
    exact hfj.eqOn_of_preconnected_of_eventuallyEq hfk hpre h2 hev

  have hidx : ∀ s : ℂ, -((⌈-s.re⌉₊ + 1 : ℕ) : ℝ) < s.re := by
    intro s
    have h1 : -s.re ≤ (⌈-s.re⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith

  have hT : ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → G (⌈-s.re⌉₊ + 1) s = G k s := by
    intro k s hs
    rcases le_total (⌈-s.re⌉₊ + 1) k with h | h
    · exact hagree _ _ h (hidx s)
    · exact (hagree _ _ h hs).symm
  refine ⟨fun s => G (⌈-s.re⌉₊ + 1) s, ?_, hT⟩
  intro s
  set k := ⌈-s.re⌉₊ + 1 with hk
  have hs : s ∈ {w : ℂ | -(k : ℝ) < w.re} := hidx s
  have hnh : {w : ℂ | -(k : ℝ) < w.re} ∈ nhds s := (hopen _).mem_nhds hs
  have hd : DifferentiableAt ℂ (G k) s := (hG k).differentiableAt hnh
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hnh] with w hw
  exact hT k w hw

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue
