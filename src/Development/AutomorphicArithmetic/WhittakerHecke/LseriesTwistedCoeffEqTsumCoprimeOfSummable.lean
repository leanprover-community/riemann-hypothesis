module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.lseries_twisted_coeff_eq_tsum_coprime_of_summable :
    ∀ (N : ℕ) (χ : HChar ℚ) (μ : ℕ → ℂ) (s : ℂ),
        Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) →
        LSeriesSummable (bN N χ μ) s ∧
          LSeries (bN N χ μ) s = ∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
  intro N χ μ s hS
  have hterm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, LSeries.term (bN N χ μ) s (n : ℕ) =
      μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
    rintro ⟨n, hn, hc⟩
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne']
    simp only [bN, if_pos hc]
    rw [Complex.cpow_sub _ _ hn0, Complex.cpow_one]
    ring
  have hzero : ∀ x ∉ Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ),
      LSeries.term (bN N χ μ) s x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero h0]
      have hc : ¬ x.Coprime N := fun hc => hx ⟨⟨x, Nat.pos_of_ne_zero h0, hc⟩, rfl⟩
      simp only [bN, if_neg hc, zero_div]
  have heq : (LSeries.term (bN N χ μ) s) ∘ (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) =
      fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) :=
    funext hterm
  refine ⟨(Subtype.val_injective.summable_iff hzero).1 (heq ▸ hS), ?_⟩
  have hsupp : Function.support (LSeries.term (bN N χ μ) s) ⊆
      Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) := by
    intro x hx
    by_contra h
    exact hx (hzero x h)
  rw [LSeries, ← Subtype.val_injective.tsum_eq hsupp]
  exact tsum_congr hterm
