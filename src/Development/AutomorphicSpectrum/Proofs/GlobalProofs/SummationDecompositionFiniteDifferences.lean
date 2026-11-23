module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeTilingBySignRegionsStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeValuesNegativeIntegerRationalStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem series_value_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (N p : ℕ), Fintype.card ι * p < N →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∃ q : ℚ, ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) := by
  intro ι _ r a b u cs N p hN hcase hval
  by_cases hex : ∃ i, cs.count i = N
  · obtain ⟨i, hi⟩ := hex
    refine ⟨0, ?_⟩
    have h0 := GlobalTheory.T.high_difference_vanishes_negative_integer ι r a b cs i N p hi hN
    simp [h0]
  · have hsupp : ∀ m : Fin r → ℕ, m ≠ 0 → u m = 0 := by
      intro m hm
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hm (funext hcon)
      rcases hcase i with h | h
      · exact absurd ⟨i, h⟩ hex
      · exact h m hi
    obtain ⟨ρ, hρ⟩ := GlobalTheory.T.cone_values_negative_integer_rational ι r a b p hval cs
    refine ⟨u 0 * ρ 0, ?_⟩
    rw [tsum_eq_single 0 (fun m hm => by simp [hsupp m hm]), hρ 0]
    push_cast
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
