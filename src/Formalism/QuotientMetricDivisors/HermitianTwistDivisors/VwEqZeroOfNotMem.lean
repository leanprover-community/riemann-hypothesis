module

public import Formalism.QuotientMetricDivisors.StatementACE
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationZeroReduction

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_eq_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {s} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hs0
  classical
  have hnd : ¬ w.asIdeal ∣ Ideal.span {s} := by
    rw [Ideal.dvd_span_singleton]; exact hs
  have hirr : Irreducible w.asIdeal := (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible
  have hc := mt (Associates.count_ne_zero_iff_dvd hJ hirr).mp hnd
  push_neg at hc
  unfold vw
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ, Nat.cast_eq_zero]
  convert hc

end ValuationZeroReduction

theorem reduction_first_step : StepA := by
  intro K _ _ _ w n D M π ι B P ζ σ hζ hvζ hP hM x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ w.asIdeal := hs
  obtain ⟨y, hy, hyx⟩ := hsx
  obtain ⟨F, hF, hFy⟩ := hy
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hFy hyx
  have hs0 : s ≠ 0 := fun h => hs' (h ▸ w.asIdeal.zero_mem)
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h; apply hs0; apply IsFractionRing.injective (𝓞 K) K; rw [map_zero]; exact h
  have hPF : P F = ζ * (algebraMap (𝓞 K) K s * B x) := by
    rw [hP F, hFy, hyx, ← algebraMap_smul K s x, map_smul, smul_eq_mul]
  have hvmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b := by
    intro a b ha hb
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w
      (fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))
      (fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))]
  have hv0 : vw w (algebraMap (𝓞 K) K s) = 0 := ValuationZeroReduction.vw_eq_zero_of_not_mem w s hs'
  by_cases hBx : B x = 0
  · exact Or.inl hBx
  · right
    have hPF0 : P F ≠ 0 := by rw [hPF]; exact mul_ne_zero hζ (mul_ne_zero hsK hBx)
    rcases hM F hF with h0 | hσ
    · exact absurd h0 hPF0
    · rw [hPF, hvmul _ _ hζ (mul_ne_zero hsK hBx), hvmul _ _ hsK hBx, hvζ, hv0] at hσ
      simpa using hσ

end Formalism.DivisionValues
