module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace GlobalTheory.FrameRead

theorem norm_map_le_one_of_isIntegral_int {F C : Type} [CommRing F] [NormedField C] [IsUltrametricDist C] (f : F →+* C) {x : F}
    (hx : IsIntegral ℤ x) : ‖f x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (f x) := hx.map f.toIntAlgHom
  have := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hy.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_le_one_iff_integral_at : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  intro K _ _ l _ w e0 hw x
  constructor
  · intro hx
    obtain ⟨n, d, h | h⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact h⟩
    · by_cases hn : n ∈ w.asIdeal
      · exfalso
        refine d.2 ((hw d).2 ?_)
        have h1 : ‖e0 ((d : 𝓞 K) : K)‖ = ‖e0 x‖ * ‖e0 (n : K)‖ := by
          have : ((d : 𝓞 K) : K) = x * (n : K) := h.symm
          rw [this, map_mul, norm_mul]
        rw [h1]
        have h2 : ‖e0 (n : K)‖ < 1 := (hw n).1 hn
        calc ‖e0 x‖ * ‖e0 (n : K)‖ ≤ 1 * ‖e0 (n : K)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact h2
      · exact ⟨n, hn, d, by rw [mul_comm]; exact h⟩
  · rintro ⟨s, hs, r, hr⟩
    have hs1 : 1 ≤ ‖e0 (s : K)‖ := by
      by_contra h
      exact hs ((hw s).2 (lt_of_not_ge h))
    have hr1 : ‖e0 (r : K)‖ ≤ 1 := norm_map_le_one_of_isIntegral_int e0 r.isIntegral_coe
    have h1 : ‖e0 (s : K)‖ * ‖e0 x‖ ≤ 1 := by rw [← norm_mul, ← map_mul, hr]; exact hr1
    nlinarith [norm_nonneg (e0 x)]

end GlobalTheory.FrameRead
