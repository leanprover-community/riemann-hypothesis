module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
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

open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem initial_product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1)
      (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) →
      (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) →
      ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  intro Ω _ ν r l hl len Ph A Rr hlen hpos hPh h0 hmass hA hR hm0 hrat
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · simp [hmass]
  obtain ⟨s, rfl⟩ : ∃ s, l = s + 1 := ⟨l - 1, by omega⟩
  have hs : s ≤ r := by omega
  have hq' : ∀ q, q ≤ (s + 1) ^ 2 → q ≤ (r + 1) ^ 2 :=
    fun q hq => hq.trans (Nat.pow_le_pow_left (by omega) 2)
  have h1 : ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal ((fun a : Fin (s + 1) => len (Fin.castLE hl a)) 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q) := by
    intro q hq
    have e : Fin.castLE hl (0 : Fin (s + 1)) = 0 := Fin.ext (by simp)
    simp only [e]
    exact hm0 q (hq' q hq)
  have h2 : ∀ a : Fin s, ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal (((fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.succ x /
        (fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.castSucc x) ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (Rr ^ (2 * q)) := by
    intro a q hq
    have e1 : Fin.castLE hl a.succ = (⟨a, by omega⟩ : Fin r).succ := Fin.ext (by simp)
    have e2 : Fin.castLE hl a.castSucc = (⟨a, by omega⟩ : Fin r).castSucc := Fin.ext (by simp)
    simp only [e1, e2]
    exact hrat _ q (hq' q hq)
  have key := product_moment_le Ω ν s (fun a => len (Fin.castLE hl a)) Ph A Rr
    (fun _ => hlen _) (fun _ => hpos _) hPh h0 hmass hA hR h1 h2
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (pow_nonneg (zero_le_one.trans hR) _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by omega)) hA) _

end GlobalTheory.MomentHolder
