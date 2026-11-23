module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLift
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

@[expose] public section

open GlobalTheory.SiegelTor

namespace GlobalTheory.CycLift

theorem exists_hom_to_field : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
    ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  intro M hM K _ y hy hMK
  obtain ⟨p, hcp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharZero (WittVector p K) := by
      obtain ⟨q, hq⟩ := CharP.exists (WittVector p K)
      have h1 : ((q : ℕ) : K) = 0 := by
        have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (CharP.cast_eq_zero (WittVector p K) q)
        rwa [map_natCast, map_zero] at this
      have h2 : p ∣ q := (CharP.cast_eq_zero_iff K p q).1 h1
      rcases CharP.char_is_prime_or_zero (WittVector p K) q with h | h
      · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp h).1 h2
        subst h3
        exact absurd (CharP.cast_eq_zero (WittVector p K) p) (WittVector.p_nonzero p K)
      · subst h
        exact CharP.charP_to_charZero _
    let π : WittVector p K →+* K := WittVector.constantCoeff
    have hcc : ∀ x : K, π (WittVector.teichmuller p x) = x := fun x => by simp [π]
    have hu : IsPrimitiveRoot (WittVector.teichmuller p y) M :=
      ⟨by rw [← map_pow, hy.pow_eq_one, map_one], fun l hl => hy.dvd_of_pow_eq_one l (by
        have := congrArg π hl
        rwa [map_pow, hcc, map_one] at this)⟩
    have hnV : IsUnit (M : WittVector p K) := by
      refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
      have : π (M : WittVector p K) ≠ 0 := by rw [map_natCast]; exact hMK.ne_zero
      exact this
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hu hnV
    exact ⟨π.comp f, by rw [RingHom.comp_apply, hfζ, hcc]⟩
  · haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hy hMK
    exact ⟨f, hfζ⟩

end GlobalTheory.CycLift
