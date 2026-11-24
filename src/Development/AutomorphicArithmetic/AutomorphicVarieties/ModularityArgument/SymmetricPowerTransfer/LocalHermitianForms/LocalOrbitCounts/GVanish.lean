module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.gVanish : UpperTheory.V.Z.Sym.Loc.GVanish := by
  intro O K _ _ _ _ _ Δ τ hL j hj χ z hz hne
  haveI := hL.frac
  obtain ⟨s, u, t, hn, ht⟩ := exists_of_gOrb_ne (O := O) hj hne
  have hu : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1 := by
    rw [← map_mul]
    simp
  rcases hz with h | h
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have h2 : (s : K) ^ 2 = algebraMap O K ↑u⁻¹ := by
      calc (s : K) ^ 2 = algebraMap O K ↑u⁻¹ * (algebraMap O K ↑u * s ^ 2) := by
            rw [← mul_assoc, hu, one_mul]
        _ = _ := by rw [← hn, mul_one]
    have hi : IsIntegral O (s : K) :=
      IsIntegral.of_pow two_pos (h2 ▸ isIntegral_algebraMap)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨y * t, by rw [map_mul, hy, ht]⟩
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have e : algebraMap O K t = algebraMap O K ↑u * s := by
      apply mul_left_cancel₀ s.ne_zero
      linear_combination hn - ht
    have hs : (s : K) = algebraMap O K (↑u⁻¹ * t) := by
      rw [map_mul, e, ← mul_assoc, hu, one_mul]
    refine ⟨↑u⁻¹ * t * t - 2, ?_⟩
    rw [map_sub, map_mul, ← hs, map_ofNat]
    linear_combination -ht
