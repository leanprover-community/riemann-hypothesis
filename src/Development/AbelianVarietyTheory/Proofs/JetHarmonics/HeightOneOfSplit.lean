module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Mathlib.RingTheory.FormalGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSmallInPrimePow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNormStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrderStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
