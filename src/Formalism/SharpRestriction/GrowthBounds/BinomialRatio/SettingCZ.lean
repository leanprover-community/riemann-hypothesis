module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem settingCZ : SettingCharZeroAt := by
  unfold SettingCharZeroAt
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  have hpW : ¬IsUnit (p : W) := hS.p_unif.1

  have hW : CharZero W := by
    rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
    · exfalso
      haveI hcp : CharP W (ringChar W) := ringChar.charP W
      by_cases hqp : ringChar W = p
      · apply hS.p_unif.ne_zero
        rw [← hqp]
        exact CharP.cast_eq_zero W (ringChar W)
      · have hcop : Nat.Coprime p (ringChar W) :=
          (Nat.coprime_primes hS.prime hq).mpr (Ne.symm hqp)
        apply hpW
        have hu : IsUnit (p : ZMod (ringChar W)) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]
          exact Units.isUnit _
        have hu' := hu.map (ZMod.castHom (dvd_refl (ringChar W)) W)
        simpa using hu'
    · haveI : CharP W 0 := by
        rw [← hq]
        exact ringChar.charP W
      exact CharP.charP_to_charZero W
  haveI := hS.frac_alt
  have hQ : CharZero Qq := charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)
  have hK : CharZero Kf := (RingHom.charZero_iff ι.injective).mp hQ

  have hpO : ¬IsUnit (p : O) := by
    intro hu
    have hint : jO.IsIntegral := RingHom.IsIntegral.of_finite hS.finite
    have hmax : ((IsLocalRing.maximalIdeal O).comap jO).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' jO hint (IsLocalRing.maximalIdeal O)
    have hle : (IsLocalRing.maximalIdeal O).comap jO = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal hmax
    have hpm : (p : W) ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hpW
    rw [← hle, Ideal.mem_comap, map_natCast] at hpm
    exact (IsLocalRing.mem_maximalIdeal _).mp hpm hu
  exact ⟨hK, hpO⟩

end Formalism.MainNotions.ColumnSystems.Pf
