module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld.RayExp

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) (n : ℕ) :
    heckeIdeal L χ (I ^ n) = heckeIdeal L χ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, GlobalTheory.NT.Model.heckeIdeal_top]
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.NT.Model.heckeIdeal_mul L χ (pow_ne_zero n hI) hI, ih]

theorem heckeIdeal_pow_finrank [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔮 : Ideal (𝓞 K)}
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hc : IsCoprime I 𝔮) : heckeIdeal L χ I ^ Module.finrank K L = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => rw [isUnit_iff_eq_one.1 hx, GlobalTheory.NT.Model.heckeIdeal_top, one_pow]
  | h₃ a p ha hpp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hpp, hpp.ne_zero⟩
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun hd =>
      hpp.not_unit (hc.of_mul_left_left.isUnit_of_dvd' dvd_rfl hd)
    obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob L 𝔭
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L _ hpp.ne_zero ha, mul_pow, ih ha hc.of_mul_left_right, mul_one,
      show p = 𝔭.asIdeal from rfl, GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hnd) hσ,
      ← Units.val_pow_eq_pow_val, ← map_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', map_one,
      Units.val_one]

theorem pow_finrank_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  intro K L _ _ _ _ _ 𝔮 ⟨hab, hun, _, hart⟩ I hI hc
  have hI0 : I ≠ 0 := hI
  refine (hart _ (pow_ne_zero _ hI0) hc.pow_left).1 fun χ => ?_
  rw [heckeIdeal_pow L χ hI0, heckeIdeal_pow_finrank L χ hun I hI0 hc]

end GlobalTheory.Mem.Fld.RayExp
