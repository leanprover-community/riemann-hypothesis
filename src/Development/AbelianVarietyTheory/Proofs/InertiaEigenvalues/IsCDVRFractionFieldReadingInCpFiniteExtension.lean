module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
public import Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts

noncomputable section

namespace GlobalTheory.GeoTie.ReadExt

section Val

open Classical

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_unit' (u : Vˣ) : vV V (algebraMap V K u) = 0 := by
  have : valV V (algebraMap V K u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_irr' {a : V} (ha : Irreducible a) : vV V (algebraMap V K a) = 1 := by
  have : valV V (algebraMap V K a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem vV_pow' {x : K} (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]


end Val

theorem norm_eq_zpow (T : CDVR) {C : Type} [NormedField C] (k : T.Fr →+* C)
    (hball : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x) {π : T.V} (hπ : Irreducible π) (x : T.Fr) (hx : x ≠ 0) :
    ‖k x‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V x := by
  have hu : ∀ u : T.Vˣ, ‖k (algebraMap T.V T.Fr u)‖ = 1 := by
    intro u
    have h1 := (hball (algebraMap T.V T.Fr u)).2 ⟨u, rfl⟩
    have h2 := (hball (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖k (algebraMap T.V T.Fr u)‖ * ‖k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one,
        norm_one]
    nlinarith [norm_nonneg (k (algebraMap T.V T.Fr u)), norm_nonneg (k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ)))]
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hρ0 : ‖k (algebraMap T.V T.Fr π)‖ ≠ 0 := by
    simpa using hπ0
  have key : ∀ a : T.V, a ≠ 0 →
      ‖k (algebraMap T.V T.Fr a)‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V (algebraMap T.V T.Fr a) := by
    intro a ha
    obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu0 : algebraMap T.V T.Fr u ≠ 0 := by simp
    rw [map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hπ0), vV_pow', vV_unit', vV_irr' hπ, map_mul, norm_mul, hu,
      map_pow, norm_pow]
    simp
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap T.V T.Fr b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hv := vV_mul (V := T.V) hx hb1
  rw [div_mul_cancel₀ _ hb1] at hv
  rw [map_div₀, norm_div, key a ha0, key b hb0, ← zpow_sub₀ hρ0, hv]
  congr 1
  ring

end GlobalTheory.GeoTie.ReadExt
