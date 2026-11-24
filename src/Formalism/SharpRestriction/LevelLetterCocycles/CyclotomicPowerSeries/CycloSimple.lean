module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

private theorem constantCoeff_aeval_eq_aeval_constantCoeff {S : Type} [CommRing S] (Q : Polynomial S) (y : PowerSeries S) :
    constantCoeff (Polynomial.aeval y Q) = Polynomial.aeval (constantCoeff y) Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1

theorem cycloSimple : CycloSimpleStatement := by
  intro LL S _ _ _ _ m hm ζ E hζ hE0 hE
  have hζm : ζ ^ m = 1 := by
    obtain ⟨q, hq⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m LL
    have h := congrArg (Polynomial.aeval ζ) hq
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.1 h
  have hζu : IsUnit ζ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hmul : ζ * ζ ^ k = 1 := by rw [← pow_succ']; exact hζm
    exact ⟨⟨ζ, ζ ^ k, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩
  set Φ := Polynomial.cyclotomic m LL with hΦ
  have hsep : Φ.Separable :=
    (Polynomial.X_pow_sub_one_separable_iff.2 (by exact_mod_cast hm.ne')).of_dvd
      (Polynomial.cyclotomic.dvd_X_pow_sub_one m LL)
  obtain ⟨a, b, hab⟩ := hsep
  have hu : IsUnit (Polynomial.aeval ζ (Polynomial.derivative Φ)) := by
    have h := congrArg (Polynomial.aeval ζ) hab
    simp only [map_add (f := _), map_mul, map_one, hζ, mul_zero, zero_add] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  set y : PowerSeries S := C ζ * E with hy
  have hy0 : constantCoeff y = ζ := by simp [hy, hE0]
  have hyd : derivative y = y := by
    simp [hy, Derivation.leibniz, derivative_C, hE, smul_eq_mul]
  have hF : Polynomial.aeval y Φ = Polynomial.aeval y (Φ.map (algebraMap LL S)) :=
    (Polynomial.aeval_map_algebraMap S y Φ).symm
  have h0 : constantCoeff (Polynomial.aeval y Φ) = 0 := by
    rw [hF, constantCoeff_aeval_eq_aeval_constantCoeff, hy0, Polynomial.aeval_map_algebraMap, hζ]
  have h1 : constantCoeff (derivative (Polynomial.aeval y Φ)) =
      Polynomial.aeval ζ (Polynomial.derivative Φ) * ζ := by
    rw [hF, Derivation.map_aeval, hyd, smul_eq_mul, map_mul, constantCoeff_aeval_eq_aeval_constantCoeff, hy0,
      Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
  obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.2 h0
  have hGc : constantCoeff (derivative (Polynomial.aeval y Φ)) = constantCoeff G := by
    rw [hG]
    simp [Derivation.leibniz, derivative_X, smul_eq_mul]
  have hGu : IsUnit G := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← hGc, h1]
    exact hu.mul hζu
  refine ⟨hGu.unit, ?_⟩
  rw [IsUnit.unit_spec, hG, mul_comm]

end LevelStatements.Lv
