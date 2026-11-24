module

public import Formalism.HermitianLattices.StatementMass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open MeasureTheory NumberField Finset

namespace GlobalTheory


open MeasureTheory NumberField Finset in
theorem _root_.GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K ∧
      (3 / 2 : ℝ) ≤ 2 * _root_.Formalism.HermitianLatticesTheory.vInv K ∧
      Real.sqrt |(discr K : ℝ)| = (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ _root_.Formalism.HermitianLatticesTheory.fDeg K := by
  intro K _ _ hK
  have hf : _root_.Formalism.HermitianLatticesTheory.fDeg K = InfinitePlace.nrComplexPlaces K := by
    unfold _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hn : Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hf]; exact IsTotallyComplex.finrank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K := by omega
  have hv : 2 * _root_.Formalism.HermitianLatticesTheory.vInv K = |(discr K : ℝ)| ^ (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) := by
    unfold _root_.Formalism.HermitianLatticesTheory.vInv; ring
  have hD0 : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hbound : (3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≤ |(discr K : ℝ)| := by
    have hd := abs_discr_ge (K := K) (by omega)
    rw [hn, Int.cast_abs] at hd
    refine le_trans ?_ hd
    obtain ⟨m, hm⟩ : ∃ m, _root_.Formalism.HermitianLatticesTheory.fDeg K = m + 1 := ⟨_root_.Formalism.HermitianLatticesTheory.fDeg K - 1, by omega⟩
    rw [hm, pow_mul, pow_mul, pow_succ ((3 / 2 : ℝ) ^ 2), pow_succ ((3 * Real.pi / 4) ^ 2)]
    have hpi := Real.pi_gt_d2
    have hc : (11 / 2 : ℝ) ≤ (3 * Real.pi / 4) ^ 2 := by nlinarith
    have hm' : ((3 / 2 : ℝ) ^ 2) ^ m ≤ ((3 * Real.pi / 4) ^ 2) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) m
    have hc' : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
    have := mul_le_mul hm' hc' (by positivity) (by positivity)
    linarith
  have hne : (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≠ 0 := by omega
  have hexp : (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) = (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ := by
    push_cast; rw [one_div]
  refine ⟨hn, h1, ?_, ?_⟩
  · rw [hv, hexp]
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) hne).symm
      _ ≤ |(discr K : ℝ)| ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hbound (by positivity)
  · rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]
    congr 1
    have : (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast (by omega : _root_.Formalism.HermitianLatticesTheory.fDeg K ≠ 0)
    field_simp

end GlobalTheory
