module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc

theorem dvr_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a y : O}
    (ha : a ∈ IsLocalRing.maximalIdeal O) (hy : y ≠ 0) : ∃ k : ℕ, y ∣ a ^ k := by
  have hyt : IsDiscreteValuationRing.addVal O y ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hyt
  have ha1 : 1 ≤ IsDiscreteValuationRing.addVal O a := by
    rw [ENat.one_le_iff_ne_zero, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact ha
  refine ⟨n, IsDiscreteValuationRing.addVal_le_iff_dvd.1 ?_⟩
  rw [IsDiscreteValuationRing.addVal_pow, ← hn]
  calc ((n : ℕ∞)) = n • (1 : ℕ∞) := by simp
    _ ≤ n • IsDiscreteValuationRing.addVal O a := nsmul_le_nsmul_right ha1 n

theorem smul_pow_integral (K : UQ) (B : InvAlg K) (a : K.O) (ha : K.Small a) (x : B.A) :
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  have hxE : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
  obtain ⟨⟨m, hm⟩, hmx⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors K.O) x hxE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, w, hw⟩ := dvr_dvd_pow ha.2.1 hm0
  refine ⟨k, ?_⟩
  have hsm : (m • x : B.A) = (⟨m, hm⟩ : nonZeroDivisors K.O) • x := rfl
  have : (al K a ^ k) • x = algebraMap K.O B.A w * (m • x) := by
    rw [← map_pow, algebraMap_smul, hw, mul_comm, mul_smul, Algebra.smul_def]
  rw [this]
  exact isIntegral_algebraMap.mul (hsm ▸ hmx)

end GlobalTheory.UnitLemma.Desc
