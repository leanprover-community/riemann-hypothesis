module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

theorem mvPowerSeries_derivation_coeffwise (σ R : Type) [CommRing R] (D : Derivation ℤ R R) :
    ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R),
      ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  classical
  let L : MvPowerSeries σ R →ₗ[ℤ] MvPowerSeries σ R :=
    { toFun := fun F => fun α => D (MvPowerSeries.coeff α F)
      map_add' := by
        intro F G
        funext α
        show D (MvPowerSeries.coeff α (F + G)) = D (MvPowerSeries.coeff α F) + D (MvPowerSeries.coeff α G)
        rw [map_add (f := _), map_add (f := _)]
      map_smul' := by
        intro n F
        funext α
        show D (MvPowerSeries.coeff α (n • F)) = n • D (MvPowerSeries.coeff α F)
        rw [map_zsmul, map_zsmul] }
  have hL : ∀ F α, MvPowerSeries.coeff α (L F) = D (MvPowerSeries.coeff α F) := fun _ _ => rfl
  refine ⟨Derivation.mk' L ?_, ?_⟩
  · intro F G
    ext α
    rw [smul_eq_mul, smul_eq_mul, map_add (f := _)]
    erw [hL]

    rw [MvPowerSeries.coeff_mul, map_sum,
    MvPowerSeries.coeff_mul, mul_comm G, MvPowerSeries.coeff_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    erw [hL, hL]
    exact congrArg (_ + ·) (mul_comm _ _)
  · intro F α
    rfl

end GlobalTheory
