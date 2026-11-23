module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.PowerSeriesComplete

theorem isAdicComplete_map_C : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R))
      (MvPowerSeries (Fin n) R) := by
  intro R _ _ I hI n
  have hfg : I.FG := IsNoetherian.noetherian I
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = algebraMap R (MvPowerSeries (Fin n) R) := rfl
  have hP : IsPrecomplete I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isPrecomplete_pi (M := R) (Fin n →₀ ℕ) hfg
  have hH : IsHausdorff I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isHausdorff_pi (M := R) (Fin n →₀ ℕ) hfg
  rw [hC]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

end GlobalTheory.PowerSeriesComplete
