module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTypedOfVolumeStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeStepOfSiegelWeil
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

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.CountConstants

theorem count_constants_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
      (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
      (∀ {eps : ℝ} (Fm : FamP eps), cIc ≤ (c30 Fm.cOut).c) ∧
      ∀ (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps),
        CountE.CountAllPointsClass P Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb := by
  intro hSW
  have H := GlobalTheory.CountBridge.count_typed_of_volumeStep (GlobalTheory.GaussMean.volumeStep_of_siegelWeil hSW)
  choose n₀ C₀ hC₀ HC using H
  let Af : List ℝ → ℝ := fun l => 2 * (l.getD 6 0 + 1)
  refine ⟨fun l => ⟨0, n₀ (Af l), Af l, 0, C₀ (Af l), 1 / 16, 1 / 16⟩, 1 / 16,
    fun Fm => ⟨hC₀ _, le_refl _⟩, by norm_num, fun Fm => le_refl _, fun P {_} Fm => ⟨by norm_num, by norm_num, ?_⟩⟩
  intro x i
  exact CountE.count_class_of_count P (HC _ _ le_rfl _ le_rfl _)

end GlobalTheory.CountConstants
