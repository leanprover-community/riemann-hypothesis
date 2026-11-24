module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicator
import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem yv_measurable : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yv k r z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset k r z z' γ R₀ y) := by
  intro k r z z' γ hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yv k r z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r r z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z' (Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z').2.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z (γ * Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z).2.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset k r z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yv k r z z' γ (Matrix.of x.1) ∧ Yv k r z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
