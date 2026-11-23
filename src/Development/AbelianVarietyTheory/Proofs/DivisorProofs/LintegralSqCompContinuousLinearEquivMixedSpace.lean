module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem lintegral_sq_comp_linearEquiv_mixed (F : Type) [Field F] [NumberField F] (κ : Type)
    [Fintype κ] (n : ℕ)
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    ∃ c : ℝ≥0∞, ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ,
      ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 = c * ∫⁻ z, ‖h z‖ₑ ^ 2 := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := MeasurableAdd₂.toMeasurableAdd
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let eM := Q.toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n)))).IsAddHaarMeasure :=
    Q.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n))) =
      c • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨(c : ℝ≥0∞), fun h => ?_⟩
  have h1 : ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 =
      ∫⁻ z, ‖h z‖ₑ ^ 2 ∂(Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    rw [lintegral_map_equiv]; rfl
  rw [h1, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory
