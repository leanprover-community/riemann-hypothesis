module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace UpperTheory.Gal.LocD

theorem prLeft : PrLeft := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ b
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨c', hc'⟩ : ∃ c' : NNReal, map (· * b) μ = c' • μ :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨(((χ b)⁻¹ : ℂˣ) : ℂ) * ((c' : ℝ) : ℂ), fun f g => ?_⟩
  set H : B → ℂ := fun y => (χ y : ℂ) * f ((y : G)⁻¹ * g) with hH
  have key : pr B μ χ (fun x => f ((b : G)⁻¹ * x)) g
      = (((χ b)⁻¹ : ℂˣ) : ℂ) * ∫ x, H (x * b) ∂μ := by
    unfold pr
    rw [← integral_const_mul]
    congr 1
    ext x
    simp only [hH, map_mul, Units.val_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
    rw [Units.val_inv_eq_inv_val]
    field_simp [(χ b).ne_zero]
  have e := (MeasurableEquiv.mulRight b).measurableEmbedding.integral_map (μ := μ) H
  rw [MeasurableEquiv.coe_mulRight] at e
  rw [key, ← e, hc', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have : pr B μ χ f g = ∫ x, H x ∂μ := rfl
  rw [this]
  ring

end UpperTheory.Gal.LocD

end
