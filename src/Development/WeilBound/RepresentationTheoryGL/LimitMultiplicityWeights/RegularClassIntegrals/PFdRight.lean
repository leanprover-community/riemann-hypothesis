module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
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

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PFdRight

end MainStatements.WeightKernel.PFdRight

theorem MainStatements.WeightKernel.fdRight : MainStatements.WeightKernel.FDRight := by
  intro G _ _ _ _ _ _ Γ _ μ _ _ 𝓕 h𝓕 F hF g
  have h2 : IsFundamentalDomain Γ ((fun x : G => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have key : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in (fun x : G => x * g⁻¹) ⁻¹' 𝓕, F x ∂μ := by
    rw [← Set.image_mul_right,
      (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) F 𝓕]
  rw [key]
  exact h2.setIntegral_eq h𝓕 (fun γ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hF γ γ.2 x)
