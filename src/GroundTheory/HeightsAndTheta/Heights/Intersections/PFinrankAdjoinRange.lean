module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StFinrankAdjoinRange
import Mathlib.Algebra.Lie.OfAssociative
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem FinrankAdjoinRange.proof : FinrankAdjoinRange.Statement := by
  intro F Φ Ω _ _ _ _ _ _ _ S
  set f := IsScalarTower.toAlgHom F Φ Ω
  set Φ₁ : IntermediateField F Ω := f.fieldRange
  let i : Φ ≃ₐ[F] Φ₁ := AlgEquiv.ofInjectiveField f
  have hi : (algebraMap Φ Ω : Φ → Ω) = (algebraMap Φ₁ Ω) ∘ i := by
    funext x; rfl

  have hres : (IntermediateField.adjoin Φ S).restrictScalars F =
      (IntermediateField.adjoin Φ₁ S).restrictScalars F :=
    IntermediateField.restrictScalars_adjoin_of_algEquiv i hi S

  have hle : Φ₁ ≤ Φ₁ ⊔ IntermediateField.adjoin F S := le_sup_left
  have hext : IntermediateField.extendScalars hle = IntermediateField.adjoin Φ₁ S := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_adjoin_eq_sup]
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext]

  let j : IntermediateField.adjoin Φ S ≃+* IntermediateField.adjoin Φ₁ S :=
    (IntermediateField.equivOfEq hres).toRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv j ?_
  ext x
  rfl

end GroundTheory.Heights₂.Heights.Inter
