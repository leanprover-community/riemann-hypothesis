module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open AlgebraicGeometry

theorem DominatingDVR.closed : DominatingDVR.Statement :=
  DominatingDVR.proof
    (KrullAkizuki.proof (KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.proof))
    BlowUpChart.proof

theorem not_isField_stalk_of_ne_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (z : Z)
    (hz : z ≠ genericPoint Z) : ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hmem : genericPoint Z ∈ Set.range (Z.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hgen
  obtain ⟨y, hy⟩ := hmem
  have hmax : IsLocalRing.maximalIdeal (Z.presheaf.stalk z) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF)
  have hyc : y = IsLocalRing.closedPoint (Z.presheaf.stalk z) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal y.isPrime.ne_top
    · exact hmax.le.trans bot_le
  apply hz
  rw [← hy, hyc, Scheme.fromSpecStalk_closedPoint]

theorem DominatingDVRScheme.proof : DominatingDVRScheme.Statement := by
  intro Z _ _ z hz
  exact DominatingDVR.closed (Z.presheaf.stalk z) (not_isField_stalk_of_ne_genericPoint Z z hz)
    Z.functionField

end GroundTheory.Heights₂.Heights.Model
