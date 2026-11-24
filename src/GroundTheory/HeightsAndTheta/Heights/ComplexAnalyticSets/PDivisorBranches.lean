module

import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorRegularGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDivisorChartGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDoublePointsGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPointBranches
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  apply _root_.GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.quotient_inf_dim_lt <;> assumption

theorem not_mem_zeroSet_of_le {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' :=
  fun h => hq fun f hf => h f (hle hf)

theorem proof (hModel : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement)
    (hReg : DivisorRegularGeneric.Statement) (hChart : NormalDivisorChartGeneric.Statement)
    (hDouble : NormalDoublePointsGeneric.Statement) (hGood : DivisorGoodPointBranches.Statement) :
    DivisorBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨M⟩ := hModel n J hJ
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hReg n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hChart n d J u M hJ hdim hu
  obtain ⟨I₃, hle₃, hdim₃, hI₃⟩ := hDouble n d J u M hJ hdim hu
  refine ⟨I₁ ⊓ I₂ ⊓ I₃, le_inf (le_inf hle₁ hle₂) hle₃,
    quotient_inf_dim_lt (quotient_inf_dim_lt hdim₁ hdim₂) hdim₃, ?_⟩
  intro q hqJ hqu hqI
  exact hGood n d J u M q hJ hdim hu hqJ hqu
    (hI₁ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_left) hqI))
    (hI₂ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_right) hqI))
    (hI₃ q hqJ hqu (not_mem_zeroSet_of_le inf_le_right hqI))

end DivisorBranches

end

end GroundTheory.Heights₂.Heights
