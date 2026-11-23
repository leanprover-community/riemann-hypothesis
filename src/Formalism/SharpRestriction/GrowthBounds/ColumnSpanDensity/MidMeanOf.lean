module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LocalHypothesisOfGlobal
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ColumnSpanNumericalFacts
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def FM (K : Cst) (X : Dat) : Prop := FixedWeightNumericalFacts K X ∧ DensityNumericalFacts K X ∧ MeanKappaNumericalFacts K X ∧ ColumnSpanNumericalFacts K X

theorem midMean_of (D : Formalism.BasicNotions.D7) (h61a : RhoSumLowerBoundEdge) (h60ab : RhoUpperBoundSmallDepth) (hE : RestEdge) (hD : RestDims) (K : Cst)
    (hK : K.Pos) : MidMean D K (FM K) := fun hA X hF R =>
  have hk := keyIneq_of D K hA h61a h60ab hE hD X hF.1 R
  mean_of K hK X hF.2.2.2 R (avg_of hD K X hF.2.1 R hk 0 (Nat.zero_le _)) (avg_of hD K X hF.2.1 R hk X.ccl le_rfl)
    (meanX_of D K hK hA X hF.2.2.1 R)

theorem TransportedAlt.and {K : Cst} {F G : ℝ → Dat → Prop} (hF : TransportedAlt K F) (hG : TransportedAlt K G) : TransportedAlt K fun C X => F C X ∧ G C X := by
  obtain ⟨T, Cn, hT, hCn, h⟩ := hF
  obtain ⟨T', Cn', _, _, h'⟩ := hG
  exact ⟨max T T', max Cn Cn', lt_max_of_lt_left hT, lt_max_of_lt_left hCn, fun CH hCH C hC X hX =>
    ⟨h CH (le_trans (le_max_left _ _) hCH) C (le_trans (le_max_left _ _) hC) X hX,
      h' CH (le_trans (le_max_right _ _) hCH) C (le_trans (le_max_right _ _) hC) X hX⟩⟩

end Formalism.MainNotions.flipOneThree.Pf

end
