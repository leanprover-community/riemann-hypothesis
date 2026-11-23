module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalLengthPlaces
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalQuotCard
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredPlacesFinite
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalQuotCentred
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPlacesRingQuot
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LocalLengthPlaces.proof (hC : LocalQuotCard.Statement) (hF : CentredPlacesFinite.Statement)
    (hE : LocalQuotCentred.Statement) (hP : PlacesRingQuot.Statement) :
    LocalLengthPlaces.Statement := by
  intro L _ _ O hft hfr m _ f hf
  have hfS : (f : L) ∈ placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} :=
    fun w hw ↦ hw.1 f
  have hg : (⟨f, hfS⟩ : placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}) ≠ 0 :=
    fun h ↦ hf (Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [← Real.log_pow, ← Nat.cast_pow, ← hC L O hft hfr m f hf, hE L O hft hfr m f hf ⟨f, hfS⟩ rfl]
  exact hP L _ (hF L O hft hfr m) ⟨f, hfS⟩ hg

end GroundTheory.Heights₂.Heights
