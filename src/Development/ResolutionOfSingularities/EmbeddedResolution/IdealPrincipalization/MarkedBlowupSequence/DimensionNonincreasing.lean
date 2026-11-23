module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupDimension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem krullDimSucc_eq_krullDimSucc_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    krullDimSucc X = krullDimSucc Y := by
  have f : ↥X ≃ₜ ↥Y := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, topologicalKrullDim_eq_of_homeomorph f]

theorem dimensionNonincreasingAlongBlowups : DimensionNonincreasingAlongBlowups.{u} := by
  intro T hT s i
  induction i with
  | zero =>
      intro _
      exact le_of_eq (krullDimSucc_eq_krullDimSucc_of_iso s.toSequenceOfBlowups.isoZero)
  | succ n ih =>
      intro hi
      have hlt : n < s.toSequenceOfBlowups.length := hi
      have hn : n ≤ s.toSequenceOfBlowups.length := Nat.le_of_lt hlt
      have hvalid := MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s n hn
      have hft : AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec n) :=
        hvalid.locallyOfFiniteType
      have hqc : AlgebraicGeometry.QuasiCompact (s.projectionToSpec n) :=
        hvalid.quasiCompact
      have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.toSequenceOfBlowups.center n) (s.boundary n) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc n hlt
      have hb : krullDimSucc (s.toSequenceOfBlowups.schemeAt (n + 1)) ≤ krullDimSucc (s.toSequenceOfBlowups.schemeAt n) :=
        krullDimSucc_le_of_blowup_strictNormalCrossings (s.projectionToSpec n) (s.toSequenceOfBlowups.transitionMapSucc n)
          (s.toSequenceOfBlowups.center n) (s.boundary n) hsnc
          (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt)
      exact le_trans hb (ih hn)

private theorem nontrivialPart_eq_filterNeTop {X : Scheme.{u}} (E : List X.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart E = filterNeTop E := by
  unfold MarkedIdealWithBoundary.nontrivialPart filterNeTop
  apply List.filter_congr
  intro D _
  simp

namespace MarkedIdealWithBoundary

theorem validOfSameNontrivialBoundary : MarkedIdealWithBoundary.AdmissibleUnderBoundaryReplacement.{u} := by
  intro T E hV hEq
  have hsm : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have h : filterNeTop T.boundary = filterNeTop E := by
    rw [← nontrivialPart_eq_filterNeTop, ← nontrivialPart_eq_filterNeTop]
    exact (MarkedIdealWithBoundary.sameNontrivialBoundary_iff T.boundary E).mp hEq
  exact ⟨hV.charZero, hV.locallyOfFiniteType, hV.nonzeroOnComponents, hV.one_le_mult,
    hV.quasiCompact, hV.smooth,
    inStrictNormalCrossingPosition_of_filterNeTop_eq T.structMap T.boundary E h hV.snc⟩

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution

end
