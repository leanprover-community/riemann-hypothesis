module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
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

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

theorem isAdmissible_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) : (T.baseChange L f).IsAdmissible := by
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base L f) :=
    instFlatSpecMapOfFieldHom T.base L f
  have hfst : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    inferInstance
  refine
    { charZero := ‹CharZero L›
      locallyOfFiniteType := ?_
      nonzeroOnComponents := ?_
      one_le_mult := hV.one_le_mult
      quasiCompact := ?_
      smooth := ?_
      snc := ?_ }
  · exact
      (inferInstance : AlgebraicGeometry.LocallyOfFiniteType
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact hV.nonzeroOnComponents.comap_of_flat
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  · exact
      (inferInstance : AlgebraicGeometry.QuasiCompact
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact smooth_pullbackSnd_specMap T.structMap (CommRingCat.ofHom f)
  · exact inStrictNormalCrossingPosition_comap_pullback_specMap T.structMap (CommRingCat.ofHom f) T.boundary hV.snc

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution
