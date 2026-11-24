module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.ProjClosure

theorem exists_isProjOver_isPullback_of_isLocalization {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (M : Submonoid O) [IsLocalization M R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsProjOver s) :
    ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'),
      IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) := by
  obtain ⟨N, c, hc, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap O R)
  have hf : Flat (spMap (algebraMap O R)) := GlobalTheory.flat_specMap_localization M R
  have hm : Mono (spMap (algebraMap O R)) := GlobalTheory.mono_specMap_localization M R
  have hq : QuasiCompact (spMap (algebraMap O R)) := inferInstance
  have : Flat (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) := MorphismProperty.of_isPullback P.flip hf
  have : Mono (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    (MorphismProperty.monomorphisms _).of_isPullback P.flip hm
  have : QuasiCompact (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    MorphismProperty.of_isPullback P.flip hq
  let j := c ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap O R)
  have H := GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ rfl
  exact ⟨j.image, j.imageι ≫ PSpace.str O N, j.toImage, ⟨N, j.imageι, inferInstance, rfl⟩,
    H.flip.paste_vert P⟩

theorem exists_projective_closure : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (a : O) [IsLocalization.Away a R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'), IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) :=
  fun _ _ _ _ _ a _ _ s hs =>
    exists_isProjOver_isPullback_of_isLocalization (Submonoid.powers a) s hs

end GlobalTheory.ProjClosure
