module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfMemSmallCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

theorem small_descent_H2_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  refine GlobalTheory.CatCoh.Desc.pull2_bijective (O κ s) ?_ (IsSmall κ s U) ?_ ?_
  · intro T b
    obtain ⟨T', l, h1, h2, h3, h4⟩ := GlobalTheory.ThickLoc.exists_localization R I κ X s T b
    exact ⟨T', l, by simpa only [mp_O] using h1, by simpa only [mp_O] using h2,
      by simpa only [mp_O] using h3, by simpa only [mp_O] using h4⟩
  · rintro S S' φ ⟨i, hi⟩
    exact ⟨i, GlobalTheory.Cris.Thick.Hom.le_preimage φ hi⟩
  · intro T
    obtain ⟨n, b, hb, h⟩ := exists_finite_small_cover R I κ X s K U hU T
    exact ⟨n, b, hb, fun i S u hu => h i S u (by simpa only [mp_O] using hu)⟩

end GlobalTheory.Cris
