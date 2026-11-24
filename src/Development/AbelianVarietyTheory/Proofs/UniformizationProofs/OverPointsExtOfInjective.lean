module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.over_points_ext_of_injective (S : Scheme.{0}) (G : Over S) [IsSeparated G.hom]
    (W F : Type) [CommRing W] [CommRing F] (φ : W →+* F) (hφ : Function.Injective φ)
    (p : Spec (CommRingCat.of W) ⟶ S) (y y' : Over.mk p ⟶ G)
    (h : (Spec.map (CommRingCat.ofHom φ)) ≫ y.left = (Spec.map (CommRingCat.ofHom φ)) ≫ y'.left) :
    y = y' := by
  let d : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  have hd : d ≫ y = d ≫ y' := by
    ext1
    simpa [d] using h
  let l := equalizer.lift d hd
  have hl : l ≫ equalizer.ι y y' = d := equalizer.lift_ι d hd
  have hfac : l.left ≫ (equalizer.ι y y').left = Spec.map (CommRingCat.ofHom φ) := by
    rw [← Over.comp_left, hl]
    rfl
  have hdom : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) :=
    (_root_.GlobalTheory.schemeDominant_specMap_iff _).2 (by simpa using hφ)
  have hdomι : IsSchemeTheoreticallyDominant (equalizer.ι y y').left :=
    ⟨eq_bot_iff.2 ((Scheme.Hom.le_ker_comp l.left _).trans (by rw [hfac, hdom.ker_eq_bot]))⟩
  have hiso : IsIso (equalizer.ι y y').left :=
    _root_.GlobalTheory.isIso_of_isClosedImmersion_of_schemeDominant _
  ext1
  rw [← cancel_epi (equalizer.ι y y').left, ← Over.comp_left, ← Over.comp_left,
    equalizer.condition]

end GlobalTheory
