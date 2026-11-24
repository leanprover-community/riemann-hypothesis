module

public import Development.EtaleCohomology.EtaleSheaves.BridgeYfiPf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.GeoProof
open LateralTheory.E.E4 LateralTheory.E.Bridge_yfiPf

theorem affNbhd {B : Scheme.{0}} (U : B.Etale) (u : U.left) :
    ∃ (U' : B.Etale) (a : U' ⟶ U) (R : CommRingCat.{0}) (_ : U'.left ≅ Spec R) (u' : U'.left), a.left u' = u := by
  let f := U.left.affineCover.f (U.left.affineCover.idx u)
  have : IsOpenImmersion f := U.left.affineCover.map_prop _
  refine ⟨Scheme.Etale.mk (f ≫ U.hom), MorphismProperty.Over.homMk f rfl trivial, _, Iso.refl _, ?_⟩
  exact U.left.affineCover.covers u

def AffGeo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (R : CommRingCat.{0}) (_ : U.left ≅ Spec R) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Shrink : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U U' : B.Etale)
  (a : U' ⟶ U) (m : ℤ) (u' : U'.left), Sys q i p ι U' m u' → Nonempty (Sys q i p ι U m (a.left u'))

theorem Geo_of (hA : AffGeo) (hS : Shrink) : Geo := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m u
  obtain ⟨U', a, R, e, u', rfl⟩ := affNbhd U u
  obtain ⟨S⟩ := hA hH q k hq i toK ι p hp U' R e m u'
  exact hS q i p ι U U' a m u' S

end LateralTheory.E.GeoProof
