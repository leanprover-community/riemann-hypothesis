module

public import Development.EtaleCohomology.EtaleSheaves.CoverCut
public import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.BuildCut

def ProdACF (W : Type) [CommRing W] : Prop :=
  AIC W ∧ ∀ a : W, ∃ e u : W, IsIdempotentElem e ∧ IsUnit u ∧ a = e * u

def Pts : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (W : Type) (_ : CommRing W) (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W ∧ Surjective w

def LimInt : Prop := ∀ {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
  (ι : ∀ j, D.obj j ⟶ Y), ClopenSys y D c ι → ∀ j, IsIntegralHom (c.π.app j ≫ ι j)

def Comp : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ w.normalization),
      ClopenSys y D c ι ∧ AICSch c.pt

theorem goal_of (hP : Pts) (hL : LimInt) (hC : Comp) : Build := by
  intro P _ _
  obtain ⟨W, _, w, hW, hs⟩ := hP (P := P)
  refine ⟨w.normalization, w.fromNormalization, inferInstance, ?_, fun y => ?_⟩
  · have h := hs
    rw [← w.toNormalization_fromNormalization] at h
    exact ⟨Function.Surjective.of_comp h.surj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hA⟩ := hC W w hW y
    refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, hA, fun j => ?_⟩
    have := hL y D c ι hc j
    infer_instance

end LateralTheory.E.BuildCut
