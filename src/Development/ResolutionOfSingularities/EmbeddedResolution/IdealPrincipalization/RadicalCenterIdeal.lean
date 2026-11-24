module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
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
import Mathlib.Tactic.TypeStar

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem radical_ker_le_ker_of_isReduced {R S : Type*} [CommRing R] [CommRing S] [IsReduced S]
    (f : R →+* S) : (RingHom.ker f).radical ≤ RingHom.ker f := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker, map_pow] at hn
  rw [RingHom.mem_ker]
  exact IsNilpotent.eq_zero ⟨n, hn⟩

theorem smoothSubschemeIdealIsRadical : SmoothSubschemeIdealIsRadical.{u} := by
  intro k ik X p Z ism J hsub
  have hstalk : ∀ x : ↥Z.subscheme, _root_.IsReduced ↑(Z.subscheme.presheaf.stalk x) := by
    intro x
    have := isDomain_stalk_of_smooth (Z.subschemeι ≫ p) x
    infer_instance
  have hred : AlgebraicGeometry.IsReduced Z.subscheme :=
    isReduced_of_isReduced_stalk Z.subscheme
  have hcomp : ∀ U : Z.subscheme.Opens,
      _root_.IsReduced ↑(Z.subscheme.presheaf.obj (Opposite.op U)) :=
    fun U => AlgebraicGeometry.IsReduced.component_reduced U
  have hZrad : ∀ U : X.affineOpens, (Z.ideal U).radical ≤ Z.ideal U := by
    intro U
    rw [← Z.ker_subschemeι_app U]
    exact radical_ker_le_ker_of_isReduced _
  have hle : Z.support ≤ J.support := SetLike.coe_subset_coe.mp hsub
  have hJv : J ≤ Scheme.IdealSheafData.vanishingIdeal Z.support := by
    apply (Scheme.IdealSheafData.gc J Z.support).mp
    exact hle
  rw [Scheme.IdealSheafData.vanishingIdeal_support] at hJv
  have hrad : Z.radical ≤ Z := by
    rw [Scheme.IdealSheafData.le_def]
    intro U
    rw [Scheme.IdealSheafData.radical_ideal]
    exact hZrad U
  exact le_trans hJv hrad

end FunctorialResolution.EmbeddedResolution
