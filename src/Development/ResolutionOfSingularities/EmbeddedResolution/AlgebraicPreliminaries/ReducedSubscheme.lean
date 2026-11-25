module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

theorem isReduced_subscheme_ker {W X : AlgebraicGeometry.Scheme}
    (f : W ⟶ X) [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.Hom.ker f).subscheme := by
  have : ∀ y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
      _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) := by
    intro y
    obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧
        f.imageι.base y ∈ U :=
      ⟨(X.affineCover.f (X.affineCover.idx _)).opensRange,
        AlgebraicGeometry.isAffineOpen_opensRange _, X.affineCover.covers _⟩
    let V := (TopologicalSpace.Opens.map f.imageι.base).obj U
    have hVaff : AlgebraicGeometry.IsAffineOpen V := hU.preimage f.imageι
    have hred : _root_.IsReduced ↥(f.image.presheaf.obj (Opposite.op V)) :=
      isReduced_of_injective (f.toImage.app V).hom
        (by simpa using AlgebraicGeometry.Scheme.Hom.toImage_app_injective f ⟨U, hU⟩)
    let x : V := ⟨y, hyU⟩
    let : Algebra ↥(f.image.presheaf.obj (Opposite.op V)) ↥(f.image.presheaf.stalk x.1) :=
      TopCat.Presheaf.algebra_section_stalk _ x
    have : IsLocalization (hVaff.primeIdealOf x).asIdeal.primeCompl
        ↥(f.image.presheaf.stalk x.1) := hVaff.isLocalization_stalk x
    exact isReduced_localizationPreserves (hVaff.primeIdealOf x).asIdeal.primeCompl
      ↥(f.image.presheaf.stalk x.1) hred
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

end FunctorialResolution.EmbeddedResolution
