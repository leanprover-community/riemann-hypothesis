module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory

theorem smoothOfRelativeDimension_genericFibre_of_affine :
    ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  intro o _ _ X s d h
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d)
    (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))) fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of o ⟶ R := Spec.preimage (x ≫ s)
  letI : Algebra o R := φ.hom.toAlgebra
  have hφ : x ≫ s = spMap (algebraMap o R) := (Spec.map_preimage (x ≫ s)).symm
  have H := h R x hx hφ
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct o (FractionRing o) R)
  have sq' : IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := o) (A := FractionRing o) (B := R)).toRingHom))
      (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) (x ≫ s)
      (spMap (algebraMap o (FractionRing o))) := by
    rw [hφ]
    exact sq.flip
  have e : (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))).f i ≫ pullback.snd s _ =
      sq'.isoPullback.inv ≫ spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)) := by
    rw [IsPullback.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e]
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension d) := hloc.1
  exact @MorphismProperty.RespectsIso.precomp _ _ (@SmoothOfRelativeDimension d) this _ _ _
    sq'.isoPullback.inv sq'.isoPullback.isIso_inv _ H

end GlobalTheory
