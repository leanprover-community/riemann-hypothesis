module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem tensor_isPullback {X0 : Scheme.{0}} (A B : Over X0) :
    IsPullback (fst A B).left (snd A B).left A.hom B.hom :=
  IsPullback.of_hasPullback A.hom B.hom

theorem secZ_isPullback {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    IsPullback (secZ G x m) (pullback.snd G.hom x) (fst (Tm x m) G).left
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := by
  have hR := (tensor_isPullback (Tm x m) G).flip
  have hO : IsPullback (secZ G x m ≫ (snd (Tm x m) G).left) (pullback.snd G.hom x) G.hom
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom) := by
    rw [secZ_snd]
    have e : spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom = x := by
      dsimp
      rw [← Category.assoc, spMap_comp_alg]
      simp [spMap]
    rw [e]
    exact IsPullback.of_hasPullback G.hom x
  exact IsPullback.of_right hO (secZ_fst G x m) hR

theorem secZ_surj (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    Function.Surjective (secZ G x m).base := by
  have hs : Surjective (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := ⟨fun q =>
    ⟨IsLocalRing.closedPoint k, jet_pt m q _⟩⟩
  have := MorphismProperty.of_isPullback (P := @Surjective) (secZ_isPullback G x m).flip hs
  exact this.surj

end GlobalTheory.CompanionTheory.Ar.Coc
