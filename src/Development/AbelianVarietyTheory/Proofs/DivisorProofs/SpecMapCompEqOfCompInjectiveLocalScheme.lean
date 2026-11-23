module

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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem spMap_comp_eq_of_injective {Y : Scheme.{0}} {W R' V : Type} [CommRing W] [IsLocalRing W]
    [CommRing R'] [CommRing V] (u : Sp W ⟶ Y) (g₁ g₂ : W →+* R') (η' : R' →+* V)
    (hη : Function.Injective η')
    (h : spMap (η'.comp g₁) ≫ u = spMap (η'.comp g₂) ≫ u) :
    spMap g₁ ≫ u = spMap g₂ ≫ u := by
  have hu := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of W) u
  have key : ∀ g : W →+* R', spMap g ≫ u =
      Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g) ≫
        Y.fromSpecStalk (u (closedPoint (CommRingCat.of W))) := by
    intro g
    conv_lhs => rw [← hu]
    simp only [spMap, Spec.map_comp, Category.assoc]
  have key' : ∀ g : W →+* R', spMap (η'.comp g) ≫ u =
      Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g ≫
        CommRingCat.ofHom η') ≫ Y.fromSpecStalk (u (closedPoint (CommRingCat.of W))) := by
    intro g
    conv_lhs => rw [← hu]
    simp only [spMap, Spec.map_comp, Category.assoc, CommRingCat.ofHom_comp]
  rw [key', key'] at h
  have h2 := (cancel_mono _).1 h
  have h3 := Spec.map_injective h2
  have h4 : Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g₁ =
      Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g₂ := by
    ext a
    apply hη
    have := congrArg (fun f => f.hom a) h3
    simpa using this
  rw [key, key, h4]

end GlobalTheory.TInj
