module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
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

namespace GlobalTheory.CompanionTheory.Ar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def charVal {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) : A :=
  (Spec.preimage (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X))).hom
    (AddMonoidAlgebra.single χ 1)

def KillsOver {G : Over S} [GrpObj G] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B : Type} [CommRing B]
    (b : Sp B ⟶ S) : Prop :=
  ∀ (A : Type) [CommRing A] (g : B →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
    (∀ y ∈ Y, charVal t y = 1) → t ≫ u = 1

def IsCocharLie {R : Type} [CommRing R] {x : Sp R ⟶ S} (M : LieModel (splitTorus S X) x (X →+ R)) : Prop :=
  ∀ (δ : X →+ R) (χ : X), charVal (M.pt δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ)

def LieModel.Lifts {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (c : R →+* R') {S' : Scheme.{0}} {G' : Over S'}
    (φ : G'.left ⟶ G.left) {x' : Sp R' ⟶ S'} (e : E) (v : epsAt x' ⟶ G') : Prop :=
  v.left ≫ φ = spMap (dualMap c) ≫ (M.pt e).left

end GlobalTheory.CompanionTheory.Ar
