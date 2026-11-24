module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

abbrev Ix (E : Type) [Field E] [NumberField E] (n : ℕ) : Type := Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E)

def dl {E : Type} [Field E] [NumberField E] {n : ℕ} (m : Ix E n) : Fin n → 𝓞 E :=
  Pi.single m.1 (RingOfIntegers.basis E m.2)

def mkN {E : Type} [Field E] [NumberField E] {n : ℕ} (p : ℕ) (x : Fin n → 𝓞 E) : TestPt.NAdd E n p :=
  fun i => Ideal.Quotient.mk _ (x i)

def toRC {O Ω C : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω] [Algebra O C] [Algebra Ω C]
    (R : Subalgebra O Ω) (RC : Subalgebra O C) (h : ∀ a ∈ R, algebraMap Ω C a ∈ RC) : R →+* RC :=
  ((algebraMap Ω C).comp (R.val : R →+* Ω)).codRestrict RC fun a => h a a.2

def IsDerAt0 {C R W N : Type} [Field C] [CommRing R] [Algebra R C] [AddCommGroup W] [Module R W] [AddCommGroup N]
    (M : Submodule R (N → C)) (Dv : M →ₗ[R] W) : Prop :=
  ∀ (f g h : M) (a b : R), (h : N → C) = (f : N → C) * (g : N → C) → algebraMap R C a = (f : N → C) 0 →
    algebraMap R C b = (g : N → C) 0 → Dv h = a • Dv g + b • Dv f

end PositivityTheory.Xgn.TestGroupPoint
