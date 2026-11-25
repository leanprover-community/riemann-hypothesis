module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj

namespace GlobalTheory.UCanon

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev prj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    (h : IsPullDeg θ D D') : D'.P.A.left ⟶ D.P.A.left :=
  h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf θ)

def Extends {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (θ : R →+* R') {F : Type} [Field F]
    [Algebra (FractionRing R') F] (κ : FractionRing R →+* F) : Prop :=
  ∀ r : R, κ (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (θ r))

variable {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V]
  (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I]
  (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X)

def DivBy (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)) : Prop :=
  (∀ y, (((g y)⁻¹ : (FractionRing V)ˣ) : FractionRing V) =
      ∏ k, algebraMap V (FractionRing V) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y))) ∧
    (∀ y : Q.X, hD.xe y = e y) ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (oQ.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) ≫ (L.oa.onB.act x).left)

variable {Q} {g : Q.X → (FractionRing V)ˣ} (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g))

def IsLevPt (a : D'.La) (p : QkPt Q (FractionRing V) l.M') : Prop :=
  p.y = 0 ∧ p.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) : Q.P.A.left ⟶ L.D.P.A.left) =
    jK V ≫ spMap iw ≫ (L.o.etaA a).left ≫ L.φB

end GlobalTheory.UCanon
