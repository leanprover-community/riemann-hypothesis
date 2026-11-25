module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev ptR (χ : D.X) : Spec (CommRingCat.of R) ⟶ D.P.A.left :=
  (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ D.c χ).left

def unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) :
    (FractionRing R)ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
    (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).toMonoidHom

def Reads (κ : D.X → (FractionRing R)ˣ) : Prop :=
  ∃ g : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptR D χ) (fun _ => -1)),
    (∀ χ, (g χ).IsGen) ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi χ) r z J = unitAt r z (κ χ) * val (g χ) (r ≫ jK R) z J

def lead {X : Type} [AddCommGroup X] (κ : X → (FractionRing R)ˣ) (k : ℕ) (α mu : X) : (FractionRing R)ˣ :=
  κ mu ^ k * (κ (mu + α) * (κ mu)⁻¹ * (κ α)⁻¹)

end GlobalTheory.ThFam
