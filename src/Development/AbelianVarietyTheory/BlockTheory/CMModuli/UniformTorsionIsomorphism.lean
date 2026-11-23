module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open scoped CategoryTheory.Obj

def ringActOf {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (a : Geo.Tor.OAct O G) : RingAct G O where
  act := a.act
  hom := a.hom
  map_one := a.one
  map_mul := fun x y => by rw [_root_.mul_comm x y]; exact a.mul y x
  map_add := fun x y => a.add x y

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {R : Type} [CommRing R] [IsDomain R]

structure OData (H : Host E) (I : Ideal R) where

  D : DegData R I

  [mod : Module (𝓞 E) D.toPre.X]

  ac : letI := hostStar H; D.OAct (𝓞 E)
  through : PsiThroughHost H ac

attribute [instance] OData.mod

variable {H : Host E} {I : Ideal R}

structure OUnif (t : SAB H (Spec (CommRingCat.of R))) (Δ : OData H I) where

  A : PolAV (Spec (CommRingCat.of (FractionRing R)))

  actA : letI := hostStar H; A.OAct (𝓞 E)

  U : Unif I Δ.D A t.G
  LG_eq : U.LG = t.PP
  cub_eq : HEq U.cubG t.cub
  lin : letI := hostStar H; U.toUnifPre.OLinear (𝓞 E) Δ.ac actA (ringActOf t.act)

section Points

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

namespace OUnif

variable {t : SAB H (Spec (CommRingCat.of R))} {Δ : OData H I} (u : OUnif t Δ)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

end OUnif

end GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
