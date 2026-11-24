module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

structure GermAt [StarRing (𝓞 E)] (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) where

  B : Germ.FB S d (𝓞 E)

  x : ∀ m, jOG x0 d m 1 ⟶ t.G

  e : ∀ m, FrTyG t x0 d x m

  tg : Fin d → (Sp (DualNumber S) ⟶ t.G.left)
  chart : IsChartG t x0 d B.G.F B.A.act tg (fun l j => if l = j then 1 else 0) x
  tan : ∀ l, IsTanAtG t x0 (tg l)
  basis : ∀ w, IsTanAtG t x0 w → ∃! a : Fin d → S, IsCombAtG t x0 tg a w
  frame : IsFrameG t x0 d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e
  trunc : FrTrunc t x0 d x e
  axes : FrAxes t x0 d x e

def PowFns (t : SAB H X0) : Prop := ∀ n, Function.Bijective (Out.powObj t.G n).hom.appTop.hom

def GeomPF (t : SAB H X0) {k : Type} [Field k] (x : Sp k ⟶ X0) : Prop :=
  ∃ (T : TorusExtension ((Over.pullback x).obj t.G)) (M : LB T.B.left),
    letI := T.grpB
    M.IsLB ∧ Out.KTriv T.B M ∧ LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (M.pull T.q.left)

def FibPF (t : SAB H X0) (z : X0) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X0), x (IsLocalRing.closedPoint k) = z ∧ GeomPF t x

def toFirst (k : Type) [CommRing k] (m : ℕ) (hm : 1 ≤ m) : Jet k Unit m →ₐ[k] Jet k Unit 1 :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

def TanPF (t : SAB H X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (p : ℕ) : Prop :=
  ∀ (hp : 1 ≤ p) (y : overAt x (Jet k Unit p) ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → y ^ p = 1 →
    (∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ y)), c.IsGen) →
      homAt x (toFirst k p hp) ≫ y = 1

end GlobalTheory.CompanionTheory.Ar.Conj
