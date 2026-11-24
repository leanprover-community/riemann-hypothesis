module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
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

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

section act
variable {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
  {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}

theorem IsEtLev.congr (h : IsEtLev o w0 r lv) {x y : D.La} (hxy : x - y ∈ wSub D w0 r) : lv x = lv y := by
  have : x = y + (x - y) := by abel
  rw [this, h.1, h.2.2.1 _ hxy, _root_.mul_one]

theorem IsEtLev.congr_mk (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : Submodule.Quotient.mk (p := wSub D w0 r) x = Submodule.Quotient.mk y) : lv x = lv y :=
  h.congr ((Submodule.Quotient.eq _).1 hxy)

def liftAct (g : LevGrp D w0 r) (x : D.La) : D.La :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose

theorem mk_liftAct (g : LevGrp D w0 r) (x : D.La) :
    Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = g (Submodule.Quotient.mk x) :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose_spec

end act

end GlobalTheory.UPel.HT.EtLev
