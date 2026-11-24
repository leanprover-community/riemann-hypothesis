module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

def tors {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℕ) : Subgroup (T ⟶ P.A) where
  carrier := {x | x ^ k = 1}
  one_mem' := one_pow k
  mul_mem' := by
    intro x y hx hy
    haveI := P.isAb.comm
    have hc : Commute x y := mul_comm x y
    have hx' : x ^ k = 1 := hx
    have hy' : y ^ k = 1 := hy
    show (x * y) ^ k = 1
    rw [hc.mul_pow, hx', hy', _root_.mul_one]
  inv_mem' := by
    intro x hx
    have hx' : x ^ k = 1 := hx
    show x⁻¹ ^ k = 1
    rw [inv_pow, hx', inv_one]

def unitSpec {K : Type} [CommRing K] (u : Kˣ) : Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom u

end GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws
