module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace ReciprocityTheory.ChartRestriction.G.Pdiv

structure SiegPairPB {S S' : Scheme.{0}} {h M₁ : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h M₁ ζ s) (f : S' ⟶ S) where
  A : Over S'
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  φ : A.left ⟶ o.A.left
  φ₂ : (G2 A).left ⟶ (G2 o.A).left
  pb : IsGrpPullback A o.A f φ
  sq : IsSquare φ φ₂
  P : LB (G2 A).left
  isLB : P.IsLB
  iso : LBIso P (o.P.pull φ₂)
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)

attribute [instance] SiegPairPB.grp SiegPairPB.comm

def StSiegPull : Prop :=
  ∀ {S S' : Scheme.{0}} {h M₁ : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h M₁ ζ s) (f : S' ⟶ S), Nonempty (SiegPairPB o f)

end ReciprocityTheory.ChartRestriction.G.Pdiv
