module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def SecIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y} (a : R)
    (σ τ : LB.Sec L) : Prop :=
  ∀ j, σ.f j = resTop _ (scal p a) * τ.f j

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def SecBGenerates (k : ℕ) (α : D.toPre.X) (s : D.toPre.SecB k α) : Prop :=
  ∀ s' : D.toPre.SecB k α, ∃! a : R, SecIsMul D.toPre.P.A.hom a s' s

def IsTheta (U : Unif I D A G) (ϑ : H0 U.LG.L 1) : Prop :=
  ∀ e : ℕ, ∃ f : ∀ α : D.toPre.X, D.toPre.SecB 1 α, U.ExpandsAt e 1 ϑ f ∧ SecBGenerates 1 0 (f 0)

def NonzeroOnSpecial (U : Unif I D A G) (σ : H0 U.LG.L 1) : Prop :=
  ∃ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom (σ.f j) ≠ 0

end ReciprocityTheory.ChartRestriction.G.DVR

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

end ReciprocityTheory.ChartRestriction.G.DVR
