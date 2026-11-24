module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

def EndData (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ RosatiAdj D.P.A D.P.L a a' ∧ (∀ y, D.c (h y) = D.c y ≫ a) ∧ (∀ y, D.c (h' y) = D.c y ≫ a') ∧
    D.TauBal a a' h h'

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def FormalEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) : Prop :=
  (∀ e, IsMonHom (b e)) ∧ (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) ∧
    (∀ e, b e ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X,
      TorusEndOf D.toPre.X h' t ∧ (U.gt e).i ≫ b e = t ≫ (U.gt e).i

def LinEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : G ⟶ G) : Prop :=
  IsMonHom b ∧ FormalEnd U a h' fun e => (Over.pullback (thick R I e)).map b

def ExtLam (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB ((Over.pullback (jK R)).obj G).left)
    (PP : LB (G2 G).left) : Prop :=
  PP.IsLB ∧ ∀ κ₂ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
    Geo.Tor.IsSquare (G' := (Over.pullback (jK R)).obj G) (G := G) (pullback.fst G.hom (jK R)) κ₂ →
      LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (PP.pull κ₂)

end GlobalTheory.Mum
